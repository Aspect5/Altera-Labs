// frontend/components/developer/DeveloperPanel.tsx

import React, { useState, useEffect, useRef } from 'react';
import { LLMAttemptLogs } from './LLMAttemptLogs.tsx';
import { LeanErrorViewer } from './LeanErrorViewer.tsx';
import { ConfigPanel } from './ConfigPanel.tsx';
import LLMPerformanceTester from './LLMPerformanceTester.tsx';

interface DeveloperConfig {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  log_level: string;
  enable_detailed_logging: boolean;
  save_attempt_logs: boolean;
  auto_save_interval: number;
  max_log_entries: number;
  lean_timeout: number;
  enable_error_parsing: boolean;
  enable_llm_feedback: boolean;
}

interface DeveloperLogs {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  config: DeveloperConfig;
  recent_logs: any[];
  attempt_logs: any[];
}

interface DeveloperPanelProps {
  isVisible: boolean;
  onClose: () => void;
  currentProofState: string;
  onAutoSolve: (proofState: string, maxAttempts?: number) => Promise<any>;
  onToggleDeveloperMode: (enabled: boolean, maxAttempts?: number) => Promise<void>;
  onGetLogs: () => Promise<DeveloperLogs>;
}

export const DeveloperPanel: React.FC<DeveloperPanelProps> = React.memo(({
  isVisible,
  onClose,
  currentProofState,
  onAutoSolve,
  onToggleDeveloperMode,
  onGetLogs
}) => {
  const [activeTab, setActiveTab] = useState<'logs' | 'errors' | 'config' | 'performance'>('logs');
  const [logs, setLogs] = useState<DeveloperLogs | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [autoSolveResult, setAutoSolveResult] = useState<any>(null);
  const [isAutoSolving, setIsAutoSolving] = useState(false);
  const pollingRef = useRef<NodeJS.Timeout | null>(null);
  const loadingTimeoutRef = useRef<NodeJS.Timeout | null>(null);

  useEffect(() => {
    if (isVisible) {
      loadLogs();
    }
  }, [isVisible]);

  // Real-time polling for logs during auto-solve
  useEffect(() => {
    if (isVisible && isAutoSolving) {
      pollingRef.current = setInterval(() => {
        loadLogs();
      }, 2000); // Increased from 1000ms to 2000ms to reduce API calls
    } else if (pollingRef.current) {
      clearInterval(pollingRef.current);
      pollingRef.current = null;
    }
    return () => {
      if (pollingRef.current) {
        clearInterval(pollingRef.current);
        pollingRef.current = null;
      }
      if (loadingTimeoutRef.current) {
        clearTimeout(loadingTimeoutRef.current);
        loadingTimeoutRef.current = null;
      }
    };
  }, [isVisible, isAutoSolving]);

  const loadLogs = async () => {
    // Debounce rapid successive calls
    if (loadingTimeoutRef.current) {
      clearTimeout(loadingTimeoutRef.current);
    }
    
    loadingTimeoutRef.current = setTimeout(async () => {
      try {
        setIsLoading(true);
        const logsData = await onGetLogs();
        setLogs(logsData);
      } catch (error) {
        console.error('Failed to load developer logs:', error);
      } finally {
        setIsLoading(false);
      }
    }, 100); // 100ms debounce
  };

  const handleAutoSolve = async () => {
    try {
      setIsAutoSolving(true);
      const result = await onAutoSolve(currentProofState);
      setAutoSolveResult(result);
      await loadLogs(); // Refresh logs after auto-solve
    } catch (error) {
      console.error('Auto-solve failed:', error);
    } finally {
      setIsAutoSolving(false);
    }
  };

  const handleToggleDeveloperMode = async (enabled: boolean, maxAttempts?: number) => {
    try {
      await onToggleDeveloperMode(enabled, maxAttempts);
      await loadLogs(); // Refresh logs after config change
    } catch (error) {
      console.error('Failed to toggle developer mode:', error);
    }
  };

  const handleClearLogs = async () => {
    // Add confirmation dialog for safety
    if (!window.confirm('Are you sure you want to clear all developer logs? This action cannot be undone.')) {
      return;
    }
    
    try {
      const response = await fetch('/api/developer_logs/clear', {
        method: 'POST',
        credentials: 'include',
      });
      if (response.ok) {
        await loadLogs(); // Refresh logs after clearing
      } else {
        console.error('Failed to clear logs');
      }
    } catch (error) {
      console.error('Failed to clear logs:', error);
    }
  };

  if (!isVisible) return null;

  return (
    <div className="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50">
      <div className="bg-slate-900 border border-slate-700 rounded-lg w-full max-w-4xl h-[90vh] flex flex-col shadow-2xl overflow-hidden">
        {/* Header */}
        <div className="flex items-center justify-between p-4 border-b border-slate-700">
          <h2 className="text-xl font-bold text-white">Developer Panel</h2>
          <div className="flex items-center space-x-4">
            <button
              onClick={handleAutoSolve}
              disabled={isAutoSolving}
              className="px-4 py-2 bg-blue-600 hover:bg-blue-500 disabled:bg-blue-800 text-white rounded-lg transition-colors"
            >
              {isAutoSolving ? 'Auto-Solving...' : 'Auto-Solve'}
            </button>
            <button
              onClick={onClose}
              className="px-4 py-2 bg-slate-600 hover:bg-slate-500 text-white rounded-lg transition-colors"
            >
              Close
            </button>
          </div>
        </div>

        {/* Tab Navigation */}
        <div className="flex border-b border-slate-700">
          <button
            onClick={() => setActiveTab('logs')}
            className={`px-6 py-3 font-medium transition-colors ${
              activeTab === 'logs'
                ? 'text-blue-400 border-b-2 border-blue-400 bg-slate-800'
                : 'text-slate-400 hover:text-white hover:bg-slate-800'
            }`}
          >
            LLM Attempt Logs
          </button>
          <button
            onClick={() => setActiveTab('errors')}
            className={`px-6 py-3 font-medium transition-colors ${
              activeTab === 'errors'
                ? 'text-blue-400 border-b-2 border-blue-400 bg-slate-800'
                : 'text-slate-400 hover:text-white hover:bg-slate-800'
            }`}
          >
            Lean Error Viewer
          </button>
          <button
            onClick={() => setActiveTab('config')}
            className={`px-6 py-3 font-medium transition-colors ${
              activeTab === 'config'
                ? 'text-blue-400 border-b-2 border-blue-400 bg-slate-800'
                : 'text-slate-400 hover:text-white hover:bg-slate-800'
            }`}
          >
            Configuration
          </button>
          <button
            onClick={() => setActiveTab('performance')}
            className={`px-6 py-3 font-medium transition-colors ${
              activeTab === 'performance'
                ? 'text-blue-400 border-b-2 border-blue-400 bg-slate-800'
                : 'text-slate-400 hover:text-white hover:bg-slate-800'
            }`}
          >
            Performance Testing
          </button>
        </div>

        {/* Content Area */}
        <div className="flex-1 overflow-y-auto min-h-0 p-2 sm:p-4">
          {activeTab === 'logs' && (
            <LLMAttemptLogs
              logs={logs}
              isLoading={isLoading}
              onRefresh={loadLogs}
              onClearLogs={handleClearLogs}
              autoSolveResult={autoSolveResult}
            />
          )}
          {activeTab === 'errors' && (
            <LeanErrorViewer
              logs={logs}
              isLoading={isLoading}
              onRefresh={loadLogs}
            />
          )}
          {activeTab === 'config' && (
            <ConfigPanel
              config={logs?.config || null}
              isLoading={isLoading}
              onToggleDeveloperMode={handleToggleDeveloperMode}
              onRefresh={loadLogs}
            />
          )}
          {activeTab === 'performance' && (
            <div className="h-full overflow-auto p-4">
              <LLMPerformanceTester />
            </div>
          )}
        </div>
      </div>
    </div>
  );
}); 