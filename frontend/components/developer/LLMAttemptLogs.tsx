// frontend/components/developer/LLMAttemptLogs.tsx

import React, { useState, useMemo } from 'react';

// interface LLMAttempt {
//   attempt: number;
//   tactic: string;
//   leanError?: string;
//   success: boolean;
//   timestamp: string;
//   proofState: string;
//   error_info?: any;
// }

interface DeveloperLogs {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  config: any;
  recent_logs: any[];
  attempt_logs: any[];
}

interface LLMAttemptLogsProps {
  logs: DeveloperLogs | null;
  isLoading: boolean;
  onRefresh: () => void;
  onClearLogs?: () => void;
  autoSolveResult: any;
}

export const LLMAttemptLogs: React.FC<LLMAttemptLogsProps> = React.memo(({
  logs,
  isLoading,
  onRefresh,
  onClearLogs,
  autoSolveResult
}) => {
  const [expandedAttempts, setExpandedAttempts] = useState<Set<number>>(new Set());
  const [filterSuccess, setFilterSuccess] = useState<'all' | 'success' | 'failed'>('all');

  const toggleExpanded = (attemptNumber: number) => {
    const newExpanded = new Set(expandedAttempts);
    if (newExpanded.has(attemptNumber)) {
      newExpanded.delete(attemptNumber);
    } else {
      newExpanded.add(attemptNumber);
    }
    setExpandedAttempts(newExpanded);
  };

  const formatTimestamp = (timestamp: string) => {
    try {
      return new Date(timestamp).toLocaleTimeString();
    } catch {
      return timestamp;
    }
  };

  const getAttempts = useMemo(() => {
    if (autoSolveResult?.attempts) {
      return autoSolveResult.attempts;
    }
    if (logs?.attempt_logs) {
      return logs.attempt_logs.map(log => {
        const attempt = log.data || log;
        // Add timestamp from outer log object if not present in data
        if (!attempt.timestamp && log.timestamp) {
          attempt.timestamp = log.timestamp;
        }
        return attempt;
      });
    }
    return [];
  }, [autoSolveResult?.attempts, logs?.attempt_logs]);

  const filteredAttempts = useMemo(() => {
    return getAttempts.filter((attempt: any) => {
      if (filterSuccess === 'success') return attempt.success;
      if (filterSuccess === 'failed') return !attempt.success;
      return true;
    });
  }, [getAttempts, filterSuccess]);

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-full">
        <div className="text-slate-400">Loading logs...</div>
      </div>
    );
  }

  return (
    <div className="h-full flex flex-col p-4">
      {/* Header */}
      <div className="flex items-center justify-between mb-4">
        <div className="flex items-center space-x-4">
          <h3 className="text-lg font-semibold text-white">LLM Attempt Logs</h3>
          <div className="flex items-center space-x-2">
            <span className="text-sm text-slate-400">Filter:</span>
            <select
              value={filterSuccess}
              onChange={(e) => setFilterSuccess(e.target.value as any)}
              className="bg-slate-800 border border-slate-600 text-white rounded px-2 py-1 text-sm"
            >
              <option value="all">All Attempts</option>
              <option value="success">Successful</option>
              <option value="failed">Failed</option>
            </select>
          </div>
        </div>
        <div className="flex items-center space-x-2">
          <button
            onClick={onRefresh}
            className="px-3 py-1 bg-slate-700 hover:bg-slate-600 text-white rounded text-sm transition-colors"
          >
            Refresh
          </button>
          {onClearLogs && (
            <button
              onClick={onClearLogs}
              className="px-3 py-1 bg-red-700 hover:bg-red-600 text-white rounded text-sm transition-colors"
            >
              Clear Logs
            </button>
          )}
        </div>
      </div>

      {/* Auto-Solve Result Summary */}
      {autoSolveResult && (
        <div className="mb-4 p-3 bg-slate-800 border border-slate-700 rounded-lg">
          <div className="flex items-center justify-between">
            <div className="flex items-center space-x-2">
              <span className={`w-3 h-3 rounded-full ${autoSolveResult.solved ? 'bg-green-500' : 'bg-red-500'}`}></span>
              <span className="text-white font-medium">
                Auto-Solve {autoSolveResult.solved ? 'Succeeded' : 'Failed'}
              </span>
            </div>
            <span className="text-slate-400 text-sm">
              {autoSolveResult.attempts_used} attempts used
            </span>
          </div>
          {autoSolveResult.solved && (
            <div className="mt-2 text-sm text-green-400">
              Final proof state: {autoSolveResult.final_proof.length > 100 
                ? autoSolveResult.final_proof.substring(0, 100) + '...' 
                : autoSolveResult.final_proof}
            </div>
          )}
        </div>
      )}

      {/* Attempts List */}
      <div className="flex-1 overflow-y-auto">
        {filteredAttempts.length === 0 ? (
          <div className="text-center text-slate-400 py-8">
            No attempts found
          </div>
        ) : (
          <div className="space-y-2">
            {filteredAttempts.map((attempt: any, index: number) => (
              <div
                key={`${attempt.attempt}-${index}`}
                className="bg-slate-800 border border-slate-700 rounded-lg overflow-hidden"
              >
                {/* Attempt Header */}
                <div
                  className="flex items-center justify-between p-3 cursor-pointer hover:bg-slate-750"
                  onClick={() => toggleExpanded(attempt.attempt)}
                >
                  <div className="flex items-center space-x-3">
                    <span className={`w-3 h-3 rounded-full ${attempt.success ? 'bg-green-500' : 'bg-red-500'}`}></span>
                    <span className="text-white font-medium">Attempt {attempt.attempt}</span>
                    <span className="text-slate-400 text-sm">{formatTimestamp(attempt.timestamp)}</span>
                  </div>
                  <div className="flex items-center space-x-2">
                    <span className={`px-2 py-1 rounded text-xs font-medium ${
                      attempt.success 
                        ? 'bg-green-900 text-green-300' 
                        : 'bg-red-900 text-red-300'
                    }`}>
                      {attempt.success ? 'Success' : 'Failed'}
                    </span>
                    <svg
                      className={`w-4 h-4 text-slate-400 transition-transform ${
                        expandedAttempts.has(attempt.attempt) ? 'rotate-180' : ''
                      }`}
                      fill="none"
                      stroke="currentColor"
                      viewBox="0 0 24 24"
                    >
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                    </svg>
                  </div>
                </div>

                {/* Expanded Details */}
                {expandedAttempts.has(attempt.attempt) && (
                  <div className="border-t border-slate-700 p-3 bg-slate-850">
                    <div className="space-y-3">
                      {/* Tactic Used */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Tactic:</span>
                        <code className="ml-2 px-2 py-1 bg-slate-900 text-blue-400 rounded text-sm">
                          {attempt.tactic}
                        </code>
                      </div>

                      {/* Error Information */}
                      {!attempt.success && attempt.error_info && (
                        <div>
                          <span className="text-sm font-medium text-slate-300">Error:</span>
                          <div className="mt-1 p-2 bg-red-900/20 border border-red-700 rounded text-sm">
                            <div className="text-red-400 font-medium">{attempt.error_info.type}</div>
                            <div className="text-red-300 mt-1">{attempt.error_info.message}</div>
                            {attempt.error_info.suggestion && (
                              <div className="text-yellow-300 mt-1">
                                <span className="font-medium">Suggestion:</span> {attempt.error_info.suggestion}
                              </div>
                            )}
                          </div>
                        </div>
                      )}

                      {/* Proof State */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Proof State:</span>
                        <pre className="mt-1 p-2 bg-slate-900 text-green-400 rounded text-xs overflow-x-auto">
                          {attempt.proofState}
                        </pre>
                      </div>

                      {/* New State (if different) */}
                      {attempt.new_state && attempt.new_state !== attempt.proofState && (
                        <div>
                          <span className="text-sm font-medium text-slate-300">New State:</span>
                          <pre className="mt-1 p-2 bg-slate-900 text-blue-400 rounded text-xs overflow-x-auto">
                            {attempt.new_state}
                          </pre>
                        </div>
                      )}
                    </div>
                  </div>
                )}
              </div>
            ))}
          </div>
        )}
      </div>

      {/* Summary */}
      <div className="mt-4 p-3 bg-slate-800 border border-slate-700 rounded-lg">
        <div className="flex items-center justify-between text-sm">
          <span className="text-slate-400">
            Total attempts: {filteredAttempts.length}
          </span>
          <span className="text-slate-400">
            Successful: {filteredAttempts.filter((a: any) => a.success).length}
          </span>
          <span className="text-slate-400">
            Failed: {filteredAttempts.filter((a: any) => !a.success).length}
          </span>
        </div>
      </div>
    </div>
  );
}); 