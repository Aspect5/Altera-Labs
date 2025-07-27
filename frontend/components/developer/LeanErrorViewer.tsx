// frontend/components/developer/LeanErrorViewer.tsx

import React, { useState } from 'react';

interface DeveloperLogs {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  config: any;
  recent_logs: any[];
  attempt_logs: any[];
}

interface LeanErrorViewerProps {
  logs: DeveloperLogs | null;
  isLoading: boolean;
  onRefresh: () => void;
}

export const LeanErrorViewer: React.FC<LeanErrorViewerProps> = ({
  logs,
  isLoading,
  onRefresh
}) => {
  const [selectedErrorType, setSelectedErrorType] = useState<string>('all');
  const [expandedErrors, setExpandedErrors] = useState<Set<string>>(new Set());

  const toggleExpanded = (errorId: string) => {
    const newExpanded = new Set(expandedErrors);
    if (newExpanded.has(errorId)) {
      newExpanded.delete(errorId);
    } else {
      newExpanded.add(errorId);
    }
    setExpandedErrors(newExpanded);
  };

  const getErrorLogs = () => {
    if (!logs?.attempt_logs) return [];
    
    const errors = [];
    for (const log of logs.attempt_logs) {
      if (log.data && !log.data.success && log.data.error_info) {
        errors.push({
          id: `${log.timestamp}-${log.data.attempt}`,
          timestamp: log.timestamp,
          attempt: log.data.attempt,
          error: log.data.error_info,
          tactic: log.data.tactic,
          proofState: log.data.proofState
        });
      }
    }
    return errors;
  };

  const filteredErrors = getErrorLogs().filter(error => {
    if (selectedErrorType === 'all') return true;
    return error.error.type === selectedErrorType;
  });

  const getErrorTypeColor = (type: string) => {
    switch (type) {
      case 'unknown_identifier': return 'bg-red-900 text-red-300';
      case 'type_mismatch': return 'bg-orange-900 text-orange-300';
      case 'tactic_failed': return 'bg-yellow-900 text-yellow-300';
      case 'unsolved_goals': return 'bg-blue-900 text-blue-300';
      case 'invalid_tactic': return 'bg-purple-900 text-purple-300';
      case 'timeout': return 'bg-gray-900 text-gray-300';
      case 'system_error': return 'bg-red-900 text-red-300';
      default: return 'bg-slate-900 text-slate-300';
    }
  };

  const getErrorTypeDescription = (type: string) => {
    switch (type) {
      case 'unknown_identifier': return 'Unknown identifier or theorem name';
      case 'type_mismatch': return 'Type mismatch between expressions';
      case 'tactic_failed': return 'Tactic could not be applied';
      case 'unsolved_goals': return 'Proof still has unsolved goals';
      case 'invalid_tactic': return 'Invalid tactic syntax';
      case 'timeout': return 'Lean verification timed out';
      case 'system_error': return 'System or Lean installation error';
      default: return 'Unknown error type';
    }
  };

  const formatTimestamp = (timestamp: string) => {
    try {
      return new Date(timestamp).toLocaleString();
    } catch {
      return timestamp;
    }
  };

  const getUniqueErrorTypes = () => {
    const types = new Set<string>();
    getErrorLogs().forEach(error => {
      types.add(error.error.type);
    });
    return Array.from(types).sort();
  };

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-full">
        <div className="text-slate-400">Loading error logs...</div>
      </div>
    );
  }

  return (
    <div className="h-full flex flex-col p-4">
      {/* Header */}
      <div className="flex items-center justify-between mb-4">
        <div className="flex items-center space-x-4">
          <h3 className="text-lg font-semibold text-white">Lean Error Viewer</h3>
          <div className="flex items-center space-x-2">
            <span className="text-sm text-slate-400">Error Type:</span>
            <select
              value={selectedErrorType}
              onChange={(e) => setSelectedErrorType(e.target.value)}
              className="bg-slate-800 border border-slate-600 text-white rounded px-2 py-1 text-sm"
            >
              <option value="all">All Errors</option>
              {getUniqueErrorTypes().map(type => (
                <option key={type} value={type}>{type}</option>
              ))}
            </select>
          </div>
        </div>
        <button
          onClick={onRefresh}
          className="px-3 py-1 bg-slate-700 hover:bg-slate-600 text-white rounded text-sm transition-colors"
        >
          Refresh
        </button>
      </div>

      {/* Error Statistics */}
      <div className="mb-4 grid grid-cols-2 md:grid-cols-4 gap-4">
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-3">
          <div className="text-2xl font-bold text-white">{getErrorLogs().length}</div>
          <div className="text-sm text-slate-400">Total Errors</div>
        </div>
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-3">
          <div className="text-2xl font-bold text-white">{getUniqueErrorTypes().length}</div>
          <div className="text-sm text-slate-400">Error Types</div>
        </div>
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-3">
          <div className="text-2xl font-bold text-white">{filteredErrors.length}</div>
          <div className="text-sm text-slate-400">Filtered</div>
        </div>
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-3">
          <div className="text-2xl font-bold text-white">
            {getErrorLogs().length > 0 
              ? Math.round((getErrorLogs().filter(e => e.error.suggestion).length / getErrorLogs().length) * 100)
              : 0}%
          </div>
          <div className="text-sm text-slate-400">With Suggestions</div>
        </div>
      </div>

      {/* Error List */}
      <div className="flex-1 overflow-y-auto">
        {filteredErrors.length === 0 ? (
          <div className="text-center text-slate-400 py-8">
            {selectedErrorType === 'all' ? 'No errors found' : `No ${selectedErrorType} errors found`}
          </div>
        ) : (
          <div className="space-y-3">
            {filteredErrors.map((error) => (
              <div
                key={error.id}
                className="bg-slate-800 border border-slate-700 rounded-lg overflow-hidden"
              >
                {/* Error Header */}
                <div
                  className="flex items-center justify-between p-3 cursor-pointer hover:bg-slate-750"
                  onClick={() => toggleExpanded(error.id)}
                >
                  <div className="flex items-center space-x-3">
                    <span className="w-3 h-3 rounded-full bg-red-500"></span>
                    <span className="text-white font-medium">Attempt {error.attempt}</span>
                    <span className="text-slate-400 text-sm">{formatTimestamp(error.timestamp)}</span>
                  </div>
                  <div className="flex items-center space-x-2">
                    <span className={`px-2 py-1 rounded text-xs font-medium ${getErrorTypeColor(error.error.type)}`}>
                      {error.error.type}
                    </span>
                    <svg
                      className={`w-4 h-4 text-slate-400 transition-transform ${
                        expandedErrors.has(error.id) ? 'rotate-180' : ''
                      }`}
                      fill="none"
                      stroke="currentColor"
                      viewBox="0 0 24 24"
                    >
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                    </svg>
                  </div>
                </div>

                {/* Expanded Error Details */}
                {expandedErrors.has(error.id) && (
                  <div className="border-t border-slate-700 p-3 bg-slate-850">
                    <div className="space-y-3">
                      {/* Error Type Description */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Error Type:</span>
                        <div className="mt-1 text-sm text-slate-400">
                          {getErrorTypeDescription(error.error.type)}
                        </div>
                      </div>

                      {/* Error Message */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Error Message:</span>
                        <div className="mt-1 p-2 bg-red-900/20 border border-red-700 rounded text-sm text-red-300">
                          {error.error.message}
                        </div>
                      </div>

                      {/* Suggestion */}
                      {error.error.suggestion && (
                        <div>
                          <span className="text-sm font-medium text-slate-300">Suggestion:</span>
                          <div className="mt-1 p-2 bg-yellow-900/20 border border-yellow-700 rounded text-sm text-yellow-300">
                            {error.error.suggestion}
                          </div>
                        </div>
                      )}

                      {/* Line and Column Numbers */}
                      {(error.error.line_number || error.error.column_number) && (
                        <div>
                          <span className="text-sm font-medium text-slate-300">Location:</span>
                          <div className="mt-1 text-sm text-slate-400">
                            {error.error.line_number && `Line ${error.error.line_number}`}
                            {error.error.line_number && error.error.column_number && ', '}
                            {error.error.column_number && `Column ${error.error.column_number}`}
                          </div>
                        </div>
                      )}

                      {/* Tactic That Caused Error */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Failed Tactic:</span>
                        <code className="ml-2 px-2 py-1 bg-slate-900 text-red-400 rounded text-sm">
                          {error.tactic}
                        </code>
                      </div>

                      {/* Proof State */}
                      <div>
                        <span className="text-sm font-medium text-slate-300">Proof State:</span>
                        <pre className="mt-1 p-2 bg-slate-900 text-green-400 rounded text-xs overflow-x-auto">
                          {error.proofState}
                        </pre>
                      </div>
                    </div>
                  </div>
                )}
              </div>
            ))}
          </div>
        )}
      </div>

      {/* Error Type Breakdown */}
      <div className="mt-4 p-3 bg-slate-800 border border-slate-700 rounded-lg">
        <h4 className="text-sm font-medium text-slate-300 mb-2">Error Type Breakdown:</h4>
        <div className="grid grid-cols-2 md:grid-cols-4 gap-2 text-xs">
          {getUniqueErrorTypes().map(type => {
            const count = getErrorLogs().filter(e => e.error.type === type).length;
            return (
              <div key={type} className="flex items-center justify-between">
                <span className={`px-2 py-1 rounded ${getErrorTypeColor(type)}`}>
                  {type}
                </span>
                <span className="text-slate-400">{count}</span>
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
}; 