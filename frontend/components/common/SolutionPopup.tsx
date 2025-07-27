// frontend/components/common/SolutionPopup.tsx

import React from 'react';

interface SolutionPopupProps {
  isVisible: boolean;
  onClose: () => void;
  onViewSolution: () => void;
  onStartTutoring: () => void;
  solution: {
    solved: boolean;
    final_proof: string;
    attempts_used: number;
    attempts: any[];
  } | null;
}

export const SolutionPopup: React.FC<SolutionPopupProps> = ({
  isVisible,
  onClose,
  onViewSolution,
  onStartTutoring,
  solution
}) => {
  if (!isVisible || !solution) return null;

  return (
    <div className="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50">
      <div className="bg-slate-900 border border-slate-700 rounded-lg p-6 max-w-md w-full mx-4">
        {/* Header */}
        <div className="text-center mb-6">
          <div className="flex items-center justify-center mb-4">
            <div className="w-12 h-12 bg-green-500 rounded-full flex items-center justify-center">
              <svg
                className="w-6 h-6 text-white"
                fill="none"
                stroke="currentColor"
                viewBox="0 0 24 24"
              >
                <path
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  strokeWidth={2}
                  d="M5 13l4 4L19 7"
                />
              </svg>
            </div>
          </div>
          <h2 className="text-2xl font-bold text-white mb-2">
            Solution Found!
          </h2>
          <p className="text-slate-400">
            AI has discovered a solution and is ready to guide you
          </p>
        </div>

        {/* Solution Summary */}
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-4 mb-6">
          <div className="flex items-center justify-between mb-2">
            <span className="text-sm font-medium text-slate-300">Attempts Used:</span>
            <span className="text-sm text-white">{solution.attempts_used}</span>
          </div>
          <div className="flex items-center justify-between mb-2">
            <span className="text-sm font-medium text-slate-300">Success Rate:</span>
            <span className="text-sm text-green-400">
              {solution.attempts.length > 0 
                ? Math.round((solution.attempts.filter(a => a.success).length / solution.attempts.length) * 100)
                : 0}%
            </span>
          </div>
          <div className="mt-3">
            <span className="text-sm font-medium text-slate-300">Final Proof:</span>
            <pre className="mt-1 p-2 bg-slate-900 text-green-400 rounded text-xs overflow-x-auto max-h-20">
              {solution.final_proof.length > 150 
                ? solution.final_proof.substring(0, 150) + '...' 
                : solution.final_proof}
            </pre>
          </div>
        </div>

        {/* Action Buttons */}
        <div className="space-y-3">
          <button
            onClick={onViewSolution}
            className="w-full px-4 py-3 bg-blue-600 hover:bg-blue-500 text-white rounded-lg font-medium transition-colors"
          >
            View Solution
          </button>
          <button
            onClick={onStartTutoring}
            className="w-full px-4 py-3 bg-green-600 hover:bg-green-500 text-white rounded-lg font-medium transition-colors"
          >
            Start Tutoring
          </button>
          <button
            onClick={onClose}
            className="w-full px-4 py-2 bg-slate-700 hover:bg-slate-600 text-white rounded-lg transition-colors"
          >
            Close
          </button>
        </div>

        {/* Quick Stats */}
        <div className="mt-4 pt-4 border-t border-slate-700">
          <div className="grid grid-cols-2 gap-4 text-xs">
            <div className="text-center">
              <div className="text-white font-medium">{solution.attempts.length}</div>
              <div className="text-slate-400">Total Attempts</div>
            </div>
            <div className="text-center">
              <div className="text-green-400 font-medium">
                {solution.attempts.filter(a => a.success).length}
              </div>
              <div className="text-slate-400">Successful</div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}; 