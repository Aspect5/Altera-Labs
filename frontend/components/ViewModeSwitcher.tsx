// frontend/components/ViewModeSwitcher.tsx

import React from 'react';

// --- MODIFIED: Added 'exam_results' to the ViewMode type ---
type ViewMode = 'graph' | 'developer' | 'exam_results';

interface ViewModeSwitcherProps {
  viewMode: ViewMode;
  setViewMode: (mode: 'graph' | 'developer') => void; // Stay as is, we don't switch TO exam results here
}

const ViewModeSwitcher: React.FC<ViewModeSwitcherProps> = ({ viewMode, setViewMode }) => {
  const commonButtonClasses = "px-4 py-2 text-sm font-medium transition-colors";
  const activeButtonClasses = "bg-blue-600 text-white";
  const inactiveButtonClasses = "bg-slate-700 text-slate-300 hover:bg-slate-600";

  return (
    <div className="flex rounded-md shadow-sm" role="group">
      <button
        type="button"
        onClick={() => setViewMode('graph')}
        className={`${commonButtonClasses} rounded-l-lg ${viewMode === 'graph' ? activeButtonClasses : inactiveButtonClasses}`}
      >
        Mentor
      </button>
      <button
        type="button"
        onClick={() => setViewMode('developer')}
        className={`${commonButtonClasses} rounded-r-lg ${viewMode === 'developer' ? activeButtonClasses : inactiveButtonClasses}`}
      >
        Developer
      </button>
    </div>
  );
};

export default ViewModeSwitcher;