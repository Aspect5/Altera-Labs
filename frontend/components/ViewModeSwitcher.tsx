
import React from 'react';

type ViewMode = 'graph' | 'developer';

interface ViewModeSwitcherProps {
    viewMode: ViewMode;
    setViewMode: (mode: ViewMode) => void;
}

const ViewModeSwitcher: React.FC<ViewModeSwitcherProps> = ({ viewMode, setViewMode }) => {
    const baseClasses = "px-4 py-2 text-sm font-semibold rounded-md transition-colors focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-offset-slate-900 focus:ring-cyan-500";
    const activeClasses = "bg-cyan-600 text-white";
    const inactiveClasses = "bg-slate-700 text-slate-300 hover:bg-slate-600";

    return (
        <div className="bg-slate-800 p-2 rounded-lg flex items-center justify-center space-x-2">
            <button 
                onClick={() => setViewMode('graph')}
                className={`${baseClasses} ${viewMode === 'graph' ? activeClasses : inactiveClasses}`}
                aria-pressed={viewMode === 'graph'}
            >
                Graph View
            </button>
            <button 
                onClick={() => setViewMode('developer')}
                className={`${baseClasses} ${viewMode === 'developer' ? activeClasses : inactiveClasses}`}
                aria-pressed={viewMode === 'developer'}
            >
                Developer View
            </button>
        </div>
    );
};

export default ViewModeSwitcher;
