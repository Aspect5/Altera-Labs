import React from 'react';
import { QuickStats } from '../../types/components';

interface QuickStatsPanelProps {
  stats: QuickStats;
}

const QuickStatsPanel: React.FC<QuickStatsPanelProps> = ({ stats }) => {
  const formatFlowTime = (minutes: number) => {
    if (minutes < 60) return `${minutes}m`;
    const hours = Math.floor(minutes / 60);
    const remainingMinutes = minutes % 60;
    return `${hours}h ${remainingMinutes}m`;
  };

  const getStreakColor = (streak: number) => {
    if (streak >= 7) return 'text-green-400';
    if (streak >= 3) return 'text-yellow-400';
    return 'text-slate-400';
  };

  const getHealthColor = (score: number) => {
    if (score >= 80) return 'text-green-400';
    if (score >= 60) return 'text-yellow-400';
    if (score >= 40) return 'text-orange-400';
    return 'text-red-400';
  };

  return (
    <div className="bg-slate-800 rounded-lg p-6 border border-slate-700">
      <h2 className="text-xl font-semibold text-cyan-400 mb-4">Quick Stats</h2>
      
      <div className="grid grid-cols-2 gap-4">
        {/* Total Concepts Mastered */}
        <div className="bg-slate-700 rounded-lg p-4">
          <div className="text-2xl font-bold text-slate-200">
            {stats.totalConceptsMastered}
          </div>
          <div className="text-sm text-slate-400">
            Concepts Mastered
          </div>
        </div>

        {/* Current Streak */}
        <div className="bg-slate-700 rounded-lg p-4">
          <div className={`text-2xl font-bold ${getStreakColor(stats.currentStreak)}`}>
            {stats.currentStreak}
          </div>
          <div className="text-sm text-slate-400">
            Day Streak
          </div>
        </div>

        {/* Flow State Time */}
        <div className="bg-slate-700 rounded-lg p-4">
          <div className="text-2xl font-bold text-blue-400">
            {formatFlowTime(stats.flowStateTime)}
          </div>
          <div className="text-sm text-slate-400">
            Flow State Time
          </div>
        </div>

        {/* Total Classes */}
        <div className="bg-slate-700 rounded-lg p-4">
          <div className="text-2xl font-bold text-slate-200">
            {stats.totalClasses}
          </div>
          <div className="text-sm text-slate-400">
            Active Classes
          </div>
        </div>
      </div>

      {/* Average Health Score */}
      <div className="mt-4 pt-4 border-t border-slate-700">
        <div className="flex items-center justify-between">
          <span className="text-sm text-slate-400">Average Health Score</span>
          <span className={`text-lg font-bold ${getHealthColor(stats.averageHealthScore)}`}>
            {stats.averageHealthScore}%
          </span>
        </div>
        <div className="w-full bg-slate-700 rounded-full h-2 mt-2">
          <div 
            className={`h-2 rounded-full transition-all duration-300 ${getHealthColor(stats.averageHealthScore).replace('text-', 'bg-')}`}
            style={{ width: `${stats.averageHealthScore}%` }}
          />
        </div>
      </div>
    </div>
  );
};

export default QuickStatsPanel; 