import React from 'react';
import { ClassSummary } from '../../types/components';

interface ClassHealthCardProps {
  classData: ClassSummary;
  onClick: () => void;
  onDelete?: (id: string) => void;
}

const ClassHealthCard: React.FC<ClassHealthCardProps> = ({ classData, onClick, onDelete }) => {
  const getHealthColor = (score: number) => {
    if (score >= 80) return 'text-green-400';
    if (score >= 60) return 'text-yellow-400';
    if (score >= 40) return 'text-orange-400';
    return 'text-red-400';
  };

  const getPlantIcon = (state: ClassSummary['plantState']) => {
    switch (state) {
      case 'flourishing':
        return '🌱';
      case 'healthy':
        return '🌿';
      case 'wilting':
        return '🥀';
      case 'struggling':
        return '🌱';
      default:
        return '🌱';
    }
  };

  const getHealthBarColor = (score: number) => {
    if (score >= 80) return 'bg-green-500';
    if (score >= 60) return 'bg-yellow-500';
    if (score >= 40) return 'bg-orange-500';
    return 'bg-red-500';
  };

  const formatLastSession = (date: Date | null) => {
    if (!date) return 'Never';
    const now = new Date();
    const diffInHours = Math.floor((now.getTime() - date.getTime()) / (1000 * 60 * 60));
    if (diffInHours < 1) return 'Just now';
    if (diffInHours < 24) return `${diffInHours}h ago`;
    const diffInDays = Math.floor(diffInHours / 24);
    if (diffInDays < 7) return `${diffInDays}d ago`;
    return date.toLocaleDateString();
  };

  return (
    <div 
      className="bg-slate-800 rounded-lg p-6 transition-all duration-200 border border-slate-700 hover:border-slate-600 group"
    >
      {/* Header with plant icon and health score */}
      <div className="flex items-center justify-between mb-4">
        <div className="flex items-center gap-3">
          <span className="text-2xl">{getPlantIcon(classData.plantState)}</span>
          <button onClick={onClick} className="text-left">
            <h3 className="text-lg font-semibold text-slate-200 group-hover:text-white transition-colors">
              {classData.name}
            </h3>
          </button>
        </div>
        <div className={`text-lg font-bold ${getHealthColor(classData.healthScore)}`}>
          {classData.healthScore}%
        </div>
      </div>

      {/* Health bar */}
      <div className="w-full bg-slate-700 rounded-full h-2 mb-4">
        <div 
          className={`h-2 rounded-full transition-all duration-300 ${getHealthBarColor(classData.healthScore)}`}
          style={{ width: `${classData.healthScore}%` }}
        />
      </div>

      {/* Stats */}
      <div className="space-y-2">
        <div className="flex justify-between text-sm">
          <span className="text-slate-400">Concepts Mastered</span>
          <span className="text-slate-200 font-medium">
            {classData.conceptsMastered} / {classData.totalConcepts}
          </span>
        </div>
        <div className="flex justify-between text-sm">
          <span className="text-slate-400">Last Session</span>
          <span className="text-slate-200 font-medium">
            {formatLastSession(classData.lastSession)}
          </span>
        </div>
      </div>

      {/* Footer actions */}
      <div className="mt-4 flex items-center justify-between text-xs text-slate-500 group-hover:text-slate-400 transition-colors">
        <span>Click to continue learning →</span>
        {onDelete && (
          <button
            onClick={(e) => { e.stopPropagation(); onDelete(classData.id); }}
            className="px-2 py-1 rounded bg-red-600 hover:bg-red-500 text-white text-xs"
            aria-label={`Delete ${classData.name}`}
            title="Delete class"
          >
            Delete
          </button>
        )}
      </div>
    </div>
  );
};

export default ClassHealthCard; 