import React, { useState, useEffect } from 'react';
import { Achievement, GamificationState } from '../../types/components';

interface AchievementSystemProps {
  gamificationState: GamificationState;
  onAchievementUnlocked?: (achievement: Achievement) => void;
}

const AchievementSystem: React.FC<AchievementSystemProps> = ({
  gamificationState,
  onAchievementUnlocked
}) => {
  const [showNotification, setShowNotification] = useState<Achievement | null>(null);
  const [recentlyUnlocked, setRecentlyUnlocked] = useState<Achievement[]>([]);

  // Check for newly unlocked achievements
  useEffect(() => {
    const newlyUnlocked = gamificationState.achievements.filter(
      achievement => achievement.unlockedAt && 
      achievement.unlockedAt.getTime() > Date.now() - 5000 // Last 5 seconds
    );

    if (newlyUnlocked.length > 0) {
      setShowNotification(newlyUnlocked[0]);
      setRecentlyUnlocked(prev => [...newlyUnlocked, ...prev].slice(0, 3));
      
      // Auto-hide notification after 4 seconds
      setTimeout(() => setShowNotification(null), 4000);
      
      // Trigger callback
      onAchievementUnlocked?.(newlyUnlocked[0]);
    }
  }, [gamificationState.achievements, onAchievementUnlocked]);

  const getLevelColor = (level: number) => {
    if (level >= 20) return 'text-purple-400';
    if (level >= 15) return 'text-red-400';
    if (level >= 10) return 'text-orange-400';
    if (level >= 5) return 'text-yellow-400';
    return 'text-green-400';
  };

  const getLevelTitle = (level: number) => {
    if (level >= 20) return 'Legendary Learner';
    if (level >= 15) return 'Master Mathematician';
    if (level >= 10) return 'Proof Prodigy';
    if (level >= 5) return 'Knowledge Knight';
    return 'Learning Apprentice';
  };

  return (
    <>
      {/* Achievement Notification */}
      {showNotification && (
        <div className="fixed top-1/2 left-1/2 transform -translate-x-1/2 -translate-y-1/2 z-50 animate-bounce">
          <div className="bg-gradient-to-r from-yellow-400 to-orange-500 rounded-lg p-6 shadow-2xl border-2 border-yellow-300">
            <div className="text-center">
              <div className="text-4xl mb-2">🏆</div>
              <div className="text-xl font-bold text-white mb-1">
                Achievement Unlocked!
              </div>
              <div className="text-lg font-semibold text-white mb-2">
                {showNotification.name}
              </div>
              <div className="text-sm text-yellow-100">
                {showNotification.description}
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Gamification Stats Panel */}
      <div className="fixed bottom-4 left-4 bg-slate-800/90 backdrop-blur-sm rounded-lg p-6 min-w-[220px] max-w-xs border border-slate-700 z-10">
        <div className="text-center mb-3">
          <div className={`text-2xl font-bold ${getLevelColor(gamificationState.level)}`}>
            Level {gamificationState.level}
          </div>
          <div className="text-xs text-slate-400">
            {getLevelTitle(gamificationState.level)}
          </div>
        </div>

        <div className="space-y-2">
          {/* Points */}
          <div className="flex items-center justify-between text-sm">
            <span className="text-slate-300">Points</span>
            <span className="text-yellow-400 font-bold">
              {gamificationState.points.toLocaleString()}
            </span>
          </div>

          {/* Streak */}
          <div className="flex items-center justify-between text-sm">
            <span className="text-slate-300">Streak</span>
            <span className="text-green-400 font-bold">
              {gamificationState.streak} days 🔥
            </span>
          </div>

          {/* Progress to next level */}
          <div className="text-xs text-slate-400 mt-3">
            <div className="flex justify-between mb-1">
              <span>Progress to Level {gamificationState.level + 1}</span>
              <span>{Math.round((gamificationState.points % 1000) / 10)}%</span>
            </div>
            <div className="w-full bg-slate-700 rounded-full h-1">
              <div 
                className="bg-gradient-to-r from-yellow-400 to-orange-500 h-1 rounded-full transition-all duration-300"
                style={{ width: `${(gamificationState.points % 1000) / 10}%` }}
              />
            </div>
          </div>
        </div>

        {/* Recent Achievements */}
        {recentlyUnlocked.length > 0 && (
          <div className="mt-4 pt-3 border-t border-slate-700">
            <div className="text-xs text-slate-400 mb-2">Recent Achievements</div>
            <div className="space-y-1">
              {recentlyUnlocked.slice(0, 2).map((achievement) => (
                <div key={achievement.id} className="flex items-center gap-2 text-xs">
                  <span className="text-yellow-400">🏆</span>
                  <span className="text-slate-300 truncate">{achievement.name}</span>
                </div>
              ))}
            </div>
          </div>
        )}
      </div>
    </>
  );
};

export default AchievementSystem; 