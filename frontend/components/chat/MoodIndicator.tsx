import React, { useState, useEffect } from 'react';

interface MoodIndicatorProps {
  affectiveState: 'NEUTRAL' | 'FRUSTRATED' | 'CONFIDENT' | 'CONFUSED' | 'EXCITED';
  confidence: number; // 0-1
  onEncouragement?: () => void;
}

interface MoodData {
  emoji: string;
  color: string;
  message: string;
  encouragement: string;
}

const MoodIndicator: React.FC<MoodIndicatorProps> = ({
  affectiveState,
  confidence,
  onEncouragement
}) => {
  const [showEncouragement, setShowEncouragement] = useState(false);
  const [lastState, setLastState] = useState(affectiveState);

  const moodData: Record<string, MoodData> = {
    NEUTRAL: {
      emoji: '😐',
      color: 'text-slate-400',
      message: 'Ready to learn',
      encouragement: 'You\'re doing great! Let\'s tackle this step by step.'
    },
    FRUSTRATED: {
      emoji: '😤',
      color: 'text-orange-400',
      message: 'Feeling stuck',
      encouragement: 'It\'s okay to feel stuck! Let\'s break this down into smaller pieces. What part is most confusing?'
    },
    CONFIDENT: {
      emoji: '😊',
      color: 'text-green-400',
      message: 'Feeling confident',
      encouragement: 'Excellent! Your confidence shows you\'re really understanding this material.'
    },
    CONFUSED: {
      emoji: '🤔',
      color: 'text-yellow-400',
      message: 'A bit confused',
      encouragement: 'Confusion is part of learning! Let\'s clarify this together. What would help you understand better?'
    },
    EXCITED: {
      emoji: '🤩',
      color: 'text-purple-400',
      message: 'Excited to learn',
      encouragement: 'Your enthusiasm is amazing! Let\'s channel that energy into solving this problem.'
    }
  };

  const currentMood = moodData[affectiveState];

  // Show encouragement when state changes to frustrated or confused
  useEffect(() => {
    if (affectiveState !== lastState) {
      setLastState(affectiveState);
      if (affectiveState === 'FRUSTRATED' || affectiveState === 'CONFUSED') {
        setShowEncouragement(true);
        // Auto-hide after 8 seconds
        setTimeout(() => setShowEncouragement(false), 8000);
      }
    }
  }, [affectiveState, lastState]);

  // Confidence indicator
  const getConfidenceColor = () => {
    if (confidence >= 0.8) return 'text-green-400';
    if (confidence >= 0.6) return 'text-yellow-400';
    if (confidence >= 0.4) return 'text-orange-400';
    return 'text-red-400';
  };

  const getConfidenceEmoji = () => {
    if (confidence >= 0.8) return '💪';
    if (confidence >= 0.6) return '👍';
    if (confidence >= 0.4) return '🤔';
    return '😰';
  };

  return (
    <div className="fixed top-4 left-4 z-20 max-w-xs mt-2">
      {/* Main mood indicator only */}
      <div className={`flex items-center gap-2 bg-slate-800/80 backdrop-blur-sm rounded-lg p-3 border border-slate-700 transition-all duration-300 ${currentMood.color}`}>
        <span className="text-2xl">{currentMood.emoji}</span>
        <div className="text-sm">
          <div className="font-medium">{currentMood.message}</div>
          <div className="text-xs text-slate-400">
            Confidence: {Math.round(confidence * 100)}%
          </div>
        </div>
      </div>

      {/* Encouragement popup */}
      {showEncouragement && (
        <div className="mt-3 bg-blue-900/90 backdrop-blur-sm border border-blue-700 rounded-lg p-4 max-w-xs animate-fade-in">
          <div className="flex items-start gap-3">
            <span className="text-2xl">💙</span>
            <div className="text-sm text-blue-100">
              <div className="font-medium mb-1">Your AI Partner says:</div>
              <div className="text-blue-200">{currentMood.encouragement}</div>
            </div>
          </div>
          <button
            onClick={() => {
              setShowEncouragement(false);
              onEncouragement?.();
            }}
            className="mt-3 text-xs bg-blue-600 hover:bg-blue-500 text-white px-3 py-1 rounded transition-colors"
          >
            Got it
          </button>
        </div>
      )}
    </div>
  );
};

export default MoodIndicator; 