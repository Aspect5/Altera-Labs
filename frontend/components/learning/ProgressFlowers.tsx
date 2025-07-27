import React, { useEffect, useState, useMemo } from 'react';
import { KnowledgeState } from '../../types/components';

interface ProgressFlowersProps {
  knowledgeState: KnowledgeState;
  proofProgress: number; // 0-1
  isActive: boolean;
  theme?: 'default' | 'nature' | 'space' | 'ocean';
}

interface Flower {
  id: string;
  x: number;
  y: number;
  size: number;
  color: string;
  bloomLevel: number; // 0-1
  animationDelay: number;
}

export const SidebarVine: React.FC<{height?: number}> = ({ height = 100 }) => (
  <div className="fixed right-8 bottom-8 flex flex-col items-center z-10 pointer-events-none" style={{maxWidth: '120px', minWidth: '80px'}}>
    <div className="bg-slate-900/80 rounded-2xl border border-slate-700 shadow-lg p-4 flex flex-col items-center">
      <svg width="60" height={height} viewBox={`0 0 60 ${height}`} fill="none" xmlns="http://www.w3.org/2000/svg">
        {/* Vine path, growing up from bottom */}
        <path d={`M30,${height} Q20,${height*0.75} 30,${height/2} Q40,${height*0.25} 30,0`} stroke="#15803d" strokeWidth="6" fill="none" />
        {/* Roses at intervals, from bottom up */}
        {[0.15, 0.35, 0.6, 0.85].map((t, i) => (
          <g key={i}>
            <circle cx={30 + (i%2===0?8:-8)} cy={height*(1-t)} r="14" fill="#be123c" stroke="#fff" strokeWidth="2" />
            <ellipse cx={30 + (i%2===0?8:-8)} cy={height*(1-t)} rx="8" ry="14" fill="#f87171" opacity="0.5" />
          </g>
        ))}
        {/* Leaves */}
        {[0.25, 0.5, 0.75].map((t, i) => (
          <ellipse key={i} cx={30 + (i%2===0?18:-18)} cy={height*(1-t)} rx="10" ry="4" fill="#22c55e" opacity="0.7" />
        ))}
      </svg>
    </div>
  </div>
);

const ProgressFlowers: React.FC<ProgressFlowersProps> = ({
  knowledgeState,
  proofProgress,
  isActive,
  theme = 'default'
}) => {
  const [flowers, setFlowers] = useState<Flower[]>([]);

  // Memoize the colors to prevent infinite re-renders
  const colors = useMemo(() => {
    switch (theme) {
      case 'nature':
        return {
          primary: '#10b981', // emerald
          secondary: '#059669',
          accent: '#34d399',
          background: '#064e3b'
        };
      case 'space':
        return {
          primary: '#6366f1', // indigo
          secondary: '#4f46e5',
          accent: '#818cf8',
          background: '#1e1b4b'
        };
      case 'ocean':
        return {
          primary: '#06b6d4', // cyan
          secondary: '#0891b2',
          accent: '#22d3ee',
          background: '#164e63'
        };
      default:
        return {
          primary: '#f59e0b', // amber
          secondary: '#d97706',
          accent: '#fbbf24',
          background: '#451a03'
        };
    }
  }, [theme]);

  useEffect(() => {
    if (!isActive) return;

    // Create flowers based on knowledge state and proof progress
    const newFlowers: Flower[] = Object.entries(knowledgeState).map(([nodeId, state], index) => {
      // Combine knowledge mastery with proof progress for bloom level
      const knowledgeLevel = state.mu;
      const combinedProgress = Math.min(1, (knowledgeLevel + proofProgress) / 2);
      const bloomLevel = Math.min(1, combinedProgress * 1.2); // Slightly boost for visual appeal
      
      // Size should grow with both knowledge and proof progress
      const baseSize = 20;
      const knowledgeSize = knowledgeLevel * 20;
      const proofSize = proofProgress * 30;
      const size = baseSize + knowledgeSize + proofSize;
      
      // Color based on combined progress
      const color = bloomLevel > 0.7 ? colors.primary : bloomLevel > 0.4 ? colors.secondary : colors.accent;
      
      return {
        id: nodeId,
        x: 30 + (index % 4) * 60, // More compact grid layout
        y: 30 + Math.floor(index / 4) * 60,
        size,
        color,
        bloomLevel,
        animationDelay: index * 0.1
      };
    });

    setFlowers(newFlowers);
  }, [knowledgeState, proofProgress, isActive, colors]);

  // Remove all rendering from ProgressFlowers
  if (!isActive) return null;
  return null;
};

export default ProgressFlowers; 