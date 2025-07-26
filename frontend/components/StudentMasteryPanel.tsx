import React from 'react';
import { GraphNode, KnowledgeState } from '../types';
import { calculateMasteryProbability } from '../services/bayesianService';

interface StudentMasteryPanelProps {
    nodes: GraphNode[];
    knowledgeState: KnowledgeState;
    onKnowledgeStateChange: (nodeId: string, value: Partial<{ mu: number; sigma: number }>) => void;
}

const getMasteryColorClass = (mu: number): string => {
    if (mu > 0.8) return 'accent-green-500';
    if (mu > 0.4) return 'accent-yellow-400';
    if (mu > 0.0) return 'accent-red-500';
    return 'accent-gray-500';
};

const StudentMasteryPanel: React.FC<StudentMasteryPanelProps> = ({ nodes, knowledgeState, onKnowledgeStateChange }) => {
    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <h2 className="text-xl font-semibold text-cyan-400 mb-3">2. Simulate Student Knowledge</h2>
            <div className="space-y-5">
                {nodes.map(node => {
                    const state = knowledgeState[node.id] || { mu: 0, sigma: 0.5 };
                    const uncertaintyPercent = Math.round((state.sigma / 0.5) * 100);
                    const masteryProb = calculateMasteryProbability(state.mu, state.sigma);

                    return (
                        <div key={node.id}>
                            <p className="block text-md font-medium text-slate-300 mb-2 flex justify-between items-center">
                               <span>{node.label}</span>
                               <span className="text-xs font-mono bg-cyan-900/50 text-cyan-300 px-2 py-1 rounded">
                                   P(Mastery): {(masteryProb * 100).toFixed(0)}%
                               </span>
                            </p>
                            {/* Mastery (mu) Slider */}
                            <div>
                                <label htmlFor={`mu-${node.id}`} className="block text-xs font-medium text-slate-400">
                                   Mastery (μ): <span className="font-bold text-slate-200">{Math.round(state.mu * 100)}%</span>
                                </label>
                                <input
                                    id={`mu-${node.id}`}
                                    type="range"
                                    min="0"
                                    max="1"
                                    step="0.01"
                                    value={state.mu}
                                    onChange={(e) => onKnowledgeStateChange(node.id, { mu: parseFloat(e.target.value) })}
                                    className={`w-full h-2 bg-slate-700 rounded-lg appearance-none cursor-pointer ${getMasteryColorClass(state.mu)}`}
                                />
                            </div>
                             {/* Uncertainty (sigma) Slider */}
                            <div className="mt-2">
                                <label htmlFor={`sigma-${node.id}`} className="block text-xs font-medium text-slate-400">
                                   Uncertainty (σ): <span className="font-bold text-slate-200">{uncertaintyPercent}%</span>
                                </label>
                                <input
                                    id={`sigma-${node.id}`}
                                    type="range"
                                    min="0.01"
                                    max="0.5"
                                    step="0.01"
                                    value={state.sigma}
                                    onChange={(e) => onKnowledgeStateChange(node.id, { sigma: parseFloat(e.target.value) })}
                                    className="w-full h-2 bg-slate-700 rounded-lg appearance-none cursor-pointer accent-sky-400"
                                />
                            </div>
                        </div>
                    );
                })}
            </div>
        </div>
    );
};

export default StudentMasteryPanel;
