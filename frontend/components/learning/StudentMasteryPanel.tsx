import React from 'react';
import { GraphNode, KnowledgeState } from '../../types/components';
import { calculateMasteryProbability } from '../../services/bayesianService';

interface StudentMasteryPanelProps {
    nodes: GraphNode[];
    knowledgeState: KnowledgeState;
    onKnowledgeStateChange: (nodeId: string, value: Partial<{mu: number, sigma: number}>) => void;
}

const StudentMasteryPanel: React.FC<StudentMasteryPanelProps> = ({ nodes, knowledgeState, onKnowledgeStateChange }) => {
    
    const handleRandomize = () => {
        nodes.forEach(node => {
            // Generate random mastery (mu) between 0 and 1
            const randomMu = Math.random();
            // Generate random uncertainty (sigma) between 0.1 and 0.5
            const randomSigma = 0.1 + Math.random() * 0.4;
            
            onKnowledgeStateChange(node.id, {
                mu: randomMu,
                sigma: randomSigma
            });
        });
    };

    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <div className="flex justify-between items-center mb-3">
                <h2 className="text-xl font-semibold text-cyan-400">2. Simulate Student Knowledge</h2>
                <button
                    onClick={handleRandomize}
                    className="px-3 py-1 bg-purple-600 hover:bg-purple-500 text-white text-sm font-medium rounded-md transition-colors"
                >
                    Randomize
                </button>
            </div>
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
                            <div className="mb-3">
                                <label className="block text-sm text-slate-400 mb-1">
                                    Mastery (μ): {state.mu.toFixed(2)}
                                </label>
                                <input
                                    type="range"
                                    min="0"
                                    max="1"
                                    step="0.01"
                                    value={state.mu}
                                    onChange={(e) => onKnowledgeStateChange(node.id, { mu: parseFloat(e.target.value) })}
                                    className="w-full h-2 bg-slate-700 rounded-lg appearance-none cursor-pointer slider"
                                />
                                <div className="flex justify-between text-xs text-slate-500 mt-1">
                                    <span>0%</span>
                                    <span>50%</span>
                                    <span>100%</span>
                                </div>
                            </div>

                            {/* Uncertainty (sigma) Slider */}
                            <div>
                                <label className="block text-sm text-slate-400 mb-1">
                                    Uncertainty (σ): {state.sigma.toFixed(2)} ({uncertaintyPercent}%)
                                </label>
                                <input
                                    type="range"
                                    min="0.1"
                                    max="0.5"
                                    step="0.01"
                                    value={state.sigma}
                                    onChange={(e) => onKnowledgeStateChange(node.id, { sigma: parseFloat(e.target.value) })}
                                    className="w-full h-2 bg-slate-700 rounded-lg appearance-none cursor-pointer slider"
                                />
                                <div className="flex justify-between text-xs text-slate-500 mt-1">
                                    <span>Low</span>
                                    <span>High</span>
                                </div>
                            </div>
                        </div>
                    );
                })}
            </div>
        </div>
    );
};

export default StudentMasteryPanel;
