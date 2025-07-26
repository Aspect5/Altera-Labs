import React, { useState, useMemo } from 'react';
import { GraphNode, Edge, KnowledgeState } from '../types';
import Katex from './Katex';
import StudentKnowledgeVector from './StudentKnowledgeVector';
import { buildAdjacencyInfo } from '../services/bayesianService';

interface BayesianModelViewProps {
    nodes: GraphNode[];
    edges: Edge[];
    knowledgeState: KnowledgeState;
    onApplyPropagation: (newKnowledgeState: KnowledgeState) => void;
}

const BayesianModelView: React.FC<BayesianModelViewProps> = ({ nodes, edges, knowledgeState, onApplyPropagation }) => {
    const [propagatedState, setPropagatedState] = useState<KnowledgeState | null>(null);

    const adjacencyInfo = useMemo(() => {
        return buildAdjacencyInfo(nodes, edges);
    }, [nodes, edges]);

    const handlePropagation = () => {
        const { matrix: M, nodeOrder } = adjacencyInfo;
        const n = nodes.length;
        
        const M_sq = M.map(row => row.map(val => val * val));

        const mu_vec = nodeOrder.map(id => knowledgeState[id]?.mu || 0);
        const sigma_sq_vec = nodeOrder.map(id => Math.pow(knowledgeState[id]?.sigma || 0, 2));

        const mu_prior_vec = Array(n).fill(0);
        const sigma_prior_sq_vec = Array(n).fill(0);

        // Perform matrix-vector multiplication
        for (let i = 0; i < n; i++) {
            for (let j = 0; j < n; j++) {
                mu_prior_vec[i] += M[i][j] * mu_vec[j];
                sigma_prior_sq_vec[i] += M_sq[i][j] * sigma_sq_vec[j];
            }
            // Clamp mu values between 0 and 1
            mu_prior_vec[i] = Math.max(0, Math.min(1, mu_prior_vec[i]));
        }

        const newPropagatedState: KnowledgeState = {};
        nodeOrder.forEach((id, i) => {
            newPropagatedState[id] = {
                mu: mu_prior_vec[i],
                sigma: Math.min(0.5, Math.sqrt(sigma_prior_sq_vec[i])),
            };
        });

        setPropagatedState(newPropagatedState);
    };
    
    const handleApplyState = () => {
        if (propagatedState) {
            onApplyPropagation(propagatedState);
            setPropagatedState(null);
        }
    };

    if (nodes.length === 0) {
        return null;
    }

    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg space-y-6">
            <div>
                <h2 className="text-xl font-semibold text-cyan-400 mb-3">Bayesian Knowledge Model</h2>
                <p className="text-sm text-slate-400 mb-4">
                    This model tracks student knowledge with two parameters: mastery (<Katex math="\mu" />) and uncertainty (<Katex math="\sigma" />). Knowledge propagates through the graph based on prerequisite relationships.
                </p>
                <div className="grid grid-cols-1 md:grid-cols-2 gap-4 text-center p-4 bg-slate-900/50 rounded-lg">
                    <div>
                        <h3 className="font-semibold text-slate-300">Mastery Propagation</h3>
                        <Katex math="\vec{\mu}_{prior} = M \cdot \vec{\mu}" block />
                    </div>
                     <div>
                        <h3 className="font-semibold text-slate-300">Uncertainty Propagation</h3>
                        <Katex math="\vec{\sigma}_{prior}^2 = M^2 \cdot \vec{\sigma}^2" block />
                    </div>
                </div>
            </div>

            <div className="border-t border-slate-700 pt-4">
                 <h3 className="text-lg font-semibold text-cyan-400 mb-3">Interactive Propagation Simulation</h3>
                 <div className="flex flex-col sm:flex-row gap-4">
                    <button
                        onClick={handlePropagation}
                        className="bg-cyan-600 text-white font-bold py-2 px-4 rounded-md hover:bg-cyan-500 transition-colors flex-grow"
                    >
                        Simulate Knowledge Propagation
                    </button>
                    {propagatedState && (
                        <button
                            onClick={handleApplyState}
                            className="bg-emerald-600 text-white font-bold py-2 px-4 rounded-md hover:bg-emerald-500 transition-colors flex-grow"
                        >
                            Apply Propagated State
                        </button>
                    )}
                 </div>
            </div>

            {propagatedState && (
                <div className="border-t border-slate-700 pt-4">
                    <StudentKnowledgeVector 
                        nodes={nodes} 
                        knowledgeState={propagatedState} 
                        title="Propagated (Prior) Knowledge State" 
                    />
                </div>
            )}
        </div>
    );
};

export default BayesianModelView;
