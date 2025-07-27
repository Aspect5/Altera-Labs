import React from 'react';
import { GraphNode, KnowledgeState } from '../../types/components';
import { calculateMasteryProbability } from '../../services/bayesianService';

interface StudentKnowledgeVectorProps {
    nodes: GraphNode[];
    knowledgeState: KnowledgeState;
    title?: string;
}

const VectorDisplay: React.FC<{title: string; description: string; vectorString: string}> = ({title, description, vectorString}) => (
     <div>
        <h3 className="text-lg font-semibold text-cyan-400">{title}</h3>
        <p className="text-sm text-slate-400 mb-2">{description}</p>
        <div className="bg-slate-900 p-3 rounded-md text-slate-300 font-mono text-xs sm:text-sm max-h-40 overflow-y-auto">
            <pre><code>{vectorString}</code></pre>
        </div>
    </div>
)

const StudentKnowledgeVector: React.FC<StudentKnowledgeVectorProps> = ({ nodes, knowledgeState, title = "Student Knowledge State" }) => {
    
    const muVectorString = `{\n${nodes.map(node => `  "${node.id}": ${(knowledgeState[node.id]?.mu * 100 || 0).toFixed(0)}`).join(',\n')}\n}`;
    const sigmaVectorString = `{\n${nodes.map(node => `  "${node.id}": ${(knowledgeState[node.id] ? Math.round(knowledgeState[node.id].sigma / 0.5 * 100) : 0)}`).join(',\n')}\n}`;
    const masteryVectorString = `{\n${nodes.map(node => {
        const state = knowledgeState[node.id];
        const prob = state ? calculateMasteryProbability(state.mu, state.sigma) : 0;
        return `  "${node.id}": ${(prob * 100).toFixed(0)}`;
    }).join(',\n')}\n}`;
    
    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <h2 className="text-xl font-semibold text-cyan-400 mb-3">{title}</h2>
            <div className="space-y-4">
                <VectorDisplay 
                    title="μ Vector (Mastery)"
                    description="The student's mean skill estimate for each concept, as a percentage (0-100)."
                    vectorString={muVectorString}
                />
                <VectorDisplay 
                    title="σ Vector (Uncertainty)"
                    description="The system's uncertainty about the skill estimate, as a percentage (0-100). Lower is better."
                    vectorString={sigmaVectorString}
                />
                 <VectorDisplay 
                    title="P(Mastery) Vector"
                    description="The probability that the student has mastered the concept (μ > 0.85), as a percentage."
                    vectorString={masteryVectorString}
                />
            </div>
        </div>
    );
};

export default StudentKnowledgeVector;
