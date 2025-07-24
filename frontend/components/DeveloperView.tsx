import React from 'react';
import { GraphNode, Edge, KnowledgeState } from '../types';
import AdjacencyMatrix from './AdjacencyMatrix';
import StudentKnowledgeVector from './StudentKnowledgeVector';
import DiagnosticTracePanel from './DiagnosticTracePanel';
import BayesianModelView from './BayesianModelView';

interface DeveloperViewProps {
    nodes: GraphNode[];
    edges: Edge[];
    knowledgeState: KnowledgeState;
    diagnosticTrace: string[];
    onApplyPropagation: (newKnowledgeState: KnowledgeState) => void;
}

const DeveloperView: React.FC<DeveloperViewProps> = ({ nodes, edges, knowledgeState, diagnosticTrace, onApplyPropagation }) => {
    return (
        <div className="space-y-6">
            <BayesianModelView 
                nodes={nodes} 
                edges={edges}
                knowledgeState={knowledgeState}
                onApplyPropagation={onApplyPropagation}
            />
            <StudentKnowledgeVector nodes={nodes} knowledgeState={knowledgeState} />
            <AdjacencyMatrix nodes={nodes} edges={edges} />
            {diagnosticTrace.length > 0 && (
                <DiagnosticTracePanel trace={diagnosticTrace} />
            )}
        </div>
    );
};

export default DeveloperView;