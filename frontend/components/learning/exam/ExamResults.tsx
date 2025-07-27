// frontend/components/learning/exam/ExamResults.tsx

import React from 'react';
import { GraphNode, KnowledgeState } from '../../../types/components';
import { calculateMasteryProbability } from '../../../services/bayesianService';

// Define the shape of the data this component expects.
interface ExamResultsProps {
  // All the concepts that were part of the exam.
  nodes: GraphNode[];
  // The student's final knowledge state after the exam.
  finalKnowledgeState: KnowledgeState;
  // A callback to the parent component to start a new practice session.
  onStartPersonalizedPractice: (practiceNodeIds: string[]) => void;
  // A callback to return to the main dashboard.
  onReturnToDashboard: () => void;
}

// A small sub-component to render a single concept's results.
const ConceptResultItem: React.FC<{ node: GraphNode; state: { mu: number; sigma: number } }> = ({ node, state }) => {
  const masteryProb = calculateMasteryProbability(state.mu, state.sigma);
  const isMastered = masteryProb > 0.8;

  return (
    <li className="flex items-center justify-between p-3 bg-slate-800/50 rounded-md">
      <span className="font-medium text-slate-300">{node.label}</span>
      <div className="flex items-center gap-2">
        <span className={`font-bold text-sm ${isMastered ? 'text-green-400' : 'text-yellow-400'}`}>
          {isMastered ? 'Mastered' : 'Needs Review'}
        </span>
        <div className={`w-4 h-4 rounded-full ${isMastered ? 'bg-green-500' : 'bg-yellow-500'}`}></div>
      </div>
    </li>
  );
};

/**
 * A component to display the results of an "Exam Mode" session.
 * It provides an overall score, a breakdown by concept, and an action to
 * start a personalized practice session based on areas of weakness.
 */
const ExamResults: React.FC<ExamResultsProps> = ({ nodes, finalKnowledgeState, onStartPersonalizedPractice, onReturnToDashboard }) => {
  // Calculate the overall score based on the mastery probability of all concepts.
  const overallMastery = nodes.reduce((acc, node) => {
    const state = finalKnowledgeState[node.id];
    return acc + (state ? calculateMasteryProbability(state.mu, state.sigma) : 0);
  }, 0) / (nodes.length || 1);

  const score = Math.round(overallMastery * 100);

  // Identify the concepts that need review (mastery probability < 80%).
  const conceptsToReview = nodes.filter(node => {
    const state = finalKnowledgeState[node.id];
    return state ? calculateMasteryProbability(state.mu, state.sigma) < 0.8 : true;
  });

  const handlePracticeClick = () => {
    // Pass the IDs of the weak concepts to the parent component.
    const practiceNodeIds = conceptsToReview.map(node => node.id);
    onStartPersonalizedPractice(practiceNodeIds);
  };

  return (
    <div className="flex justify-center items-center h-full bg-gray-900 p-4">
      <div className="w-full max-w-2xl bg-slate-800 rounded-xl shadow-2xl border border-slate-700 p-6 md:p-8">
        <header className="text-center border-b border-slate-700 pb-4 mb-6">
          <h1 className="text-3xl font-bold text-blue-400">Exam Results</h1>
          <p className="text-slate-400 mt-1">Here's a summary of your performance.</p>
        </header>

        <div className="text-center my-8">
          <p className="text-slate-300 text-lg">Overall Mastery</p>
          <p className={`text-7xl font-bold ${score >= 80 ? 'text-green-500' : 'text-yellow-500'}`}>
            {score}%
          </p>
        </div>

        <div className="mb-8">
          <h2 className="text-xl font-semibold text-cyan-400 mb-4">Concept Breakdown</h2>
          {nodes.length > 0 ? (
            <ul className="space-y-2 max-h-60 overflow-y-auto pr-2">
              {nodes.map(node => (
                <ConceptResultItem key={node.id} node={node} state={finalKnowledgeState[node.id]} />
              ))}
            </ul>
          ) : (
            <p className="text-slate-500 text-center">No concepts were assessed in this exam.</p>
          )}
        </div>

        {conceptsToReview.length > 0 && (
          <div className="text-center bg-slate-900/50 p-6 rounded-lg mb-6">
            <h3 className="text-lg font-semibold text-slate-200">Ready for a targeted review?</h3>
            <p className="text-slate-400 my-2">
              You have {conceptsToReview.length} concept{conceptsToReview.length > 1 ? 's' : ''} to review.
            </p>
            <button
              onClick={handlePracticeClick}
              className="mt-4 w-full sm:w-auto bg-cyan-600 text-white font-bold py-3 px-6 rounded-md hover:bg-cyan-500 transition-colors text-lg"
            >
              Start Personalized Practice
            </button>
          </div>
        )}

        <div className="text-center mt-4">
            <button onClick={onReturnToDashboard} className="text-slate-400 hover:text-white text-sm">
                &larr; Return to Dashboard
            </button>
        </div>
      </div>
    </div>
  );
};

export default ExamResults;
