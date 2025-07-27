// frontend/src/pages/TutorPage.tsx

import React from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from '../../types';

// Component Imports
import ChatMentor from '../../components/ChatMentor';

interface TutorPageProps {
  nodes: GraphNode[];
  edges: Edge[];
  knowledgeState: KnowledgeState;
  handlePartialKnowledgeStateChange: (nodeId: string, value: Partial<{ mu: number; sigma: number }>) => void;
  proofCode: string;
  chatHistory: ChatMessage[];
  isAiLoading: boolean;
  chatMode: 'chat' | 'verify';
  handleSendMessage: (message: string) => void;
  handleVerifyProofStep: (step: string) => void;
  handleContextualQuery: (selectedText: string, contextText: string) => void;
  handleFinishExam: () => void;
  currentView: string;
  setCurrentView: (view: string) => void;
  chatInput?: string;
  onChatInputChange?: (value: string) => void;
}

const TutorPage: React.FC<TutorPageProps> = ({
  nodes,
  edges,
  knowledgeState,
  handlePartialKnowledgeStateChange,
  proofCode,
  chatHistory,
  isAiLoading,
  chatMode,
  handleSendMessage,
  handleVerifyProofStep,
  handleContextualQuery,
  handleFinishExam,
  currentView,
  setCurrentView,
  chatInput = '',
  onChatInputChange,
}) => {
  if (nodes.length === 0) {
    return <div className="text-center p-8">Loading session...</div>;
  }
  
  return (
    <div className="flex flex-col h-full max-w-4xl mx-auto">
      {/* Header */}
      <div className="flex items-center justify-between p-6 border-b border-slate-700">
        <div>
          <h1 className="text-2xl font-bold text-blue-400">Learning Session</h1>
          <p className="text-slate-400 mt-1">
            {nodes.length} concepts loaded • {Object.keys(knowledgeState).length} mastery tracked
          </p>
        </div>
        <div className="flex gap-3">
          <button
            onClick={() => setCurrentView('progress')}
            className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
          >
            View Progress
          </button>
          <button
            onClick={handleFinishExam}
            className="px-4 py-2 rounded-lg bg-red-600 hover:bg-red-500 transition-colors font-medium"
          >
            End Session
          </button>
        </div>
      </div>

      {/* Main Chat Interface */}
      <div className="flex-1 flex flex-col min-h-0">
        <ChatMentor
          history={chatHistory}
          isLoading={isAiLoading}
          mode={chatMode}
          onSendMessage={handleSendMessage}
          onVerifyStep={handleVerifyProofStep}
          onContextualQuery={handleContextualQuery}
          inputValue={chatInput}
          onInputChange={onChatInputChange}
        />
      </div>

      {/* Footer with Quick Actions */}
      <div className="p-4 border-t border-slate-700 bg-slate-800/50">
        <div className="flex justify-center gap-4">
          <button
            onClick={() => setCurrentView('graph')}
            className="px-3 py-2 text-sm rounded-md bg-slate-700 hover:bg-slate-600 transition-colors"
          >
            Knowledge Graph
          </button>
          <button
            onClick={() => setCurrentView('mastery')}
            className="px-3 py-2 text-sm rounded-md bg-slate-700 hover:bg-slate-600 transition-colors"
          >
            Mastery Panel
          </button>
          {proofCode && (
            <button
              onClick={() => setCurrentView('proof')}
              className="px-3 py-2 text-sm rounded-md bg-slate-700 hover:bg-slate-600 transition-colors"
            >
              Proof State
            </button>
          )}
        </div>
      </div>
    </div>
  );
};

export default TutorPage; 