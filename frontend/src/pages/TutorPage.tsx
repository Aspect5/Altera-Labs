// frontend/src/pages/TutorPage.tsx

import React, { useState } from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from '../../types/components';

// Component Imports
import { ChatMentor, ProgressFlowers, MoodIndicator, AchievementSystem } from '../../components';
import { SidebarVine } from '../../components/learning/ProgressFlowers';
import { SolutionPopup } from '../../components/common/SolutionPopup';
import { uploadHomework } from '../../services';

// Error Boundary Component
class TutorPageErrorBoundary extends React.Component<
  { children: React.ReactNode },
  { hasError: boolean; error?: Error }
> {
  constructor(props: { children: React.ReactNode }) {
    super(props);
    this.state = { hasError: false };
  }

  static getDerivedStateFromError(error: Error) {
    return { hasError: true, error };
  }

  componentDidCatch(error: Error, errorInfo: React.ErrorInfo) {
    console.error('TutorPage Error Boundary caught an error:', error, errorInfo);
  }

  render() {
    if (this.state.hasError) {
      return (
        <div className="flex flex-col items-center justify-center h-full p-8 bg-red-900/20 border border-red-700 rounded-lg">
          <h2 className="text-xl font-bold text-red-400 mb-4">Something went wrong</h2>
          <p className="text-slate-400 mb-4 text-center">
            There was an error rendering the tutor page. Please try refreshing the page.
          </p>
          <details className="text-sm text-slate-500 max-w-md">
            <summary className="cursor-pointer mb-2">Error Details</summary>
            <pre className="bg-slate-800 p-2 rounded text-xs overflow-auto">
              {this.state.error?.toString()}
            </pre>
          </details>
          <button
            onClick={() => window.location.reload()}
            className="mt-4 px-4 py-2 bg-red-600 hover:bg-red-500 text-white rounded-lg transition-colors"
          >
            Refresh Page
          </button>
        </div>
      );
    }

    return this.props.children;
  }
}

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
  onInputChange?: (value: string) => void;
  onBackToDashboard?: () => void;
  affectiveState?: 'NEUTRAL' | 'FRUSTRATED' | 'CONFIDENT' | 'CONFUSED' | 'EXCITED';
  confidence?: number;
  gamificationState?: any;
  onAchievementUnlocked?: (achievement: any) => void;
}

const TutorPage: React.FC<TutorPageProps> = ({
  nodes,
  // edges,
  knowledgeState,
  // handlePartialKnowledgeStateChange,
  proofCode,
  chatHistory,
  isAiLoading,
  chatMode,
  handleSendMessage,
  handleVerifyProofStep,
  handleContextualQuery,
  handleFinishExam,
  // currentView,
  setCurrentView,
  chatInput = '',
  onInputChange,
  onBackToDashboard,
  affectiveState = 'NEUTRAL',
  confidence = 0.5,
  gamificationState,
  onAchievementUnlocked,
}) => {
  // Calculate proof progress based on proof code content
  const calculateProofProgress = (code: string): number => {
    if (!code) return 0;
    
    // Check if proof is complete (no 'sorry' placeholder)
    if (!code.includes('sorry')) return 1.0;
    
    // Count proof steps (lines that contain tactics or reasoning)
    const lines = code.split('\n').filter(line => line.trim());
    const proofLines = lines.filter(line => 
      line.includes('by') || 
      line.includes('rw') || 
      line.includes('simp') || 
      line.includes('apply') ||
      line.includes('exact') ||
      line.includes('intro') ||
      line.includes('cases') ||
      line.includes('induction')
    );
    
    // Calculate progress based on proof steps vs total lines
    const totalLines = lines.length;
    const proofSteps = proofLines.length;
    
    // Base progress on proof steps, but cap at 0.9 until complete
    const stepProgress = Math.min(0.9, proofSteps / Math.max(1, totalLines - 2));
    
    return stepProgress;
  };

  // File upload state
  const [uploadedFile, setUploadedFile] = useState<File | null>(null);
  const [isUploading, setIsUploading] = useState(false);
  const [uploadError, setUploadError] = useState<string | null>(null);
  
  // Enhanced homework upload state
  const [homeworkResult, setHomeworkResult] = useState<any>(null);
  const [showSolutionPopup, setShowSolutionPopup] = useState(false);
  const [uploadProgress, setUploadProgress] = useState<string>('');
  const [autoSolveAttempts, setAutoSolveAttempts] = useState<number>(0);

  const handleFileUpload = async (file: File) => {
    setIsUploading(true);
    setUploadError(null);
    setUploadProgress('Processing homework file...');
    setAutoSolveAttempts(0);
    
    try {
      // Step 1: Upload and process homework
      setUploadProgress('AI is analyzing your homework...');
      const result = await uploadHomework(file);
      setHomeworkResult(result);
      setUploadedFile(file);
      
      // Step 2: Show auto-solve progress
      if (result.solutions && result.solutions.length > 0) {
        setUploadProgress('AI is attempting to solve...');
        
        // Simulate progress updates for each solution attempt
        for (let i = 0; i < result.solutions.length; i++) {
          const solution = result.solutions[i];
          if (solution.solution && solution.solution.attempts) {
            setAutoSolveAttempts(solution.solution.attempts.length);
            
            // Check if any solution was found
            if (solution.solution.solved) {
              setUploadProgress('Solution found!');
              setShowSolutionPopup(true);
              break;
            }
          }
          
          // Small delay to show progress
          await new Promise(resolve => setTimeout(resolve, 500));
        }
      }
      
      setUploadProgress('Upload complete');
      console.log('Homework processed successfully:', result);
      
    } catch (error: any) {
      setUploadError(error.message || 'Upload failed');
      setUploadProgress('');
      console.error('Upload error:', error);
    } finally {
      setIsUploading(false);
    }
  };

  // Debug logging (reduced for production)
  // REMOVED: console.log statements that run on every render for better performance

  // Defensive checks
  if (!nodes || nodes.length === 0) {
    return (
      <div className="flex flex-col items-center justify-center h-full p-8">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-400 mb-4"></div>
        <p className="text-slate-400">Loading session...</p>
      </div>
    );
  }

  if (!knowledgeState) {
    return (
      <div className="flex flex-col items-center justify-center h-full p-8">
        <p className="text-red-400 mb-4">Error: Knowledge state not available</p>
        <button
          onClick={() => window.location.reload()}
          className="px-4 py-2 bg-red-600 hover:bg-red-500 text-white rounded-lg transition-colors"
        >
          Refresh Page
        </button>
      </div>
    );
  }

  if (!chatHistory) {
    return (
      <div className="flex flex-col items-center justify-center h-full p-8">
        <p className="text-red-400 mb-4">Error: Chat history not available</p>
        <button
          onClick={() => window.location.reload()}
          className="px-4 py-2 bg-red-600 hover:bg-red-500 text-white rounded-lg transition-colors"
        >
          Refresh Page
        </button>
      </div>
    );
  }

  // TEST MODE: Render minimal version first to isolate the issue
  const TEST_MODE = false;
  
  if (TEST_MODE) {
    return (
      <TutorPageErrorBoundary>
        <div className="flex flex-col h-full max-w-4xl mx-auto">
          {/* Header */}
          <div className="flex items-center justify-between p-6 border-b border-slate-700">
            <div>
              <h1 className="text-2xl font-bold text-blue-400">Learning Session (TEST MODE)</h1>
              <p className="text-slate-400 mt-1">
                {nodes.length} concepts loaded • {Object.keys(knowledgeState).length} mastery tracked
              </p>
            </div>
            <div className="flex gap-3">
              {onBackToDashboard && (
                <button
                  onClick={onBackToDashboard}
                  className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
                >
                  ← Dashboard
                </button>
              )}
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

          {/* Main Chat Interface - TEST VERSION */}
          <div className="flex-1 flex flex-col min-h-0 p-6">
            <div className="bg-slate-800 rounded-lg p-4 mb-4">
              <h2 className="text-lg font-semibold text-slate-200 mb-2">Chat History (TEST)</h2>
              <div className="space-y-2">
                {chatHistory.map((msg, index) => (
                  <div key={index} className={`p-2 rounded ${msg.role === 'user' ? 'bg-blue-600' : 'bg-slate-700'}`}>
                    <span className="text-xs text-slate-400">{msg.role}:</span>
                    <p className="text-slate-200">{msg.content}</p>
                  </div>
                ))}
              </div>
            </div>
            
            <div className="bg-slate-800 rounded-lg p-4">
              <h2 className="text-lg font-semibold text-slate-200 mb-2">Chat Input (TEST)</h2>
              <textarea
                value={chatInput}
                onChange={(e) => onInputChange?.(e.target.value)}
                placeholder="Type your message..."
                className="w-full p-2 bg-slate-700 border border-slate-600 rounded text-slate-200"
                rows={3}
              />
              <button
                onClick={() => handleSendMessage('Test message')}
                className="mt-2 px-4 py-2 bg-blue-600 hover:bg-blue-700 text-white rounded"
              >
                Send Test Message
              </button>
            </div>
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
      </TutorPageErrorBoundary>
    );
  }
  
  return (
    <TutorPageErrorBoundary>
      <div className="relative flex flex-col h-full max-w-4xl mx-auto">
        <SidebarVine height={100} />
        {/* Header */}
        <div className="flex items-center justify-between p-6 border-b border-slate-700">
          <div>
            <h1 className="text-2xl font-bold text-blue-400">Learning Session</h1>
            <p className="text-slate-400 mt-1">
              {nodes.length} concepts loaded • {Object.keys(knowledgeState).length} mastery tracked
              {proofCode && (
                <span className="ml-2 text-green-400">
                  • Proof Progress: {Math.round(calculateProofProgress(proofCode) * 100)}%
                </span>
              )}
            </p>
          </div>
          <div className="flex gap-3">
            {onBackToDashboard && (
              <button
                onClick={onBackToDashboard}
                className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
              >
                ← Dashboard
              </button>
            )}
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
          <TutorPageErrorBoundary>
            <ChatMentor
              history={chatHistory}
              isLoading={isAiLoading}
              mode={chatMode}
              onSendMessage={handleSendMessage}
              onVerifyStep={handleVerifyProofStep}
              onContextualQuery={handleContextualQuery}
              inputValue={chatInput}
              onInputChange={onInputChange}
            />
          </TutorPageErrorBoundary>
          
          {/* File Upload Section */}
          <div className="p-4 border-t border-slate-700 bg-slate-800/30">
            <div className="flex items-center gap-4">
              <div className="flex-1">
                <label className="block text-sm font-medium text-slate-300 mb-2">
                  Upload Homework (.tex, .txt, .pdf)
                </label>
                <input
                  type="file"
                  accept=".tex,.txt,.pdf"
                  onChange={(e) => {
                    const file = e.target.files?.[0];
                    if (file) handleFileUpload(file);
                  }}
                  className="block w-full text-sm text-slate-400
                    file:mr-4 file:py-2 file:px-4
                    file:rounded-full file:border-0
                    file:text-sm file:font-semibold
                    file:bg-blue-600 file:text-white
                    hover:file:bg-blue-700
                    file:cursor-pointer"
                  disabled={isUploading}
                />
              </div>
              {isUploading && (
                <div className="flex items-center gap-2 text-blue-400">
                  <div className="animate-spin rounded-full h-4 w-4 border-b-2 border-blue-400"></div>
                  <span className="text-sm">Uploading...</span>
                </div>
              )}
              {uploadedFile && (
                <div className="flex items-center gap-2 text-green-400">
                  <span className="text-sm">✓ {uploadedFile.name}</span>
                </div>
              )}
            </div>
            {uploadError && (
              <div className="mt-2 text-red-400 text-sm">
                Error: {uploadError}
              </div>
            )}
          </div>
        </div>

        {/* Gamification and Progress Components */}
        <TutorPageErrorBoundary>
          <ProgressFlowers
            knowledgeState={knowledgeState}
            proofProgress={calculateProofProgress(proofCode)}
            isActive={true}
            theme="nature"
          />
        </TutorPageErrorBoundary>

        <TutorPageErrorBoundary>
          <MoodIndicator
            affectiveState={affectiveState}
            confidence={confidence}
            onEncouragement={() => {
              // TODO: Trigger encouraging response from AI
              console.log('Encouragement requested');
            }}
          />
        </TutorPageErrorBoundary>

        {gamificationState && (
          <TutorPageErrorBoundary>
            <AchievementSystem
              gamificationState={gamificationState}
              onAchievementUnlocked={onAchievementUnlocked}
            />
          </TutorPageErrorBoundary>
        )}

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

        {/* Enhanced Upload Progress */}
        {isUploading && uploadProgress && (
          <div className="fixed top-4 left-1/2 transform -translate-x-1/2 z-50 bg-slate-800 border border-slate-700 rounded-lg p-4 shadow-lg">
            <div className="flex items-center gap-3">
              <div className="animate-spin rounded-full h-5 w-5 border-b-2 border-blue-400"></div>
              <div>
                <div className="text-white font-medium">{uploadProgress}</div>
                {autoSolveAttempts > 0 && (
                  <div className="text-sm text-slate-400">Attempt {autoSolveAttempts}</div>
                )}
              </div>
            </div>
          </div>
        )}

        {/* Solution Popup */}
        <SolutionPopup
          isVisible={showSolutionPopup}
          onClose={() => setShowSolutionPopup(false)}
          onViewSolution={() => {
            setShowSolutionPopup(false);
            // TODO: Navigate to developer panel or show solution details
            console.log('View solution clicked');
          }}
          onStartTutoring={() => {
            setShowSolutionPopup(false);
            // TODO: Start interactive tutoring session
            console.log('Start tutoring clicked');
          }}
          solution={homeworkResult?.solutions?.[0]?.solution || null}
        />
      </div>
    </TutorPageErrorBoundary>
  );
};

export default TutorPage; 