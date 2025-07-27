// frontend/App.tsx

import React, { useState, useCallback, useEffect } from 'react';
import { Routes, Route, useNavigate } from 'react-router-dom';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from './types';

// API services
import { createClass, getConceptExplanation, finalizeExam, verifyProofStep, startSession, sendMessage } from './services/aiService';

// Page Components
import SetupPage from './src/pages/SetupPage';
import TutorPage from './src/pages/TutorPage';

// View Components
import KnowledgeGraph from './components/KnowledgeGraph';
import StudentMasteryPanel from './components/StudentMasteryPanel';

// View types for different learning modes

const App: React.FC = () => {
    const navigate = useNavigate();
    const [className, setClassName] = useState<string>("");
    const [nodes, setNodes] = useState<GraphNode[]>([]);
    const [edges, setEdges] = useState<Edge[]>([]);
    const [knowledgeState, setKnowledgeState] = useState<KnowledgeState>({});
    const [isAiLoading, setIsAiLoading] = useState<boolean>(false);
    const [error, setError] = useState<string | null>(null);
    const [currentView, setCurrentView] = useState<string>('chat');
    const [chatHistory, setChatHistory] = useState<ChatMessage[]>([]);
    const [finalKnowledgeState, setFinalKnowledgeState] = useState<KnowledgeState | null>(null);
    const [sessionStarted, setSessionStarted] = useState<boolean>(false);
    const [chatMode, setChatMode] = useState<'chat' | 'verify'>('chat');
    const [proofCode, setProofCode] = useState<string>("");
    const [isCreatingClass, setIsCreatingClass] = useState<boolean>(false);
    const [agentStatus, setAgentStatus] = useState<'SOLVED' | 'FAILED' | 'SYLLABUS_BASED' | null>(null);
    
    // Add input state management
    const [chatInput, setChatInput] = useState<string>("");

    const initializeTutoringSession = useCallback(async () => {
        if (sessionStarted) return;
        setIsAiLoading(true);
        setError(null);
        try {
            const response = await startSession('homework');
            setProofCode(response.proofCode);
            setChatHistory([{ role: 'model', content: response.aiResponse }]);
            setSessionStarted(true);
        } catch (e: any) {
            setError(e.message || 'Failed to start tutoring session.');
        } finally {
            setIsAiLoading(false);
        }
    }, [sessionStarted]);

    const handleSendMessage = useCallback(async (message: string) => {
        setIsAiLoading(true);
        setError(null);
        setChatHistory(prev => [...prev, { role: 'user', content: message }]);
        try {
            console.log('Sending message to backend:', message);
            const response = await sendMessage(message);
            console.log('Received response from backend:', response);
            
            if (response.proofCode) {
                setProofCode(response.proofCode);
            }
            
            const aiMessage: ChatMessage = { role: 'model', content: response.aiResponse };
            console.log('Adding AI message to chat history:', aiMessage);
            setChatHistory(prev => [...prev, aiMessage]);
            
            // Only switch to verify mode if the AI explicitly mentions proof verification
            // and we're not already in verify mode
            if (chatMode === 'chat' && 
                (response.aiResponse.toLowerCase().includes('proof step') || 
                 response.aiResponse.toLowerCase().includes('verify') ||
                 response.aiResponse.toLowerCase().includes('lean')) &&
                response.aiResponse.toLowerCase().includes('enter')) {
                console.log('Switching to verify mode based on AI response');
                setChatMode('verify');
            }
        } catch (e: any) {
            console.error('Error in handleSendMessage:', e);
            setError(e.message || 'Failed to send message.');
            setChatHistory(prev => [...prev, { role: 'model', content: "Sorry, I encountered an error. Please try again." }]);
        } finally {
            setIsAiLoading(false);
        }
    }, [chatMode]);

    useEffect(() => {
        if (nodes.length > 0 && !sessionStarted) {
            initializeTutoringSession();
        }
    }, [nodes.length, sessionStarted, initializeTutoringSession]);

    const handleCreateClass = useCallback(async (className: string, syllabusFile: File | null, homeworkFile: File | null) => {
        setIsCreatingClass(true);
        setError(null);
        try {
            const { concepts: newNodes, edges: newEdges, solutionStatus } = await createClass(className, syllabusFile, homeworkFile);
            setAgentStatus(solutionStatus);
            setNodes(newNodes);
            setEdges(newEdges);
            const initialKnowledge: KnowledgeState = newNodes.reduce((acc: KnowledgeState, node: GraphNode) => {
                acc[node.id] = { mu: 0, sigma: 0.5 };
                return acc;
            }, {} as KnowledgeState);
            setKnowledgeState(initialKnowledge);
            navigate('/tutor');
        } catch (e: any) {
            setError(e.message || 'Failed to process class.');
        } finally {
            setIsCreatingClass(false);
        }
    }, [navigate]);

    const handlePartialKnowledgeStateChange = (nodeId: string, value: Partial<{mu: number, sigma: number}>) => {
        setKnowledgeState(prev => ({ ...prev, [nodeId]: { ...prev[nodeId], ...value } }));
    };

    const handleContextualQuery = useCallback(async (selectedText: string, contextText: string) => {
        setIsAiLoading(true);
        const userQueryMessage: ChatMessage = { role: 'system', content: `[Asking for explanation of: "${selectedText}"]` };
        setChatHistory(prev => [...prev, userQueryMessage]);
        try {
            const { explanation } = await getConceptExplanation(selectedText, contextText);
            setChatHistory(prev => [...prev, { role: 'model', content: explanation }]);
        } catch (e: any) {
            setChatHistory(prev => [...prev, { role: 'model', content: `Sorry, I had trouble explaining that. Error: ${e.message}` }]);
        } finally {
            setIsAiLoading(false);
        }
    }, []);

    const handleFinishExam = async () => {
        setIsAiLoading(true);
        setError(null);
        try {
            console.log('Finalizing exam with knowledge state:', knowledgeState);
            const result = await finalizeExam(knowledgeState);
            console.log('Exam finalized successfully:', result);
            setFinalKnowledgeState(result.finalKnowledgeState);
            
            // Clear session state
            setSessionStarted(false);
            setChatHistory([]);
            setChatMode('chat');
            setProofCode("");
            
            // Show success message
            setChatHistory([{ 
                role: 'system', 
                content: `Session ended successfully. Final knowledge state saved.` 
            }]);
            
            // Optionally navigate to results page in the future
            // navigate('/results');
        } catch (e: any) {
            console.error('Error finalizing exam:', e);
            setError(e.message || 'Failed to finalize the exam session.');
            setChatHistory(prev => [...prev, { 
                role: 'system', 
                content: `Error ending session: ${e.message || 'Unknown error'}` 
            }]);
        } finally {
            setIsAiLoading(false);
        }
    };
    
    const handleVerifyProofStep = useCallback(async (step: string) => {
        setIsAiLoading(true);
        setError(null);
        setChatHistory(prev => [...prev, { role: 'user', content: step }]);
        try {
            const result = await verifyProofStep(proofCode, step);
            setProofCode(result.new_proof_state);
            const aiMessage: ChatMessage = {
                role: 'model',
                content: result.feedback,
                verification: { verified: result.verified, isComplete: result.is_complete }
            };
            setChatHistory(prev => [...prev, aiMessage]);
        } catch (e: any) {
            setError(e.message || 'Failed to verify proof step.');
            const aiErrorMessage: ChatMessage = { role: 'model', content: "Sorry, I encountered an error trying to verify that step." };
            setChatHistory(prev => [...prev, aiErrorMessage]);
        } finally {
            setIsAiLoading(false);
        }
    }, [proofCode]);

    useEffect(() => {
        if (agentStatus) {
            let initialMessage = "";
            if (agentStatus === 'SOLVED') {
                initialMessage = "I've analyzed this homework and have a solution path. Let's begin by outlining a plan.";
            } else if (agentStatus === 'FAILED') {
                initialMessage = "I tried solving this myself and ran into some trouble, but I did identify some key concepts we'll need. Let's look at this together, starting with the basics.";
            } else {
                initialMessage = `I've analyzed the syllabus for "${className}". What would you like to discuss first?`;
            }
            setChatHistory([{ role: 'model', content: initialMessage }]);
        }
    }, [agentStatus, className]);

    // Render different views based on currentView
    const renderCurrentView = () => {
        switch (currentView) {
            case 'chat':
                return (
                    <TutorPage
                        nodes={nodes}
                        edges={edges}
                        knowledgeState={knowledgeState}
                        handlePartialKnowledgeStateChange={handlePartialKnowledgeStateChange}
                        proofCode={proofCode}
                        chatHistory={chatHistory}
                        isAiLoading={isAiLoading}
                        chatMode={chatMode}
                        handleSendMessage={handleSendMessage}
                        handleVerifyProofStep={handleVerifyProofStep}
                        handleContextualQuery={handleContextualQuery}
                        handleFinishExam={handleFinishExam}
                        currentView={currentView}
                        setCurrentView={setCurrentView}
                        chatInput={chatInput}
                        onChatInputChange={setChatInput}
                    />
                );
            case 'graph':
                return (
                    <div className="flex flex-col h-full max-w-6xl mx-auto">
                        <div className="flex items-center justify-between p-6 border-b border-slate-700">
                            <div>
                                <h1 className="text-2xl font-bold text-blue-400">Knowledge Graph</h1>
                                <p className="text-slate-400 mt-1">Visual representation of concept relationships</p>
                            </div>
                            <button
                                onClick={() => setCurrentView('chat')}
                                className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
                            >
                                Back to Chat
                            </button>
                        </div>
                        <div className="flex-1 min-h-0">
                            <KnowledgeGraph
                                nodes={nodes}
                                edges={edges}
                                knowledgeState={knowledgeState}
                            />
                        </div>
                    </div>
                );
            case 'mastery':
                return (
                    <div className="flex flex-col h-full max-w-4xl mx-auto">
                        <div className="flex items-center justify-between p-6 border-b border-slate-700">
                            <div>
                                <h1 className="text-2xl font-bold text-blue-400">Mastery Panel</h1>
                                <p className="text-slate-400 mt-1">Track and adjust your knowledge state</p>
                            </div>
                            <button
                                onClick={() => setCurrentView('chat')}
                                className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
                            >
                                Back to Chat
                            </button>
                        </div>
                        <div className="flex-1 overflow-y-auto p-6">
                            <StudentMasteryPanel
                                nodes={nodes}
                                knowledgeState={knowledgeState}
                                onKnowledgeStateChange={handlePartialKnowledgeStateChange}
                            />
                        </div>
                    </div>
                );
            case 'progress':
                return (
                    <div className="flex flex-col h-full max-w-4xl mx-auto">
                        <div className="flex items-center justify-between p-6 border-b border-slate-700">
                            <div>
                                <h1 className="text-2xl font-bold text-blue-400">Progress Dashboard</h1>
                                <p className="text-slate-400 mt-1">Your learning progress and achievements</p>
                            </div>
                            <button
                                onClick={() => setCurrentView('chat')}
                                className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
                            >
                                Back to Chat
                            </button>
                        </div>
                        <div className="flex-1 overflow-y-auto p-6">
                            <div className="bg-slate-800 p-6 rounded-lg shadow-lg">
                                <h2 className="text-xl font-semibold text-cyan-400 mb-4">Session Progress</h2>
                                <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
                                    <div className="bg-slate-700 p-4 rounded-lg">
                                        <h3 className="text-lg font-medium text-slate-200 mb-2">Concepts Covered</h3>
                                        <p className="text-3xl font-bold text-blue-400">{nodes.length}</p>
                                        <p className="text-sm text-slate-400">Total concepts in session</p>
                                    </div>
                                    <div className="bg-slate-700 p-4 rounded-lg">
                                        <h3 className="text-lg font-medium text-slate-200 mb-2">Messages Exchanged</h3>
                                        <p className="text-3xl font-bold text-green-400">{chatHistory.length}</p>
                                        <p className="text-sm text-slate-400">Total interactions</p>
                                    </div>
                                    <div className="bg-slate-700 p-4 rounded-lg">
                                        <h3 className="text-lg font-medium text-slate-200 mb-2">Average Mastery</h3>
                                        <p className="text-3xl font-bold text-yellow-400">
                                            {nodes.length > 0 
                                                ? Math.round((Object.values(knowledgeState).reduce((sum, state) => sum + state.mu, 0) / nodes.length) * 100)
                                                : 0}%
                                        </p>
                                        <p className="text-sm text-slate-400">Across all concepts</p>
                                    </div>
                                    <div className="bg-slate-700 p-4 rounded-lg">
                                        <h3 className="text-lg font-medium text-slate-200 mb-2">Session Duration</h3>
                                        <p className="text-3xl font-bold text-purple-400">
                                            {sessionStarted ? 'Active' : 'Not Started'}
                                        </p>
                                        <p className="text-sm text-slate-400">Current session status</p>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                );
            case 'proof':
                return (
                    <div className="flex flex-col h-full max-w-4xl mx-auto">
                        <div className="flex items-center justify-between p-6 border-b border-slate-700">
                            <div>
                                <h1 className="text-2xl font-bold text-blue-400">Proof State</h1>
                                <p className="text-slate-400 mt-1">Current Lean proof code and verification status</p>
                            </div>
                            <button
                                onClick={() => setCurrentView('chat')}
                                className="px-4 py-2 rounded-lg bg-slate-700 hover:bg-slate-600 transition-colors"
                            >
                                Back to Chat
                            </button>
                        </div>
                        <div className="flex-1 overflow-y-auto p-6">
                            <div className="bg-slate-800 p-6 rounded-lg shadow-lg">
                                <h2 className="text-xl font-semibold text-cyan-400 mb-4">Current Proof Code</h2>
                                <div className="bg-slate-900 p-4 rounded-lg border border-slate-600">
                                    <pre className="text-sm text-slate-200 font-mono whitespace-pre-wrap overflow-x-auto">
                                        {proofCode || "No proof code available"}
                                    </pre>
                                </div>
                                <div className="mt-4">
                                    <h3 className="text-lg font-medium text-slate-200 mb-2">Verification Status</h3>
                                    <div className="flex items-center gap-2">
                                        <div className={`w-3 h-3 rounded-full ${proofCode ? 'bg-yellow-400' : 'bg-gray-400'}`}></div>
                                        <span className="text-slate-300">
                                            {proofCode ? 'Proof in progress' : 'No proof started'}
                                        </span>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                );
            default:
                return (
                    <TutorPage
                        nodes={nodes}
                        edges={edges}
                        knowledgeState={knowledgeState}
                        handlePartialKnowledgeStateChange={handlePartialKnowledgeStateChange}
                        proofCode={proofCode}
                        chatHistory={chatHistory}
                        isAiLoading={isAiLoading}
                        chatMode={chatMode}
                        handleSendMessage={handleSendMessage}
                        handleVerifyProofStep={handleVerifyProofStep}
                        handleContextualQuery={handleContextualQuery}
                        handleFinishExam={handleFinishExam}
                        currentView={currentView}
                        setCurrentView={setCurrentView}
                        chatInput={chatInput}
                        onChatInputChange={setChatInput}
                    />
                );
        }
    };

    return (
        <div className="h-full flex flex-col p-4 sm:p-6 lg:p-8 gap-8 bg-gray-900 text-slate-200">
            <header className="text-center shrink-0">
                <h1 className="text-3xl sm:text-4xl lg:text-5xl font-bold text-blue-400">Altera Labs Cognitive Partner</h1>
            </header>
            <main className="flex-grow overflow-hidden">
                <Routes>
                    <Route 
                        path="/" 
                        element={
                            <SetupPage 
                                className={className}
                                setClassName={setClassName}
                                onCreateClass={handleCreateClass}
                                isLoading={isCreatingClass}
                                error={error}
                            />
                        } 
                    />
                    <Route 
                        path="/tutor" 
                        element={renderCurrentView()}
                    />
                </Routes>
            </main>
        </div>
    );
};

export default App;
