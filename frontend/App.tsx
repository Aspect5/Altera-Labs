// frontend/App.tsx

import React, { useState, useCallback } from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from './types';

import { addClassFromSyllabus, getConceptExplanation, finalizeExam, verifyProofStep } from './services/aiService';
import SyllabusInput from './components/SyllabusInput';
import KnowledgeGraph from './components/KnowledgeGraph';
import StudentMasteryPanel from './components/StudentMasteryPanel';
import ViewModeSwitcher from './components/ViewModeSwitcher';
import DeveloperView from './components/DeveloperView';
import ChatMentor from './components/ChatMentor';
import ExamResults from './components/ExamResults';

type AppView = 'graph' | 'developer' | 'exam_results';

const App: React.FC = () => {
    const [className, setClassName] = useState<string>("");
    const [nodes, setNodes] = useState<GraphNode[]>([]);
    const [edges, setEdges] = useState<Edge[]>([]);
    const [knowledgeState, setKnowledgeState] = useState<KnowledgeState>({});
    const [isLoadingSyllabus, setIsLoadingSyllabus] = useState<boolean>(false);
    const [isAiLoading, setIsAiLoading] = useState<boolean>(false);
    const [error, setError] = useState<string | null>(null);
    const [currentView, setCurrentView] = useState<AppView>('graph');
    const [chatHistory, setChatHistory] = useState<ChatMessage[]>([]);
    // --- FIXED: Removed unused activePracticeNodeId state ---
    const [finalKnowledgeState, setFinalKnowledgeState] = useState<KnowledgeState | null>(null);

    // --- State for Socratic Verifier ---
    const [proofCode, setProofCode] = useState<string>("example (a b : ℝ) : a * b = b * a := by\n  sorry");

    // --- FIXED: Removed unused adjacencyInfo memo ---

    const handleProcessSyllabus = useCallback(async (syllabusFile: File) => {
        setIsLoadingSyllabus(true);
        setError(null);
        try {
            const { concepts: newNodes } = await addClassFromSyllabus(className, syllabusFile);
            setNodes(newNodes);

            const dummyEdges: Edge[] = [];
            if (newNodes.length > 1) {
                for (let i = 0; i < newNodes.length - 1; i++) {
                    dummyEdges.push({
                        id: `${newNodes[i].id}->${newNodes[i+1].id}`,
                        source: newNodes[i].id,
                        target: newNodes[i+1].id,
                        label: 'is_related_to',
                    });
                }
            }
            setEdges(dummyEdges);

            const initialKnowledge: KnowledgeState = newNodes.reduce((acc, node) => {
                acc[node.id] = { mu: 0, sigma: 0.5 };
                return acc;
            }, {} as KnowledgeState);
            setKnowledgeState(initialKnowledge);
            setChatHistory([{ role: 'model', content: `Hello! I've analyzed the syllabus for "${className}". What would you like to discuss?` }]);

        } catch (e: any) {
            setError(e.message || 'Failed to process syllabus.');
        } finally {
            setIsLoadingSyllabus(false);
        }
    }, [className]);

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
            const result = await finalizeExam(knowledgeState);
            setFinalKnowledgeState(result.finalKnowledgeState);
            setCurrentView('exam_results');
        } catch (e: any) {
            setError(e.message || 'Failed to finalize the exam session.');
        } finally {
            setIsAiLoading(false);
        }
    };
    
    const handleStartPersonalizedPractice = (practiceNodeIds: string[]) => {
        console.log("Starting personalized practice for nodes:", practiceNodeIds);
        setCurrentView('graph'); 
    };

    const handleVerifyProofStep = useCallback(async (step: string) => {
        setIsAiLoading(true);
        setError(null);
        
        setChatHistory(prev => {
            const lastMessage = prev[prev.length - 1];
            if (lastMessage?.role === 'user' && lastMessage?.content === step) {
                return prev;
            }
            return [...prev, { role: 'user', content: step }];
        });

        try {
            const result = await verifyProofStep(proofCode, step);
            setProofCode(result.new_proof_state);
            
            const aiMessage: ChatMessage = {
                role: 'model',
                content: result.feedback,
                verification: {
                    verified: result.verified,
                    isComplete: result.is_complete
                }
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


    const renderContent = () => {
        if (currentView === 'exam_results' && finalKnowledgeState) {
            return (
                <ExamResults
                    nodes={nodes}
                    finalKnowledgeState={finalKnowledgeState}
                    onStartPersonalizedPractice={handleStartPersonalizedPractice}
                    onReturnToDashboard={() => setCurrentView('graph')}
                />
            );
        }

        // If no syllabus is loaded yet, show a placeholder in the main panel.
        if (nodes.length === 0) {
            return (
                <div className="flex h-full items-center justify-center rounded-lg bg-slate-800/50 p-4 text-center shadow-inner">
                    <div>
                        <h3 className="text-xl font-semibold text-cyan-400">Welcome to Altera Labs</h3>
                        <p className="mt-2 text-slate-400">To begin your session, please create a class using the panel on the left.</p>
                    </div>
                </div>
            );
        }
        
        // This is the main view after the syllabus has been loaded.
        return (
            <div className="flex h-full flex-col gap-6 overflow-y-auto">
                <div className="flex items-center gap-4">
                    <h2 className="text-xl font-semibold text-blue-400">AI Mentor Session</h2>
                    <ViewModeSwitcher viewMode={currentView} setViewMode={setCurrentView} />
                    <button 
                        onClick={handleFinishExam} 
                        className="ml-auto rounded-md bg-red-600 px-4 py-2 font-bold text-white transition-colors hover:bg-red-500"
                    >
                        Finish Exam (Simulate)
                    </button>
                </div>

                {currentView === 'graph' ? (
                    <div className="grid h-full grid-cols-1 gap-6 lg:grid-cols-2">
                        <div className="col-span-2 flex flex-col rounded-lg bg-slate-800/50 p-4 shadow-inner lg:col-span-1">
                                <div className="min-h-0 flex-1">
                                    <h3 className="mb-2 text-lg font-semibold text-cyan-400">Knowledge Graph</h3>
                                    <KnowledgeGraph nodes={nodes} edges={edges} knowledgeState={knowledgeState} />
                                </div>
                                <div className="mt-4">
                                    <h3 className="mb-2 mt-4 text-lg font-semibold text-cyan-400">Proof State</h3>
                                    <pre className="overflow-x-auto whitespace-pre-wrap rounded-md bg-gray-900 p-4 text-sm text-white">
                                        <code>{proofCode}</code>
                                    </pre>
                                </div>
                        </div>
                        <div className="col-span-2 flex flex-col lg:col-span-1">
                            <ChatMentor
                                history={chatHistory}
                                isLoading={isAiLoading}
                                onVerifyStep={handleVerifyProofStep}
                                onContextualQuery={handleContextualQuery}
                            />
                        </div>
                    </div>
                ) : (
                    <DeveloperView
                        nodes={nodes}
                        edges={edges}
                        knowledgeState={knowledgeState}
                        diagnosticTrace={[]}
                        onApplyPropagation={setKnowledgeState}
                    />
                )}
            </div>
        );
    };

    return (
        <div className="h-full flex flex-col p-4 sm:p-6 lg:p-8 gap-8 bg-gray-900 text-slate-200">
            <header className="text-center shrink-0">
                <h1 className="text-3xl sm:text-4xl lg:text-5xl font-bold text-blue-400">Altera Labs Cognitive Partner</h1>
            </header>

            <main className="grid grid-cols-1 lg:grid-cols-12 gap-6 lg:gap-8 flex-grow overflow-hidden">
                <div className="lg:col-span-4 flex flex-col gap-6 overflow-y-auto pr-2">
                    <SyllabusInput
                        className={className}
                        setClassName={setClassName}
                        onProcessSyllabus={handleProcessSyllabus}
                        isLoading={isLoadingSyllabus}
                    />
                    {nodes.length > 0 && (
                        <StudentMasteryPanel
                            nodes={nodes}
                            knowledgeState={knowledgeState}
                            onKnowledgeStateChange={handlePartialKnowledgeStateChange}
                        />
                    )}
                </div>

                <div className="lg:col-span-8 space-y-6 flex flex-col overflow-hidden">
                    {error && (
                        <div className="bg-red-900/50 border border-red-700 text-red-300 p-4 rounded-lg">
                            <p className="font-bold">An Error Occurred</p>
                            <p>{error}</p>
                        </div>
                    )}
                    {renderContent()}
                </div>
            </main>
        </div>
    );
};

export default App;
