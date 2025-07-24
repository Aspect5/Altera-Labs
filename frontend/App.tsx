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

        if (isLoadingSyllabus || nodes.length === 0 || error) {
            return (
                <div className="flex justify-center items-center h-full">
                    <SyllabusInput
                        className={className}
                        setClassName={setClassName}
                        onProcessSyllabus={handleProcessSyllabus}
                        isLoading={isLoadingSyllabus}
                    />
                </div>
            );
        }
        
        return (
            <div className="flex flex-col gap-6 h-full overflow-y-auto">
                <div className="flex items-center gap-4">
                    <h2 className="text-xl font-semibold text-blue-400">AI Mentor Session</h2>
                    <ViewModeSwitcher viewMode={currentView} setViewMode={setCurrentView} />
                    <button 
                        onClick={handleFinishExam} 
                        className="ml-auto bg-red-600 hover:bg-red-500 text-white font-bold py-2 px-4 rounded-md transition-colors"
                    >
                        Finish Exam (Simulate)
                    </button>
                </div>

                {currentView === 'graph' ? (
                    <div className="grid grid-cols-1 lg:grid-cols-2 gap-6 h-full">
                        <div className="bg-slate-800/50 p-4 rounded-lg shadow-inner col-span-2 lg:col-span-1 flex flex-col">
                             <div className="flex-1 min-h-0">
                                <h3 className="text-lg font-semibold text-cyan-400 mb-2">Knowledge Graph</h3>
                                <KnowledgeGraph nodes={nodes} edges={edges} knowledgeState={knowledgeState} />
                             </div>
                             <div className="mt-4">
                                <h3 className="text-lg font-semibold text-cyan-400 mt-4 mb-2">Proof State</h3>
                                <pre className="bg-gray-900 text-white p-4 rounded-md text-sm whitespace-pre-wrap overflow-x-auto">
                                    <code>{proofCode}</code>
                                </pre>
                             </div>
                        </div>
                        <div className="col-span-2 lg:col-span-1 flex flex-col">
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
