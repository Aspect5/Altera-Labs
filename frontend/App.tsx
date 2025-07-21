
import React, { useState, useCallback, useMemo } from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage, Reassessment, PracticeSuggestion } from './types';
import { extractGraphFromSyllabus, getMentorResponse } from './services/geminiService';
import { buildAdjacencyInfo, calculatePriors, performBayesianUpdate } from './services/bayesianService';
import SyllabusInput from './components/SyllabusInput';
import KnowledgeGraph from './components/KnowledgeGraph';
import StudentMasteryPanel from './components/StudentMasteryPanel';
import ViewModeSwitcher from './components/ViewModeSwitcher';
import DeveloperView from './components/DeveloperView';
import ChatMentor from './components/ChatMentor';
import { INITIAL_SYLLABUS } from './constants';

type ViewMode = 'graph' | 'developer';

const App: React.FC = () => {
    const [syllabusText, setSyllabusText] = useState<string>(INITIAL_SYLLABUS);
    const [nodes, setNodes] = useState<GraphNode[]>([]);
    const [edges, setEdges] = useState<Edge[]>([]);
    const [knowledgeState, setKnowledgeState] = useState<KnowledgeState>({});
    const [isLoadingSyllabus, setIsLoadingSyllabus] = useState<boolean>(false);
    const [isAiLoading, setIsAiLoading] = useState<boolean>(false);
    const [error, setError] = useState<string | null>(null);
    const [viewMode, setViewMode] = useState<ViewMode>('graph');
    const [chatHistory, setChatHistory] = useState<ChatMessage[]>([]);
    const [activePracticeNodeId, setActivePracticeNodeId] = useState<string | null>(null);

    const adjacencyInfo = useMemo(() => {
        if (nodes.length > 0) {
            return buildAdjacencyInfo(nodes, edges);
        }
        return null;
    }, [nodes, edges]);
    
    const handleProcessSyllabus = useCallback(async () => {
        setIsLoadingSyllabus(true);
        setError(null);
        setNodes([]);
        setEdges([]);
        setKnowledgeState({});
        setChatHistory([]);

        try {
            const { nodes: newNodes, edges: newEdges } = await extractGraphFromSyllabus(syllabusText);
            setNodes(newNodes);
            setEdges(newEdges);

            const initialKnowledge: KnowledgeState = newNodes.reduce((acc, node) => {
                acc[node.id] = { mu: 0, sigma: 0.5 }; // Initial state: 0 mastery, max uncertainty
                return acc;
            }, {} as KnowledgeState);
            setKnowledgeState(initialKnowledge);
            setChatHistory([{ role: 'model', content: "Hello! I'm your AI mentor. I've just read the syllabus. What concept should we start with?" }]);

        } catch (e) {
            console.error(e);
            setError('Failed to process syllabus. The AI might be having trouble parsing the text. Please try again or adjust the input.');
        } finally {
            setIsLoadingSyllabus(false);
        }
    }, [syllabusText]);
    
    const handlePartialKnowledgeStateChange = (nodeId: string, value: Partial<{mu: number, sigma: number}>) => {
        setKnowledgeState(prev => ({ ...prev, [nodeId]: { ...prev[nodeId], ...value } }));
    };

    const fetchAndProcessAIResponse = useCallback(async (currentHistory: ChatMessage[]) => {
        setIsAiLoading(true);
        try {
            const response = await getMentorResponse(currentHistory, knowledgeState, nodes);
            
            // Handle potential reassessment from the AI
            if (response.reassessment) {
                const { nodeId, newMu, newSigma, reasoning } = response.reassessment;
                setKnowledgeState(prev => ({
                    ...prev,
                    [nodeId]: { mu: Math.max(0, Math.min(1, newMu)), sigma: Math.max(0.01, Math.min(0.5, newSigma)) }
                }));
                 // Add a system message about the reassessment to the history for transparency
                setChatHistory(prev => [...prev, { role: 'system', content: `Knowledge for "${nodes.find(n => n.id === nodeId)?.label}" updated based on conversation. Reason: ${reasoning}` }]);
            }

            const newAiMessage: ChatMessage = { role: 'model', content: response.responseText };
            if (response.practiceSuggestion) {
                newAiMessage.suggestion = {
                    nodeId: response.practiceSuggestion.nodeId,
                    label: nodes.find(n => n.id === response.practiceSuggestion.nodeId)?.label || response.practiceSuggestion.nodeId
                };
            }
            setChatHistory(prev => [...prev, newAiMessage]);

        } catch (e) {
            console.error(e);
            const errorMessage = "I seem to be having trouble connecting. Please try again in a moment.";
            setChatHistory(prev => [...prev, {role: 'model', content: errorMessage}]);
        } finally {
            setIsAiLoading(false);
        }
    }, [knowledgeState, nodes]);

    const handleSendMessage = useCallback(async (message: string) => {
        const newHistory: ChatMessage[] = [...chatHistory, { role: 'user', content: message }];
        setChatHistory(newHistory);
        await fetchAndProcessAIResponse(newHistory);
    }, [chatHistory, fetchAndProcessAIResponse]);
    
    const handleStartPractice = useCallback((nodeId: string) => {
        setActivePracticeNodeId(nodeId);
        const node = nodes.find(n => n.id === nodeId)!;
        setChatHistory(prev => [
            ...prev,
            { role: 'system', content: `Let's practice "${node.label}". Once you've thought about the problem, select whether you think you answered correctly or incorrectly.`, practiceNodeId: nodeId }
        ]);
    }, [nodes]);

    const handlePracticeAnswer = useCallback(async (targetNodeId: string, isCorrect: boolean) => {
        if (!adjacencyInfo) return;
        
        setActivePracticeNodeId(null);

        const node = nodes.find(n => n.id === targetNodeId)!;
        
        const { mu_prior, sigma_prior } = calculatePriors(targetNodeId, knowledgeState, adjacencyInfo);
        const { mu_post, sigma_post } = performBayesianUpdate(mu_prior, sigma_prior, isCorrect);
        
        const newKnowledgeState = {
            ...knowledgeState,
            [targetNodeId]: { mu: mu_post, sigma: Math.min(0.5, sigma_post) }
        };
        setKnowledgeState(newKnowledgeState);

        const systemMessage = `[PRACTICE OUTCOME] Student answered question for "${node.label}" ${isCorrect ? 'correctly' : 'incorrectly'}. Their knowledge state for this concept has been updated to μ=${mu_post.toFixed(2)}, σ=${sigma_post.toFixed(2)}.`;
        
        const newHistory: ChatMessage[] = [...chatHistory, { role: 'system', content: systemMessage }];
        setChatHistory(newHistory);
        await fetchAndProcessAIResponse(newHistory);

    }, [knowledgeState, adjacencyInfo, nodes, chatHistory, fetchAndProcessAIResponse]);

    return (
        <div className="h-full flex flex-col p-4 sm:p-6 lg:p-8 gap-8">
            <header className="text-center shrink-0">
                <h1 className="text-3xl sm:text-4xl lg:text-5xl font-bold text-cyan-400">Conversational Knowledge Tutor</h1>
                <p className="text-slate-400 mt-2 max-w-4xl mx-auto">
                    An interactive simulation of an AI mentor. Process a syllabus, then chat with the AI to learn concepts and test your knowledge.
                </p>
            </header>

            <main className="grid grid-cols-1 lg:grid-cols-12 gap-6 lg:gap-8 flex-grow overflow-hidden">
                <div className="lg:col-span-4 flex flex-col gap-6 overflow-y-auto pr-2">
                    <SyllabusInput 
                        syllabusText={syllabusText} 
                        setSyllabusText={setSyllabusText}
                        onProcess={handleProcessSyllabus}
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
                    {isLoadingSyllabus && (
                        <div className="flex justify-center items-center h-full bg-slate-800/50 rounded-lg p-8 flex-grow">
                            <div className="text-center">
                                <div className="w-16 h-16 border-4 border-dashed rounded-full animate-spin border-cyan-400 mx-auto"></div>
                                <p className="mt-4 text-lg">AI is building the knowledge graph...</p>
                            </div>
                        </div>
                    )}
                     {error && (
                        <div className="bg-red-900/50 border border-red-700 text-red-300 p-4 rounded-lg">
                           <p className="font-bold">Error</p>
                           <p>{error}</p>
                        </div>
                    )}

                    {!isLoadingSyllabus && nodes.length === 0 && !error &&(
                         <div className="flex justify-center items-center h-full bg-slate-800/50 rounded-lg p-8 min-h-[400px] flex-grow">
                            <div className="text-center text-slate-400">
                                <p className="text-lg">Process a syllabus to begin the simulation.</p>
                            </div>
                        </div>
                    )}

                    {!isLoadingSyllabus && nodes.length > 0 && (
                        <div className="flex flex-col gap-6 h-full overflow-y-auto">
                           <div className="flex items-center gap-4">
                               <h2 className="text-xl font-semibold text-cyan-400">AI Mentor Session</h2>
                               <ViewModeSwitcher viewMode={viewMode} setViewMode={setViewMode} />
                           </div>
                           
                            {viewMode === 'graph' ? (
                               <div className="grid grid-rows-2 gap-4 h-full">
                                    <div className="bg-slate-800 p-4 rounded-lg shadow-2xl row-span-1">
                                       <KnowledgeGraph nodes={nodes} edges={edges} knowledgeState={knowledgeState} />
                                    </div>
                                     <div className="row-span-1 flex flex-col">
                                        <ChatMentor 
                                           history={chatHistory} 
                                           isLoading={isAiLoading} 
                                           onSendMessage={handleSendMessage}
                                           onStartPractice={handleStartPractice}
                                           onPracticeAnswer={handlePracticeAnswer}
                                           activePracticeNodeId={activePracticeNodeId}
                                        />
                                     </div>
                               </div>
                            ) : (
                                <DeveloperView 
                                    nodes={nodes}
                                    edges={edges}
                                    knowledgeState={knowledgeState}
                                    diagnosticTrace={chatHistory.filter(m => m.role === 'system').map(m => m.content)}
                                    onApplyPropagation={setKnowledgeState}
                                />
                            )}
                        </div>
                    )}
                </div>
            </main>
        </div>
    );
};

export default App;
