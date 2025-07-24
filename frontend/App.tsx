import React, { useState, useCallback, useMemo } from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from './types';

import { addClassFromSyllabus, getConceptExplanation } from './services/aiService'; 
import { buildAdjacencyInfo, performBayesianUpdate, calculatePriors } from './services/bayesianService';

import SyllabusInput from './components/SyllabusInput';
import KnowledgeGraph from './components/KnowledgeGraph';
import StudentMasteryPanel from './components/StudentMasteryPanel';
import ViewModeSwitcher from './components/ViewModeSwitcher';
import DeveloperView from './components/DeveloperView';
import ChatMentor from './components/ChatMentor';

type ViewMode = 'graph' | 'developer';

const App: React.FC = () => {
    const [className, setClassName] = useState<string>("");
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
                        source: newNodes[i].id,
                        target: newNodes[i+1].id,
                        weight: 0.8,
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

    const handleSendMessage = (message: string) => {
        setChatHistory(prev => [...prev, { role: 'user', content: message }]);
        setIsAiLoading(true);
        setTimeout(() => {
            setChatHistory(prev => [...prev, { role: 'model', content: "This is a placeholder response while the session view is in development." }]);
            setIsAiLoading(false);
        }, 1000);
    };

    const handleStartPractice = (nodeId: string) => {
        setActivePracticeNodeId(nodeId);
        const node = nodes.find(n => n.id === nodeId)!;
        setChatHistory(prev => [
            ...prev,
            { role: 'system', content: `Let's practice "${node.label}". Once you've thought about the problem, select whether you think you answered correctly or incorrectly.`, practiceNodeId: nodeId }
        ]);
    };

    const handlePracticeAnswer = useCallback((targetNodeId: string, isCorrect: boolean) => {
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

        const systemMessage = `[PRACTICE OUTCOME] Student answered question for "${node.label}" ${isCorrect ? 'correctly' : 'incorrectly'}. Their knowledge state has been updated.`;
        
        setChatHistory(prev => [...prev, { role: 'system', content: systemMessage }]);
    }, [knowledgeState, adjacencyInfo, nodes]);

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
                    {/* FIXED: Add rendering for the error state */}
                    {error && (
                        <div className="bg-red-900/50 border border-red-700 text-red-300 p-4 rounded-lg">
                           <p className="font-bold">An Error Occurred</p>
                           <p>{error}</p>
                        </div>
                    )}
                    
                    {!isLoadingSyllabus && nodes.length > 0 && !error && (
                        <div className="flex flex-col gap-6 h-full overflow-y-auto">
                           <div className="flex items-center gap-4">
                               <h2 className="text-xl font-semibold text-blue-400">AI Mentor Session</h2>
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
                    )}
                </div>
            </main>
        </div>
    );
};

export default App;
