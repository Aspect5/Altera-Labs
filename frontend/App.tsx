import React, { useState, useCallback, useMemo } from 'react';
import { GraphNode, Edge, KnowledgeState, ChatMessage } from './types';

// --- SERVICE IMPORTS: This is the key change ---
// We now import our new service that communicates with the refactored Flask backend.
import { addClassFromSyllabus } from './services/aiService'; 
import { buildAdjacencyInfo, calculatePriors, performBayesianUpdate } from './services/bayesianService';

// --- COMPONENT IMPORTS: No change needed here ---
import SyllabusInput from './components/SyllabusInput';
import KnowledgeGraph from './components/KnowledgeGraph';
import StudentMasteryPanel from './components/StudentMasteryPanel';
import ViewModeSwitcher from './components/ViewModeSwitcher';
import DeveloperView from './components/DeveloperView';
import ChatMentor from './components/ChatMentor';
// We no longer need INITIAL_SYLLABUS from constants.

type ViewMode = 'graph' | 'developer';

const App: React.FC = () => {
    // --- STATE MANAGEMENT: Remove syllabusText, add className ---
    const [className, setClassName] = useState<string>(""); // Start with an empty class name
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
    
    // --- SYLLABUS PROCESSING: Updated to handle a file and use the new service ---
    const handleProcessSyllabus = useCallback(async (syllabusFile: File) => {
        setIsLoadingSyllabus(true);
        setError(null);
        setNodes([]);
        setEdges([]);
        setKnowledgeState({});
        setChatHistory([]);

        try {
            // Call the new service function which hits our '/api/add_class' endpoint.
            // It now sends the class name and the syllabus file.
            const { concepts: newNodes } = await addClassFromSyllabus(className, syllabusFile);
            
            setNodes(newNodes);

            // --- DUMMY EDGE GENERATION (for visualization until backend provides it) ---
            const dummyEdges: Edge[] = [];
            if (newNodes.length > 1) {
                for (let i = 0; i < newNodes.length - 1; i++) {
                    dummyEdges.push({
                        id: `e${i}`,
                        source: newNodes[i].id,
                        target: newNodes[i+1].id,
                        label: 'prerequisite'
                    });
                }
            }
            setEdges(dummyEdges);

            const initialKnowledge: KnowledgeState = newNodes.reduce((acc, node) => {
                acc[node.id] = { mu: 0, sigma: 0.5 };
                return acc;
            }, {} as KnowledgeState);
            setKnowledgeState(initialKnowledge);
            setChatHistory([{ role: 'model', content: `Hello! I've analyzed the syllabus for "${className}". This knowledge graph represents the core concepts. What would you like to discuss first?` }]);

        } catch (e: any) {
            console.error(e);
            setError(e.message || 'Failed to process syllabus. Please check the backend server and try again.');
        } finally {
            setIsLoadingSyllabus(false);
        }
    }, [className]); // Now depends on `className` state.
    
    // --- No changes needed to the other handler functions yet ---
    const handlePartialKnowledgeStateChange = (nodeId: string, value: Partial<{mu: number, sigma: number}>) => {
        setKnowledgeState(prev => ({ ...prev, [nodeId]: { ...prev[nodeId], ...value } }));
    };

    // ... (handleSendMessage, handleStartPractice, handlePracticeAnswer can remain as they are for now) ...
    const handleSendMessage = () => {};
    const handleStartPractice = () => {};
    const handlePracticeAnswer = () => {};


    return (
        <div className="h-full flex flex-col p-4 sm:p-6 lg:p-8 gap-8 bg-gray-900 text-slate-200">
            <header className="text-center shrink-0">
                <h1 className="text-3xl sm:text-4xl lg:text-5xl font-bold text-blue-400">Altera Labs Cognitive Partner</h1>
                <p className="text-slate-400 mt-2 max-w-4xl mx-auto">
                    Enter a class name and upload your syllabus to generate an interactive course knowledge graph.
                </p>
            </header>

            <main className="grid grid-cols-1 lg:grid-cols-12 gap-6 lg:gap-8 flex-grow overflow-hidden">
                <div className="lg:col-span-4 flex flex-col gap-6 overflow-y-auto pr-2">
                    {/* Pass the new props to the updated SyllabusInput component */}
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
                    {/* No changes needed to the rendering logic below. It will now work with the new flow. */}
                    {isLoadingSyllabus && (
                        <div className="flex justify-center items-center h-full bg-slate-800/50 rounded-lg p-8 flex-grow">
                            <div className="text-center">
                                <div className="w-16 h-16 border-4 border-dashed rounded-full animate-spin border-blue-400 mx-auto"></div>
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
                                <p className="text-lg">Enter a class name and upload a syllabus to begin.</p>
                            </div>
                        </div>
                    )}

                    {!isLoadingSyllabus && nodes.length > 0 && (
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
