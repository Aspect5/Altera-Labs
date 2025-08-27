// frontend/App.tsx

import React, { useState, useCallback, useEffect } from 'react';
import { Routes, Route, useNavigate } from 'react-router-dom';
import { GraphNode, Edge, KnowledgeState, ChatMessage, ClassSummary, QuickStats, ClassData, GamificationState } from './types/components';

// API services
import { 
    createClass, 
    getConceptExplanation, 
    finalizeExam, 
    verifyProofStep, 
    startSession, 
    sendMessage, 
    dashboardService, 
    gamificationService,
    autoSolveProof,
    toggleDeveloperMode,
    getDeveloperLogs
} from './services';

// Page Components
import SetupPage from './src/pages/SetupPage';
import TutorPage from './src/pages/TutorPage';
import DashboardPage from './src/pages/DashboardPage';

// View Components
import { KnowledgeGraph, StudentMasteryPanel } from './components';
import { DeveloperPanel } from './components/developer/DeveloperPanel';
import ViewModeSwitcher from './components/common/ViewModeSwitcher';

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
    // const [finalKnowledgeState, setFinalKnowledgeState] = useState<KnowledgeState | null>(null);
    const [sessionStarted, setSessionStarted] = useState<boolean>(false);
    const [chatMode, setChatMode] = useState<'chat' | 'verify'>('chat');
    const [proofCode, setProofCode] = useState<string>("");
    const [isCreatingClass, setIsCreatingClass] = useState<boolean>(false);
    const [agentStatus, setAgentStatus] = useState<'SOLVED' | 'FAILED' | 'SYLLABUS_BASED' | null>(null);
    
    // Add input state management
    const [chatInput, setChatInput] = useState<string>("");

    // Dashboard state
    const [classes, setClasses] = useState<ClassSummary[]>([]);
    const [currentClassId, setCurrentClassId] = useState<string | null>(null);
    const [showDashboard, setShowDashboard] = useState<boolean>(true);
    const [isLoadingDashboard, setIsLoadingDashboard] = useState<boolean>(false);
    const [dashboardError, setDashboardError] = useState<string | null>(null);

    // Gamification state
    const [gamificationState, setGamificationState] = useState<GamificationState>(gamificationService.getState());
    const [affectiveState, setAffectiveState] = useState<'NEUTRAL' | 'FRUSTRATED' | 'CONFIDENT' | 'CONFUSED' | 'EXCITED'>('NEUTRAL');
    const [confidence, setConfidence] = useState<number>(0.5);

    // Developer mode state
    const [developerMode, setDeveloperMode] = useState<boolean>(false);
    const [showDeveloperPanel, setShowDeveloperPanel] = useState<boolean>(false);
    // const [autoSolveAttempts, setAutoSolveAttempts] = useState<any[]>([]);
    // const [solutionFound, setSolutionFound] = useState<boolean>(false);
    // const [maxAttempts, setMaxAttempts] = useState<number>(5);

    // Session state management
    const [sessionId, setSessionId] = useState<string | null>(null);
    const [sessionMode, setSessionMode] = useState<'homework' | 'exam' | null>(null);
    const [rehydrationAttempted, setRehydrationAttempted] = useState<boolean>(false);

    // Gamification trigger functions
    const awardPoints = useCallback((action: string, amount: number) => {
        const newAchievements = gamificationService.addPoints(amount, action);
        setGamificationState(gamificationService.getState());
        return newAchievements;
    }, []);

    const updateAffectiveState = useCallback((aiResponse: string) => {
        // Simple sentiment analysis based on AI response content
        const response = aiResponse.toLowerCase();
        let newAffectiveState: 'NEUTRAL' | 'FRUSTRATED' | 'CONFIDENT' | 'CONFUSED' | 'EXCITED' = 'NEUTRAL';
        
        if (response.includes('great') || response.includes('excellent') || response.includes('correct') || 
            response.includes('well done') || response.includes('good job') || response.includes('perfect')) {
            newAffectiveState = 'CONFIDENT';
        } else if (response.includes('wrong') || response.includes('incorrect') || response.includes('error') ||
                   response.includes('try again') || response.includes('not quite')) {
            newAffectiveState = 'FRUSTRATED';
        } else if (response.includes('confused') || response.includes('unclear') || response.includes('not sure')) {
            newAffectiveState = 'CONFUSED';
        } else if (response.includes('amazing') || response.includes('wow') || response.includes('incredible')) {
            newAffectiveState = 'EXCITED';
        }
        
        setAffectiveState(newAffectiveState);
    }, []);

    // const checkConceptMastery = useCallback(() => {
    //     // Check if any concepts have high mastery (mu >= 0.9)
    //     const masteredConcepts = Object.values(knowledgeState).filter(state => state.mu >= 0.9).length;
    //     if (masteredConcepts > 0) {
    //         const newAchievements = gamificationService.conceptMastered();
    //         setGamificationState(gamificationService.getState());
    //         return newAchievements;
    //     }
    //     return [];
    // }, [knowledgeState]);

    // Developer mode functions
    const handleAutoSolve = useCallback(async (proofState: string, maxAttempts?: number) => {
        try {
            const result = await autoSolveProof(proofState, maxAttempts);
            // setAutoSolveAttempts(result.attempts || []);
            // setSolutionFound(result.solved);
            return result;
        } catch (error) {
            console.error('Auto-solve failed:', error);
            throw error;
        }
    }, []);

    const handleToggleDeveloperMode = useCallback(async (enabled: boolean, maxAttempts?: number) => {
        try {
            const result = await toggleDeveloperMode(enabled, maxAttempts);
            setDeveloperMode(result.developer_mode);
            // if (maxAttempts) setMaxAttempts(maxAttempts);
        } catch (error) {
            console.error('Failed to toggle developer mode:', error);
            throw error;
        }
    }, []);

    const handleGetDeveloperLogs = useCallback(async () => {
        try {
            return await getDeveloperLogs();
        } catch (error) {
            console.error('Failed to get developer logs:', error);
            throw error;
        }
    }, []);

    // Auto-refresh developer logs when panel is open
    // REMOVED: Unnecessary polling that was causing conflicts with DeveloperPanel's internal polling
    // The DeveloperPanel handles its own polling when needed (during auto-solve operations)

    // Session state management functions
    const saveSessionState = useCallback(() => {
        const sessionState = {
            sessionId,
            sessionMode,
            currentClassId,
            chatHistory,
            knowledgeState,
            proofCode,
            chatMode,
            gamificationState,
            affectiveState,
            confidence
        };
        localStorage.setItem('sessionState', JSON.stringify(sessionState));
    }, [sessionId, sessionMode, currentClassId, chatHistory, knowledgeState, proofCode, chatMode, gamificationState, affectiveState, confidence]);

    const loadSessionState = useCallback(() => {
        const saved = localStorage.getItem('sessionState');
        if (saved) {
            try {
                const sessionState = JSON.parse(saved);
                setSessionId(sessionState.sessionId);
                setSessionMode(sessionState.sessionMode);
                setCurrentClassId(sessionState.currentClassId);
                setChatHistory(sessionState.chatHistory || []);
                setKnowledgeState(sessionState.knowledgeState || {});
                setProofCode(sessionState.proofCode || '');
                setChatMode(sessionState.chatMode || 'chat');
                setGamificationState(sessionState.gamificationState || gamificationService.getState());
                setAffectiveState(sessionState.affectiveState || 'NEUTRAL');
                setConfidence(sessionState.confidence || 0.5);
                return true;
            } catch (error) {
                console.error('Failed to load session state:', error);
                return false;
            }
        }
        return false;
    }, []);

    const clearSessionState = useCallback(() => {
        localStorage.removeItem('sessionState');
        setSessionId(null);
        setSessionMode(null);
        setChatHistory([]);
        setProofCode('');
        setChatMode('chat');
        setSessionStarted(false);
    }, []);

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
        
        // Award points for chat interaction
        const newAchievements = awardPoints('chat_interaction', 5);
        
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
            
            // Update affective state based on AI response
            updateAffectiveState(response.aiResponse);
            
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
    }, [chatMode, awardPoints, updateAffectiveState]);

    // Load session state on app startup
    useEffect(() => {
        const hasSession = loadSessionState();
        if (hasSession && sessionId) {
            setSessionStarted(true);
        }
    }, [loadSessionState]);

    // Rehydrate class data if user refreshes or lands directly on /tutor (attempt once)
    useEffect(() => {
        if (window.location.pathname !== '/tutor' || rehydrationAttempted) return;
        setRehydrationAttempted(true);
        const saved = localStorage.getItem('sessionState');
        let savedClassId: string | null = null;
        if (saved) {
            try {
                const parsed = JSON.parse(saved);
                savedClassId = parsed.currentClassId || null;
            } catch {}
        }
        const classIdToLoad = savedClassId || currentClassId;
        if (classIdToLoad) {
            (async () => {
                try {
                    const classData = await dashboardService.getClassData(classIdToLoad as string);
                    setNodes(classData.nodes);
                    setEdges(classData.edges);
                    setKnowledgeState(classData.knowledgeState);
                } catch (e: any) {
                    console.error('Failed to rehydrate class data:', e);
                    setError(e.message || 'Failed to load class data. Returning to dashboard.');
                    navigate('/dashboard');
                }
            })();
        } else {
            navigate('/dashboard');
        }
    }, [rehydrationAttempted, currentClassId, navigate]);

    // Save session state when it changes
    useEffect(() => {
        if (sessionId) {
            saveSessionState();
        }
    }, [sessionId, saveSessionState]);

    useEffect(() => {
        if (nodes && nodes.length > 0 && !sessionStarted) {
            initializeTutoringSession();
        }
    }, [nodes, sessionStarted, initializeTutoringSession]);

    // Ensure session starts on Tutor route even if nodes are empty
    useEffect(() => {
        if (!sessionStarted && window.location.pathname === '/tutor') {
            initializeTutoringSession();
        }
    }, [sessionStarted, initializeTutoringSession]);

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
            
            // Create class summary for dashboard
            const classId = `class_${Date.now()}`;
            const classData: ClassData = {
                id: classId,
                name: className,
                healthScore: 0,
                knowledgeState: initialKnowledge,
                nodes: newNodes,
                edges: newEdges,
                lastSession: null,
            };
            updateClassSummary(classId, classData);
            setCurrentClassId(classId);
            
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
            // setFinalKnowledgeState(result.finalKnowledgeState);
            
            // Award points for session completion
            // const sessionAchievements = awardPoints('session_completed', 20);
            
            // Save session data to backend if we have a current class
            if (currentClassId) {
                try {
                    await dashboardService.updateSessionData(currentClassId, knowledgeState);
                    console.log('Session data saved to backend');
                } catch (error) {
                    console.error('Failed to save session data:', error);
                }
            }
            
            // Clear session state
            clearSessionState();
            
            // Show success message
            setChatHistory([{ 
                role: 'system', 
                content: `Session ended successfully. Final knowledge state saved.` 
            }]);
            
            // Navigate back to dashboard
            handleBackToDashboard();
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

    // Dashboard functions
    const calculateClassHealth = useCallback((knowledgeState: KnowledgeState, nodes: GraphNode[]): number => {
        if (!nodes || nodes.length === 0) return 0;
        const totalMu = Object.values(knowledgeState).reduce((sum, state) => sum + state.mu, 0);
        return Math.round((totalMu / nodes.length) * 100);
    }, []);

    const calculatePlantState = useCallback((healthScore: number): ClassSummary['plantState'] => {
        if (healthScore >= 80) return 'flourishing';
        if (healthScore >= 60) return 'healthy';
        if (healthScore >= 40) return 'wilting';
        return 'struggling';
    }, []);

    const updateClassSummary = useCallback((classId: string, classData: ClassData) => {
        const healthScore = calculateClassHealth(classData.knowledgeState, classData.nodes);
        const conceptsMastered = Object.values(classData.knowledgeState).filter(state => state.mu >= 0.7).length;
        
        const classSummary: ClassSummary = {
            id: classId,
            name: classData.name,
            healthScore,
            conceptsMastered,
            totalConcepts: classData.nodes.length,
            lastSession: classData.lastSession,
            plantState: calculatePlantState(healthScore),
            createdAt: new Date(),
            updatedAt: new Date(),
        };

        setClasses(prev => {
            const existing = prev.find(c => c.id === classId);
            if (existing) {
                return prev.map(c => c.id === classId ? { ...classSummary, createdAt: existing.createdAt } : c);
            }
            return [...prev, classSummary];
        });
    }, [calculateClassHealth, calculatePlantState]);

    const handleSelectClass = useCallback(async (classId: string) => {
        setCurrentClassId(classId);
        
        try {
            // Load class data from backend
            const classData = await dashboardService.getClassData(classId);
            setNodes(classData.nodes);
            setEdges(classData.edges);
            setKnowledgeState(classData.knowledgeState);
            
            // Start session
            const response = await startSession('homework');
            setSessionId(response.sessionId);
            setSessionMode('homework');
            setProofCode(response.proofCode);
            setChatHistory([{ role: 'model', content: response.aiResponse }]);
            setSessionStarted(true);
            
            navigate('/tutor');
        } catch (error: any) {
            console.error('handleSelectClass: Failed to start session:', error);
            setError(error.message || 'Failed to start session');
        }
    }, [navigate]);

    const handleCreateNewClass = useCallback(() => {
        navigate('/setup');
    }, [navigate]);

    const handleBackToDashboard = useCallback(() => {
        setShowDashboard(true);
        setCurrentClassId(null);
        navigate('/dashboard');
    }, [navigate]);

    // Load dashboard data
    const loadDashboardData = useCallback(async () => {
        setIsLoadingDashboard(true);
        setDashboardError(null);
        try {
            const [classesData, statsData] = await Promise.all([
                dashboardService.getClasses(),
                dashboardService.getStats(),
            ]);
            setClasses(classesData);
            setQuickStats(statsData);
        } catch (error: any) {
            console.error('Error loading dashboard data:', error);
            setDashboardError(error.message || 'Failed to load dashboard data');
        } finally {
            setIsLoadingDashboard(false);
        }
    }, []);

    // Quick stats state
    const [quickStats, setQuickStats] = useState<QuickStats>({
        totalConceptsMastered: 0,
        currentStreak: 0,
        flowStateTime: 0,
        totalClasses: 0,
        averageHealthScore: 0,
    });

    // Load dashboard data on mount
    useEffect(() => {
        if (showDashboard) {
            loadDashboardData();
        }
    }, [showDashboard, loadDashboardData]);

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
                        onInputChange={setChatInput}
                        onBackToDashboard={handleBackToDashboard}
                        affectiveState={affectiveState}
                        confidence={confidence}
                        gamificationState={gamificationState}
                        onAchievementUnlocked={(achievement) => {
                            console.log('Achievement unlocked:', achievement);
                        }}
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
                                        <p className="text-3xl font-bold text-blue-400">{nodes ? nodes.length : 0}</p>
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
                                            {nodes && nodes.length > 0 
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
                        onInputChange={setChatInput}
                        onBackToDashboard={handleBackToDashboard}
                        affectiveState={affectiveState}
                        confidence={confidence}
                        gamificationState={gamificationState}
                        onAchievementUnlocked={(achievement) => {
                            console.log('Achievement unlocked:', achievement);
                        }}
                    />
                );
        }
    };

    return (
        <div className="h-full flex flex-col p-4 sm:p-6 lg:p-8 gap-8 bg-gray-900 text-slate-200">
            <header className="text-center shrink-0 relative">
                <h1 className="text-3xl sm:text-4xl lg:text-5xl font-bold text-blue-400">Altera Labs Cognitive Partner</h1>
                {/* Removed Confidence Level modal */}
                <div className="absolute top-0 right-0 mt-2 mr-2 z-50">
                  <ViewModeSwitcher 
                    viewMode={developerMode ? 'developer' : 'graph'} 
                    setViewMode={mode => {
                      setDeveloperMode(mode === 'developer');
                      setShowDeveloperPanel(mode === 'developer');
                    }}
                  />
                </div>
            </header>
            <main className="flex-grow overflow-hidden">
                <Routes>
                    <Route 
                        path="/" 
                        element={
                            <DashboardPage
                                classes={classes}
                                stats={quickStats}
                                onCreateClass={handleCreateNewClass}
                                onSelectClass={handleSelectClass}
                                isLoading={isLoadingDashboard}
                                error={dashboardError}
                            />
                        } 
                    />
                    <Route 
                        path="/dashboard" 
                        element={
                            <DashboardPage
                                classes={classes}
                                stats={quickStats}
                                onCreateClass={handleCreateNewClass}
                                onSelectClass={handleSelectClass}
                                isLoading={isLoadingDashboard}
                                error={dashboardError}
                            />
                        } 
                    />
                    <Route 
                        path="/setup" 
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

            {/* Developer Panel */}
            {showDeveloperPanel && (
                <DeveloperPanel
                    isVisible={showDeveloperPanel}
                    onClose={() => setShowDeveloperPanel(false)}
                    currentProofState={proofCode}
                    onAutoSolve={handleAutoSolve}
                    onToggleDeveloperMode={handleToggleDeveloperMode}
                    onGetLogs={handleGetDeveloperLogs}
                />
            )}
        </div>
    );
};

export default App;
