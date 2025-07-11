// App.jsx

import React, { useState, useEffect, useRef } from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { oneDark } from '@codemirror/theme-one-dark';
import { basicSetup } from '@uiw/codemirror-extensions-basic-setup';

// --- NEW: KaTeX for LaTeX Rendering ---
import 'katex/dist/katex.min.css'; // Import KaTeX CSS
import { InlineMath, BlockMath } from 'react-katex';

// --- NEW: LaTeX Renderer Component ---
// This component parses a string for LaTeX delimiters ($...$ and $$...$$)
// and renders the math using KaTeX.
function LatexRenderer({ text }) {
    // Regular expression to split the text by inline and block math delimiters.
    // It captures the delimiters and the content inside them.
    const parts = text.split(/(\$\$[\s\S]*?\$\$|\$[\s\S]*?\$)/g);

    return (
        <div className="text-white whitespace-pre-wrap">
            {parts.map((part, index) => {
                if (part.startsWith('$$') && part.endsWith('$$')) {
                    // It's a block-level equation. Render with BlockMath.
                    // Slice(2, -2) removes the '$$' delimiters.
                    return <BlockMath key={index} math={part.slice(2, -2)} />;
                } else if (part.startsWith('$') && part.endsWith('$')) {
                    // It's an inline equation. Render with InlineMath.
                    // Slice(1, -1) removes the '$' delimiters.
                    return <InlineMath key={index} math={part.slice(1, -1)} />;
                }
                // It's a plain text part.
                return <span key={index}>{part}</span>;
            })}
        </div>
    );
}


// --- Main App Component ---
export default function App() {
    const [route, setRoute] = useState('dashboard');
    const [classes, setClasses] = useState([]); 
    
    // Session-specific state
    const [sessionId, setSessionId] = useState(null);
    const [proofCode, setProofCode] = useState('');
    const [chatHistory, setChatHistory] = useState([]);
    const [isLoading, setIsLoading] = useState(false);
    const [error, setError] = useState('');

    const navigate = (newRoute) => setRoute(newRoute);

    const handleAddClass = (newClass) => {
        setClasses(prevClasses => [...prevClasses, newClass]);
    };

    const handleStartAuditorSession = async () => {
        setIsLoading(true);
        setError('');
        try {
            const response = await fetch('http://127.0.0.1:5000/startSession', { method: 'POST' });
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
            const data = await response.json();
            
            setSessionId(data.sessionId);
            setProofCode(data.proof_code);
            setChatHistory([{ author: 'ai', text: data.ai_response_text }]);
            navigate('session');
        } catch (err) {
            setError(`Failed to start session. Is the backend server running? Details: ${err.message}`);
        } finally {
            setIsLoading(false);
        }
    };
    
    const handleSendMessage = async (message) => {
        if (!sessionId) return;
        const userMessage = { author: 'user', text: message };
        setChatHistory(prev => [...prev, userMessage]);

        try {
            const response = await fetch('http://127.0.0.1:5000/sendMessage', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ sessionId, message }),
            });
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
            const data = await response.json();
            
            setChatHistory(prev => [...prev, { author: 'ai', text: data.ai_response_text, isVerified: data.is_verified }]);
            setProofCode(data.proof_code);
        } catch (err) {
            setChatHistory(prev => [...prev, { author: 'system', text: `Error: Could not contact server. ${err.message}` }]);
        }
    };

    return (
        <div className="bg-gray-900 text-white min-h-screen font-sans">
            <header className="bg-gray-900/80 backdrop-blur-sm sticky top-0 z-40 border-b border-gray-700">
                <div className="container mx-auto p-4 flex justify-between items-center">
                    <h1 className="text-2xl font-bold text-cyan-400 cursor-pointer" onClick={() => navigate('dashboard')}>
                        Altera Labs
                    </h1>
                    {route === 'session' && (
                        <button onClick={() => navigate('dashboard')} className="bg-gray-700 hover:bg-gray-600 text-white font-semibold py-2 px-4 rounded-lg transition-transform transform hover:scale-105">
                            ← Back to Dashboard
                        </button>
                    )}
                </div>
            </header>
            <main>
                {route === 'dashboard' ? (
                    <Dashboard 
                        classes={classes} 
                        onAddClass={handleAddClass}
                        onStartAuditor={handleStartAuditorSession}
                        isLoadingAuditor={isLoading}
                        auditorError={error}
                    />
                ) : (
                    <SessionView 
                        proofCode={proofCode}
                        chatHistory={chatHistory}
                        onSendMessage={handleSendMessage}
                    />
                )}
            </main>
        </div>
    );
}

// --- DASHBOARD COMPONENTS ---

function Dashboard({ classes, onAddClass, onStartAuditor, isLoadingAuditor, auditorError }) {
    const [isModalOpen, setIsModalOpen] = useState(false);
    const [expandedClass, setExpandedClass] = useState(null);
    const [explanation, setExplanation] = useState({ concept: '', text: '', isLoading: false });
    
    const handleExplainConcept = async (concept) => {
        setExplanation({ concept, text: '', isLoading: true });
        try {
            const response = await fetch('http://127.0.0.1:5000/explainConcept', {
                method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ concept }),
            });
            if (!response.ok) throw new Error('Failed to fetch explanation.');
            const data = await response.json();
            setExplanation({ concept, text: data.explanation, isLoading: false });
        } catch (error) {
            setExplanation({ concept, text: 'Could not load explanation.', isLoading: false });
        }
    };

    return (
        <div className="container mx-auto p-8">
            <div className="bg-gray-800 rounded-xl shadow-xl p-6 mb-8 text-center">
                <h3 className="text-2xl font-bold text-white mb-2">AI Cognitive Partner</h3>
                <p className="text-gray-400 mb-4">Launch a session to work through a formal proof, step-by-step.</p>
                <button onClick={onStartAuditor} disabled={isLoadingAuditor} className="bg-cyan-500 hover:bg-cyan-600 text-white font-bold py-2 px-6 rounded-lg shadow-lg transition-transform transform hover:scale-105 disabled:bg-gray-500 disabled:cursor-not-allowed">
                    {isLoadingAuditor ? 'Starting...' : 'Launch Proof Auditor'}
                </button>
                {auditorError && <p className="text-red-400 mt-3">{auditorError}</p>}
            </div>

            <div className="flex justify-between items-center mb-8">
                <h2 className="text-3xl font-semibold">Your Classes</h2>
                <button onClick={() => setIsModalOpen(true)} className="bg-gray-700 hover:bg-gray-600 text-white font-bold py-2 px-4 rounded-lg">
                    + Add a Class
                </button>
            </div>
            <div className="space-y-4">
                {classes.map((cls) => (
                    <div key={cls.id} className="bg-gray-800 rounded-xl shadow-lg transition-all duration-300">
                        <div className="p-6 cursor-pointer" onClick={() => setExpandedClass(expandedClass === cls.id ? null : cls.id)}>
                            <h3 className="text-xl font-bold text-white">{cls.name}</h3>
                            <p className="text-gray-400 text-sm">{expandedClass === cls.id ? 'Click to Collapse' : 'Click to Expand'}</p>
                        </div>
                        {expandedClass === cls.id && (
                            <div className="p-6 border-t border-gray-700">
                                <h4 className="font-semibold text-lg mb-3 text-cyan-400">Key Concepts</h4>
                                <div className="flex flex-wrap gap-2">
                                    {cls.concepts.map(concept => (
                                        <button key={concept} onClick={() => handleExplainConcept(concept)} className="bg-gray-700 hover:bg-gray-600 text-sm text-white py-1 px-3 rounded-full">
                                            {concept}
                                        </button>
                                    ))}
                                </div>
                            </div>
                        )}
                    </div>
                ))}
            </div>

            {isModalOpen && <AddClassModal onClose={() => setIsModalOpen(false)} onAddClass={onAddClass} />}
            {explanation.concept && <ExplanationModal explanation={explanation} onClose={() => setExplanation({ concept: '', text: '', isLoading: false })} />}
        </div>
    );
}

function AddClassModal({ onClose, onAddClass }) {
    const [className, setClassName] = useState('');
    const [syllabus, setSyllabus] = useState(null);
    const [isSubmitting, setIsSubmitting] = useState(false);
    const [error, setError] = useState('');

    const handleSubmit = async (e) => {
        e.preventDefault();
        setError('');
        if (!className || !syllabus) { setError('Please provide both a class name and a syllabus file.'); return; }
        setIsSubmitting(true);

        const formData = new FormData();
        formData.append('className', className);
        formData.append('syllabus', syllabus);

        try {
            const response = await fetch('http://127.0.0.1:5000/addClass', { method: 'POST', body: formData });
            if (!response.ok) throw new Error(`Server error: ${await response.text()}`);
            const result = await response.json();
            onAddClass({ name: result.className, id: result.classId, concepts: result.concepts });
            onClose();
        } catch (err) {
            setError(`Failed to add class. Details: ${err.message}`);
        } finally {
            setIsSubmitting(false);
        }
    };

    return (
        <div className="fixed inset-0 bg-black bg-opacity-70 flex justify-center items-center z-50">
            <div className="bg-gray-800 p-8 rounded-2xl shadow-2xl w-full max-w-md m-4">
                <h2 className="text-2xl font-bold mb-6 text-white">Add a New Class</h2>
                <form onSubmit={handleSubmit}>
                    {error && <p className="text-red-400 bg-red-900/30 p-3 rounded-lg mb-4">{error}</p>}
                    <div className="mb-4">
                        <label className="block text-gray-400 text-sm font-bold mb-2">Class Name</label>
                        <input type="text" value={className} onChange={(e) => setClassName(e.target.value)} placeholder="e.g., MATH-401 Abstract Algebra" className="w-full bg-gray-700 border border-gray-600 rounded-lg py-3 px-4 text-white focus:outline-none focus:ring-2 focus:ring-cyan-500" required />
                    </div>
                    <div className="mb-6">
                        <label className="block text-gray-400 text-sm font-bold mb-2">Syllabus (.pdf, .txt)</label>
                        <input type="file" onChange={(e) => setSyllabus(e.target.files[0])} accept=".pdf,.txt,.md" className="w-full text-sm text-gray-400 file:mr-4 file:py-2 file:px-4 file:rounded-lg file:border-0 file:text-sm file:font-semibold file:bg-cyan-500 file:text-white hover:file:bg-cyan-600" required />
                    </div>
                    <div className="flex justify-end gap-4">
                        <button type="button" onClick={onClose} className="bg-gray-600 hover:bg-gray-700 text-white font-bold py-2 px-4 rounded-lg">Cancel</button>
                        <button type="submit" disabled={isSubmitting} className="bg-cyan-500 hover:bg-cyan-600 text-white font-bold py-2 px-4 rounded-lg disabled:bg-gray-500">{isSubmitting ? 'Analyzing...' : 'Create Class'}</button>
                    </div>
                </form>
            </div>
        </div>
    );
}

function ExplanationModal({ explanation, onClose }) {
    return (
        <div className="fixed inset-0 bg-black bg-opacity-70 flex justify-center items-center z-50" onClick={onClose}>
            <div className="bg-gray-800 p-8 rounded-2xl shadow-2xl w-full max-w-2xl m-4" onClick={e => e.stopPropagation()}>
                <h3 className="text-2xl font-bold mb-4 text-cyan-400">Explanation: {explanation.concept}</h3>
                {explanation.isLoading ? <p>Loading...</p> : <LatexRenderer text={explanation.text} />}
                <button onClick={onClose} className="mt-6 bg-gray-600 hover:bg-gray-700 text-white font-bold py-2 px-4 rounded-lg">Close</button>
            </div>
        </div>
    );
}

// --- SESSION COMPONENTS ---

function SessionView({ proofCode, chatHistory, onSendMessage }) {
    const [leftPanelWidth, setLeftPanelWidth] = useState(50);
    const containerRef = useRef(null);
    const isDragging = useRef(false);

    const handleMouseDown = (e) => { isDragging.current = true; e.preventDefault(); };
    const handleMouseUp = () => { isDragging.current = false; };
    const handleMouseMove = (e) => {
        if (!isDragging.current || !containerRef.current) return;
        const containerRect = containerRef.current.getBoundingClientRect();
        const newLeftWidth = ((e.clientX - containerRect.left) / containerRect.width) * 100;
        if (newLeftWidth > 20 && newLeftWidth < 80) setLeftPanelWidth(newLeftWidth);
    };

    useEffect(() => {
        window.addEventListener('mousemove', handleMouseMove);
        window.addEventListener('mouseup', handleMouseUp);
        return () => {
            window.removeEventListener('mousemove', handleMouseMove);
            window.removeEventListener('mouseup', handleMouseUp);
        };
    }, []);

    return (
        <div ref={containerRef} className="flex" style={{ height: 'calc(100vh - 65px)'}}>
            <div className="p-4 flex flex-col" style={{ width: `${leftPanelWidth}%` }}>
                <h2 className="text-xl font-semibold text-gray-300 mb-4 pl-2">Dialogue</h2>
                <ChatPanel history={chatHistory} onSendMessage={onSendMessage} />
            </div>
            <div onMouseDown={handleMouseDown} className="w-2 cursor-col-resize bg-gray-700 hover:bg-cyan-500 transition-colors"></div>
            <div className="flex-grow flex flex-col" style={{ width: `${100 - leftPanelWidth}%` }}>
                <div className="flex flex-col h-full p-4">
                    <h2 className="text-xl font-semibold text-gray-300 mb-4 pl-2">Formal Proof State (Lean 4)</h2>
                    <LeanEditor content={proofCode} />
                </div>
            </div>
        </div>
    );
}

function ChatPanel({ history, onSendMessage }) {
    const [message, setMessage] = useState('');
    const chatEndRef = useRef(null);

    useEffect(() => { chatEndRef.current?.scrollIntoView({ behavior: 'smooth' }); }, [history]);

    const handleSend = () => {
        if (message.trim()) {
            onSendMessage(message);
            setMessage('');
        }
    };

    return (
        <div className="flex flex-col h-full bg-gray-800 rounded-lg">
            <div className="flex-grow p-4 overflow-y-auto">
                {history.map((msg, index) => {
                    const isUser = msg.author === 'user';
                    const isSystem = msg.author === 'system';
                    const isVerified = msg.isVerified === true;
                    const isRejected = msg.isVerified === false;
                    
                    let bubbleStyles = 'bg-gray-700';
                    if (isUser) bubbleStyles = 'bg-cyan-600';
                    if (isSystem) bubbleStyles = 'bg-yellow-900/50 text-yellow-400 text-center text-sm';
                    
                    let borderStyles = '';
                    if (isVerified) borderStyles = 'border-2 border-green-500';
                    if (isRejected) borderStyles = 'border-2 border-red-500';

                    return (
                        <div key={index} className={`flex my-2 ${isUser ? 'justify-end' : 'justify-start'} ${isSystem ? 'justify-center' : ''}`}>
                            <div className={`rounded-xl p-3 max-w-lg ${bubbleStyles} ${borderStyles}`}>
                                {/* UPDATED: Use LatexRenderer for all chat messages */}
                                <LatexRenderer text={msg.text} />
                            </div>
                        </div>
                    );
                })}
                <div ref={chatEndRef} />
            </div>
            <div className="p-4 border-t border-gray-700">
                 {/* NEW: Live LaTeX Preview */}
                {message.trim() && (
                    <div className="p-3 mb-3 bg-gray-900 rounded-lg border border-gray-700">
                        <h4 className="text-xs text-gray-500 mb-2 font-semibold tracking-wider uppercase">Preview</h4>
                        <LatexRenderer text={message} />
                    </div>
                )}
                <div className="flex items-center bg-gray-700 rounded-lg">
                    <input type="text" value={message} onChange={(e) => setMessage(e.target.value)} onKeyPress={(e) => e.key === 'Enter' && handleSend()} placeholder="Type your next step or question... Use $...$ for math." className="flex-grow bg-transparent p-3 text-white focus:outline-none" />
                    <button onClick={handleSend} className="p-3 text-cyan-400 hover:text-cyan-300 disabled:text-gray-500" disabled={!message.trim()}>
                        <svg xmlns="http://www.w3.org/2000/svg" className="h-6 w-6" fill="none" viewBox="0 0 24 24" stroke="currentColor"><path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 19l9 2-9-18-9 18 9-2zm0 0v-8" /></svg>
                    </button>
                </div>
            </div>
        </div>
    );
}

function LeanEditor({ content }) {
    return (
        <div className="flex-grow rounded-lg overflow-hidden border border-gray-700 h-full">
             <CodeMirror 
                value={content} 
                height="100%" 
                theme={oneDark} 
                extensions={[basicSetup({lineNumbers: true, foldGutter: true})]} 
                readOnly={true} 
                style={{height: '100%'}}
             />
        </div>
    );
}
