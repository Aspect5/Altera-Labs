// frontend/components/ChatMentor.tsx

import React, { useState, useEffect, useRef } from 'react';
import { ChatMessage } from '../types';

interface ChatMentorProps {
    history: ChatMessage[];
    isLoading: boolean;
    onSendMessage: (message: string) => void;
    onContextualQuery: (selectedText: string, contextText: string) => void;
    onStartPractice: (nodeId: string) => void;
    onPracticeAnswer: (nodeId: string, isCorrect: boolean) => void;
    activePracticeNodeId: string | null;
}

const ChatMentor: React.FC<ChatMentorProps> = ({ history, isLoading, onSendMessage, onContextualQuery, onStartPractice, onPracticeAnswer, activePracticeNodeId }) => {
    const [input, setInput] = useState('');
    const chatEndRef = useRef<HTMLDivElement>(null);
    const chatContainerRef = useRef<HTMLDivElement>(null);
    
    // State to manage the "Explain" pop-up for contextual queries.
    const [selection, setSelection] = useState<{ text: string; x: number; y: number } | null>(null);

    // Effect to scroll to the bottom of the chat on new messages.
    useEffect(() => {
        chatEndRef.current?.scrollIntoView({ behavior: 'smooth' });
    }, [history, isLoading]);

    // Effect to handle text selection for the "Highlight-to-Ask" feature.
    useEffect(() => {
        const handleMouseUp = () => {
            setTimeout(() => {
                const currentSelection = window.getSelection();
                const selectedText = currentSelection?.toString().trim();

                if (currentSelection && selectedText && selectedText.length > 5 && selectedText.length < 100) {
                    const range = currentSelection.getRangeAt(0);
                    // Ensure the selection is within our chat container before showing the popup.
                    if (chatContainerRef.current && chatContainerRef.current.contains(range.commonAncestorContainer)) {
                        const rect = range.getBoundingClientRect();
                        const containerRect = chatContainerRef.current.getBoundingClientRect();
                        setSelection({
                            text: selectedText,
                            x: rect.left - containerRect.left + rect.width / 2,
                            y: rect.top - containerRect.top,
                        });
                    }
                } else {
                    setSelection(null);
                }
            }, 10);
        };
        
        document.addEventListener('mouseup', handleMouseUp);
        return () => document.removeEventListener('mouseup', handleMouseUp);
    }, []);

    const handleExplainClick = () => {
        if (selection) {
            const contextMessage = history.find(msg => msg.content.includes(selection.text))?.content || '';
            onContextualQuery(selection.text, contextMessage);
            setSelection(null);
        }
    };

    const handleSubmit = (e: React.FormEvent) => {
        e.preventDefault();
        if (input.trim() && !isLoading && !activePracticeNodeId) {
            onSendMessage(input.trim());
            setInput('');
        }
    };
    
    // This is the complete MessageBubble component from your original file.
    const MessageBubble: React.FC<{ msg: ChatMessage }> = ({ msg }) => {
        const isModel = msg.role === 'model';
        const isSystem = msg.role === 'system';

        if (isSystem && msg.practiceNodeId) {
            // This is the prompt to answer a practice problem
            return (
                <div className="bg-slate-700/50 p-3 my-2 rounded-lg text-center">
                    <p className="text-slate-300 text-sm italic mb-3">{msg.content}</p>
                    <div className="grid grid-cols-2 gap-3">
                        <button
                            onClick={() => onPracticeAnswer(msg.practiceNodeId!, true)}
                            className="w-full bg-emerald-600 text-white font-bold py-2 px-4 rounded-md hover:bg-emerald-500 transition-colors"
                        >✓ Correct</button>
                        <button
                            onClick={() => onPracticeAnswer(msg.practiceNodeId!, false)}
                            className="w-full bg-red-600 text-white font-bold py-2 px-4 rounded-md hover:bg-red-500 transition-colors"
                        >✗ Incorrect</button>
                    </div>
                </div>
            )
        }
        
        if (isSystem) {
             return (
                <div className="text-center my-2">
                    <span className="text-xs text-slate-500 italic px-2 py-1 bg-slate-800 rounded-full">{msg.content}</span>
                </div>
            )
        }

        return (
            <div className={`flex ${isModel ? 'justify-start' : 'justify-end'} mb-3`}>
                <div className={`rounded-lg px-4 py-2 max-w-sm md:max-w-md lg:max-w-lg ${isModel ? 'bg-slate-700 text-slate-200' : 'bg-cyan-600 text-white'}`}>
                    <p style={{whiteSpace: 'pre-wrap'}}>{msg.content}</p>
                    {msg.suggestion && (
                        <div className="mt-3 pt-2 border-t border-t-slate-500/50">
                            <p className="text-xs italic mb-2">{isModel ? 'Suggested Practice:' : ''}</p>
                             <button 
                                onClick={() => onStartPractice(msg.suggestion!.nodeId)}
                                className="w-full bg-slate-600 hover:bg-slate-500 text-white font-semibold py-2 px-3 rounded text-sm text-left transition-colors"
                            >
                                Practice: {msg.suggestion.label}
                            </button>
                        </div>
                    )}
                </div>
            </div>
        );
    };

    return (
        <div className="bg-slate-800 rounded-lg shadow-2xl flex flex-col h-full">
            <div ref={chatContainerRef} className="flex-grow p-4 overflow-y-auto relative">
                {history.map((msg, index) => <MessageBubble key={index} msg={msg} />)}
                
                {isLoading && (
                    <div className="flex justify-start mb-3">
                        <div className="rounded-lg px-4 py-2 bg-slate-700 text-slate-200">
                           <div className="flex items-center space-x-2">
                                <div className="w-2 h-2 bg-slate-400 rounded-full animate-pulse"></div>
                                <div className="w-2 h-2 bg-slate-400 rounded-full animate-pulse [animation-delay:0.2s]"></div>
                                <div className="w-2 h-2 bg-slate-400 rounded-full animate-pulse [animation-delay:0.4s]"></div>
                            </div>
                        </div>
                    </div>
                )}
                
                {selection && (
                    <div 
                        className="absolute z-10 p-1 bg-blue-600 rounded-lg shadow-xl"
                        style={{ left: `${selection.x}px`, top: `${selection.y}px`, transform: 'translate(-50%, -120%)' }}
                    >
                        <button
                            onClick={handleExplainClick}
                            className="text-white text-xs font-bold px-3 py-1 hover:bg-blue-500 rounded-md transition-colors"
                        >
                            Explain This
                        </button>
                    </div>
                )}

                <div ref={chatEndRef}></div>
            </div>
            <div className="p-4 border-t border-slate-700">
                <form onSubmit={handleSubmit} className="flex gap-3">
                    <input
                        type="text"
                        value={input}
                        onChange={(e) => setInput(e.target.value)}
                        placeholder={activePracticeNodeId ? "Please answer the practice question." : "Ask the mentor a question..."}
                        disabled={isLoading || !!activePracticeNodeId}
                        className="flex-grow bg-slate-900 border border-slate-600 rounded-lg py-2 px-4 focus:ring-2 focus:ring-cyan-500 focus:outline-none disabled:cursor-not-allowed"
                    />
                    <button type="submit" disabled={isLoading || !!activePracticeNodeId} className="bg-cyan-600 text-white font-bold py-2 px-4 rounded-lg hover:bg-cyan-500 disabled:bg-slate-600 disabled:cursor-not-allowed transition-colors">
                        Send
                    </button>
                </form>
            </div>
        </div>
    );
};

export default ChatMentor;
