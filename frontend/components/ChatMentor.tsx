// frontend/components/ChatMentor.tsx

import React, { useState, useEffect, useRef } from 'react';
import { ChatMessage } from '../types';
import Katex from './Katex';

// --- MODIFIED: Added mode prop and onSendMessage for general chat ---
interface ChatMentorProps {
    history: ChatMessage[];
    isLoading: boolean;
    mode?: 'chat' | 'verify';
    onVerifyStep: (step: string) => void;
    onSendMessage?: (message: string) => void;
    onContextualQuery: (selectedText: string, contextText: string) => void;
    // Add input state management props
    inputValue?: string;
    onInputChange?: (value: string) => void;
}

const ChatMentor: React.FC<ChatMentorProps> = ({ 
    history, 
    isLoading, 
    mode = 'chat',
    onVerifyStep, 
    onSendMessage,
    onContextualQuery,
    inputValue = '',
    onInputChange
}) => {
    const [input, setInput] = useState(inputValue);
    const chatEndRef = useRef<HTMLDivElement>(null);
    const chatContainerRef = useRef<HTMLDivElement>(null);
    const [selection, setSelection] = useState<{ text: string; x: number; y: number } | null>(null);

    // Debug logging for chat history
    useEffect(() => {
        console.log('ChatMentor: Received new history:', history);
    }, [history]);

    // Sync input with parent component
    useEffect(() => {
        setInput(inputValue);
    }, [inputValue]);

    // Effect to scroll to the bottom of the chat on new messages.
    useEffect(() => {
        chatEndRef.current?.scrollIntoView({ behavior: 'smooth' });
    }, [history, isLoading]);

    // Effect for "Highlight-to-Ask" feature.
    useEffect(() => {
        const handleMouseUp = () => {
            setTimeout(() => {
                const currentSelection = window.getSelection();
                const selectedText = currentSelection?.toString().trim();

                if (currentSelection && selectedText && selectedText.length > 5 && selectedText.length < 100) {
                    const range = currentSelection.getRangeAt(0);
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

    const handleInputChange = (e: React.ChangeEvent<HTMLTextAreaElement>) => {
        const value = e.target.value;
        setInput(value);
        onInputChange?.(value);
    };

    const handleKeyDown = (e: React.KeyboardEvent<HTMLTextAreaElement>) => {
        if (e.key === 'Enter' && !e.shiftKey) {
            e.preventDefault();
            handleSubmit(e as any);
        }
    };

    const handleSubmit = async (e: React.FormEvent) => {
        e.preventDefault();
        if (input.trim() && !isLoading) {
            const message = input.trim();
            setInput('');
            onInputChange?.('');

            if (mode === 'chat' && onSendMessage) {
                // Handle general tutoring chat
                onSendMessage(message);
            } else if (mode === 'verify') {
                // Handle proof verification
                onVerifyStep(message);
            }
        }
    };

    // Function to parse and render mathematical content
    const renderMessageContent = (content: string) => {
        // Split content by LaTeX delimiters
        const parts = content.split(/(\$[^$]+\$|\\\([^)]+\\\)|\\\[[^\]]+\\\])/);
        
        return parts.map((part, index) => {
            if (part.startsWith('$') && part.endsWith('$')) {
                // Inline math: $...$
                const math = part.slice(1, -1);
                return <Katex key={index} math={math} block={false} />;
            } else if (part.startsWith('\\(') && part.endsWith('\\)')) {
                // Inline math: \(...\)
                const math = part.slice(2, -2);
                return <Katex key={index} math={math} block={false} />;
            } else if (part.startsWith('\\[') && part.endsWith('\\]')) {
                // Display math: \[...\]
                const math = part.slice(2, -2);
                return <Katex key={index} math={math} block={true} />;
            } else {
                // Regular text
                return <span key={index} style={{whiteSpace: 'pre-wrap'}}>{part}</span>;
            }
        });
    };

    // Function to extract LaTeX from input for preview
    const extractLatexFromInput = (text: string) => {
        const latexMatches = text.match(/\$[^$]+\$|\\\([^)]+\\\)|\\\[[^\]]+\\\]/g);
        return latexMatches || [];
    };

    const latexInInput = extractLatexFromInput(input);
    
    // --- MODIFIED: MessageBubble now renders verification status and KaTeX ---
    const MessageBubble: React.FC<{ msg: ChatMessage }> = ({ msg }) => {
        const isModel = msg.role === 'model';
        const hasVerification = !!msg.verification;

        // System messages and practice prompts can remain if needed for other flows,
        // but the primary addition is handling the verification display.
        if (msg.role === 'system') {
             return (
                <div className="text-center my-2">
                    <span className="text-xs text-slate-500 italic px-2 py-1 bg-slate-800 rounded-full">{msg.content}</span>
                </div>
            )
        }

        return (
            <div className={`flex ${isModel ? 'justify-start' : 'justify-end'} mb-3`}>
                <div className={`rounded-lg px-4 py-2 max-w-sm md:max-w-md lg:max-w-lg ${isModel ? 'bg-slate-700 text-slate-200' : 'bg-cyan-600 text-white'}`}>
                    <div>{renderMessageContent(msg.content)}</div>
                    
                    {/* --- NEW: Display for verification results --- */}
                    {hasVerification && (
                        <div className={`mt-3 pt-2 border-t text-sm font-semibold flex items-center gap-2 ${
                            msg.verification?.isComplete ? 'border-green-400/50 text-green-400' : 
                            msg.verification?.verified ? 'border-blue-400/50 text-blue-400' : 'border-red-400/50 text-red-400'
                        }`}>
                            {msg.verification?.isComplete ? '✅ Proof Complete' : msg.verification?.verified ? '✔️ Step Verified' : '❌ Step Failed'}
                        </div>
                    )}
                </div>
            </div>
        );
    };

    // Dynamic placeholder based on mode
    const getPlaceholder = () => {
        return mode === 'chat' 
            ? "Ask a question or describe your approach... (Shift+Enter for new line)" 
            : "Enter your proof step here... (Shift+Enter for new line)";
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
                            Explain
                        </button>
                    </div>
                )}

                <div ref={chatEndRef}></div>
            </div>
            
            {/* LaTeX Preview */}
            {latexInInput.length > 0 && (
                <div className="px-4 py-2 border-t border-slate-700 bg-slate-900">
                    <div className="text-xs text-slate-400 mb-1">LaTeX Preview:</div>
                    <div className="flex flex-wrap gap-2">
                        {latexInInput.map((latex, index) => (
                            <div key={index} className="bg-slate-800 px-2 py-1 rounded text-sm">
                                {renderMessageContent(latex)}
                            </div>
                        ))}
                    </div>
                </div>
            )}
            
            <div className="p-4 border-t border-slate-700">
                <form onSubmit={handleSubmit} className="flex gap-3">
                    <textarea
                        value={input}
                        onChange={handleInputChange}
                        onKeyDown={handleKeyDown}
                        placeholder={getPlaceholder()}
                        disabled={isLoading}
                        rows={1}
                        className="flex-grow bg-slate-900 border border-slate-600 rounded-lg py-2 px-4 focus:ring-2 focus:ring-cyan-500 focus:outline-none disabled:cursor-not-allowed resize-none"
                        style={{ minHeight: '40px', maxHeight: '120px' }}
                    />
                    <button type="submit" disabled={isLoading} className="bg-cyan-600 text-white font-bold py-2 px-4 rounded-lg hover:bg-cyan-500 disabled:bg-slate-600 disabled:cursor-not-allowed transition-colors self-end">
                        Send
                    </button>
                </form>
            </div>
        </div>
    );
};

export default ChatMentor;