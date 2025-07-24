// frontend/components/SessionView.tsx

/**
 * SessionView is the primary component for the interactive tutoring experience.
 * It orchestrates the main layout, including the proof display area, the chat interface,
 * and the side panel for controls and diagnostics. It manages all state related to a
 * single tutoring session.
 */
import React, { useState, useEffect, useCallback, useRef } from 'react';

// --- Component Imports ---
// We'll reuse existing components for a consistent UI.
import { ViewModeSwitcher } from './ViewModeSwitcher';
import { ChatMentor } from './ChatMentor';
import { Katex } from './Katex'; // For rendering LaTeX
import { Message } from '../types'; // Assuming you have a types file for message structure

// --- API Service Import ---
// This service will encapsulate all fetch calls to the backend.
// You would create this file to handle API communication.
import { startSession, sendMessage } from '../services/aiService'; 

// --- Helper & Sub-Components ---

/**
 * A simple loading spinner to provide feedback during API calls.
 */
const LoadingSpinner: React.FC = () => (
  <div className="flex items-center justify-center p-4">
    <div className="w-8 h-8 border-4 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
  </div>
);

/**
 * Displays the current state of the mathematical proof.
 * It can render either the formal Lean 4 code or the more user-friendly LaTeX representation.
 */
const ProofStateDisplay: React.FC<{ leanCode: string; latexCode: string; viewMode: 'latex' | 'lean' }> = ({
  leanCode,
  latexCode,
  viewMode,
}) => {
  return (
    <div className="bg-gray-800 text-white rounded-lg shadow-inner p-6 flex-grow overflow-auto">
      <h3 className="text-lg font-semibold text-gray-300 mb-4 border-b border-gray-700 pb-2">Current Proof State</h3>
      {viewMode === 'lean' ? (
        // Display raw Lean code in a preformatted block
        <pre className="text-sm font-mono whitespace-pre-wrap"><code>{leanCode}</code></pre>
      ) : (
        // Render the LaTeX string using the Katex component
        <div className="text-lg">
          <Katex content={latexCode} />
        </div>
      )}
    </div>
  );
};


// --- Main SessionView Component ---

export const SessionView: React.FC = () => {
  // --- State Management ---
  const [sessionId, setSessionId] = useState<string | null>(null);
  const [messages, setMessages] = useState<Message[]>([]);
  const [leanCode, setLeanCode] = useState<string>('');
  const [latexCode, setLatexCode] = useState<string>(''); // Assuming backend will provide this
  const [viewMode, setViewMode] = useState<'latex' | 'lean'>('latex');
  const [isLoading, setIsLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);
  
  // A ref to hold the session ID to avoid issues with stale closures in callbacks.
  const sessionIdRef = useRef(sessionId);
  useEffect(() => {
    sessionIdRef.current = sessionId;
  }, [sessionId]);


  // --- API Communication ---

  // Function to initialize a new session when the component mounts.
  const initializeSession = useCallback(async () => {
    setIsLoading(true);
    setError(null);
    try {
      // Call the API to start a new session in 'homework' mode by default.
      const data = await startSession('homework');
      setSessionId(data.sessionId);
      setLeanCode(data.proofCode);
      // For now, we'll just show the lean code as latex until a proper converter is in place
      setLatexCode(data.proofCode); 
      setMessages([{ author: 'ai', text: data.aiResponse }]);
    } catch (err) {
      setError('Failed to start a new session. Please check the server connection and try again.');
      console.error(err);
    } finally {
      setIsLoading(false);
    }
  }, []);

  // Effect to start the session on component mount.
  useEffect(() => {
    initializeSession();
  }, [initializeSession]);

  // Function to handle sending a message from the ChatMentor component.
  const handleSendMessage = useCallback(async (messageText: string) => {
    const currentSessionId = sessionIdRef.current;
    if (!currentSessionId || !messageText.trim()) return;

    // Add the user's message to the chat immediately for a responsive feel.
    setMessages(prev => [...prev, { author: 'user', text: messageText }]);
    setIsLoading(true);

    try {
      const data = await sendMessage(currentSessionId, messageText);
      // Add the AI's response and update the proof state.
      setMessages(prev => [...prev, { author: 'ai', text: data.aiResponse }]);
      setLeanCode(data.proofCode);
      // Again, using lean code as a placeholder for latex
      setLatexCode(data.proofCode); 
    } catch (err) {
      setError('Failed to send message. Please try again.');
      console.error(err);
      // Optionally add an error message to the chat
      setMessages(prev => [...prev, { author: 'ai', text: 'Sorry, I encountered an error. Please try again.' }]);
    } finally {
      setIsLoading(false);
    }
  }, []);


  // --- Render Logic ---

  if (error) {
    return (
      <div className="flex items-center justify-center h-full bg-red-900 text-white p-8 rounded-lg">
        <div className="text-center">
          <h2 className="text-2xl font-bold mb-4">An Error Occurred</h2>
          <p>{error}</p>
          <button
            onClick={initializeSession}
            className="mt-6 bg-red-500 hover:bg-red-600 text-white font-bold py-2 px-4 rounded-lg transition-colors"
          >
            Retry Connection
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className="flex h-screen bg-gray-900 text-gray-100 font-sans">
      {/* Main Content Panel */}
      <main className="flex-1 flex flex-col p-4 md:p-6 gap-4">
        <div className="flex-1 flex flex-col min-h-0 bg-gray-800/50 rounded-xl border border-gray-700 shadow-2xl">
          <div className="p-4 flex-1 flex flex-col gap-4 min-h-0">
            <ProofStateDisplay 
              leanCode={leanCode}
              latexCode={latexCode}
              viewMode={viewMode}
            />
            <ChatMentor 
              messages={messages} 
              onSendMessage={handleSendMessage}
              isLoading={isLoading}
            />
          </div>
        </div>
      </main>

      {/* Side Panel for Controls and Diagnostics */}
      <aside className="w-72 bg-gray-900/80 border-l border-gray-700 p-6 flex flex-col gap-8">
        <div>
          <h2 className="text-xl font-bold mb-4 text-gray-200">Session Controls</h2>
          <div className="bg-gray-800 p-4 rounded-lg">
            <ViewModeSwitcher viewMode={viewMode} setViewMode={setViewMode} />
          </div>
        </div>
        
        {/* Placeholder for future diagnostic panels */}
        <div className="flex-1">
           <h2 className="text-xl font-bold mb-4 text-gray-200">Diagnostics</h2>
           <div className="bg-gray-800 p-4 rounded-lg h-full text-gray-400 text-sm">
             <p>Diagnostic panels (like Student Mastery, Trace, etc.) will be displayed here in future phases.</p>
             {isLoading && <LoadingSpinner />}
           </div>
        </div>
      </aside>
    </div>
  );
};
