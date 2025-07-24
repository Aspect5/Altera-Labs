
import React from 'react';

interface SyllabusInputProps {
    syllabusText: string;
    setSyllabusText: (text: string) => void;
    onProcess: () => void;
    isLoading: boolean;
}

const SyllabusInput: React.FC<SyllabusInputProps> = ({ syllabusText, setSyllabusText, onProcess, isLoading }) => {
    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <h2 className="text-xl font-semibold text-cyan-400 mb-3">1. Input Syllabus</h2>
            <textarea
                value={syllabusText}
                onChange={(e) => setSyllabusText(e.target.value)}
                className="w-full h-64 p-3 bg-slate-900 border border-slate-700 rounded-md focus:ring-2 focus:ring-cyan-500 focus:outline-none text-slate-300 resize-y"
                placeholder="Paste your syllabus text here..."
                disabled={isLoading}
            />
            <button
                onClick={onProcess}
                disabled={isLoading}
                className="mt-4 w-full bg-cyan-600 text-white font-bold py-2 px-4 rounded-md hover:bg-cyan-500 disabled:bg-slate-600 disabled:cursor-not-allowed transition-colors flex items-center justify-center"
            >
                {isLoading ? (
                    <>
                        <svg className="animate-spin -ml-1 mr-3 h-5 w-5 text-white" xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24">
                            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4"></circle>
                            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"></path>
                        </svg>
                        Processing...
                    </>
                ) : (
                    'Process Syllabus with AI'
                )}
            </button>
        </div>
    );
};

export default SyllabusInput;