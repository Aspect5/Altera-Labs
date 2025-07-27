// frontend/components/ClassCreationPanel.tsx

import React, { useState, useRef } from 'react';

interface ClassCreationPanelProps {
  className: string;
  setClassName: (name: string) => void;
  // The main callback now accepts both file types
  onCreateClass: (className: string, syllabusFile: File | null, homeworkFile: File | null) => void;
  isLoading: boolean;
}

const ClassCreationPanel: React.FC<ClassCreationPanelProps> = ({
  className,
  setClassName,
  onCreateClass,
  isLoading,
}) => {
  const [syllabusFile, setSyllabusFile] = useState<File | null>(null);
  const [homeworkFile, setHomeworkFile] = useState<File | null>(null);
  
  // Use separate refs for each file input
  const syllabusInputRef = useRef<HTMLInputElement>(null);
  const homeworkInputRef = useRef<HTMLInputElement>(null);

  const handleSyllabusChange = (event: React.ChangeEvent<HTMLInputElement>) => {
    if (event.target.files && event.target.files[0]) {
      setSyllabusFile(event.target.files[0]);
    }
    event.target.value = ''; // Allow re-selecting the same file
  };

  const handleHomeworkChange = (event: React.ChangeEvent<HTMLInputElement>) => {
    if (event.target.files && event.target.files[0]) {
      setHomeworkFile(event.target.files[0]);
    }
    event.target.value = ''; // Allow re-selecting the same file
  };

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    if (className.trim() && (syllabusFile || homeworkFile)) {
      onCreateClass(className.trim(), syllabusFile, homeworkFile);
    }
  };

  // The "Create Class" button is disabled until a class name and at least one file are provided.
  const isFormIncomplete = !className.trim() || (!syllabusFile && !homeworkFile);

  return (
    <div className="rounded-lg bg-slate-800 p-6 shadow-2xl">
      <h2 className="text-2xl font-bold text-cyan-400">1. Create Your Class</h2>
      <form onSubmit={handleSubmit} className="mt-4 space-y-4">
        <div>
          <label htmlFor="className" className="block text-sm font-medium text-slate-300">
            Class Name
          </label>
          <input
            type="text"
            id="className"
            value={className}
            onChange={(e) => setClassName(e.target.value)}
            className="mt-1 block w-full rounded-md border-slate-600 bg-slate-900 px-3 py-2 text-white shadow-sm focus:border-cyan-500 focus:ring-cyan-500 sm:text-sm"
            placeholder="e.g., Abstract Algebra"
            required
          />
        </div>

        {/* --- Syllabus Upload (Recommended) --- */}
        <div>
            <label className="block text-sm font-medium text-slate-300">
                Syllabus <span className="text-xs text-blue-400">(Highly Recommended)</span>
            </label>
            <input type="file" ref={syllabusInputRef} onChange={handleSyllabusChange} className="hidden" accept=".pdf,.txt,.md,.tex"/>
            <button 
                type="button" 
                onClick={() => syllabusInputRef.current?.click()}
                className={`mt-1 flex w-full justify-center rounded-md border-2 border-dashed px-3 py-3 text-sm font-semibold transition-colors ${
                    syllabusFile 
                    ? 'border-green-500 bg-green-900/50 text-green-300' 
                    : 'border-slate-600 text-slate-400 hover:border-cyan-500 hover:bg-slate-700/50'
                }`}
            >
                {syllabusFile ? `✓ Selected: ${syllabusFile.name}` : '+ Upload Syllabus'}
            </button>
        </div>

        <div className="flex items-center">
            <hr className="flex-grow border-slate-600"/>
            <span className="px-2 text-xs font-medium text-slate-500">OR</span>
            <hr className="flex-grow border-slate-600"/>
        </div>


        {/* --- Homework Upload --- */}
        <div>
            <label className="block text-sm font-medium text-slate-300">
                Homework File
            </label>
            <input type="file" ref={homeworkInputRef} onChange={handleHomeworkChange} className="hidden" accept=".pdf,.txt,.md,.tex"/>
            <button 
                type="button" 
                onClick={() => homeworkInputRef.current?.click()}
                className={`mt-1 flex w-full justify-center rounded-md border-2 border-dashed px-3 py-3 text-sm font-semibold transition-colors ${
                    homeworkFile 
                    ? 'border-green-500 bg-green-900/50 text-green-300' 
                    : 'border-slate-600 text-slate-400 hover:border-cyan-500 hover:bg-slate-700/50'
                }`}
            >
                {homeworkFile ? `✓ Selected: ${homeworkFile.name}` : '+ Upload Homework'}
            </button>
        </div>

        <button
          type="submit"
          disabled={isFormIncomplete || isLoading}
          className="w-full rounded-md bg-cyan-600 px-4 py-2 font-bold text-white shadow-lg transition-all hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-600 disabled:opacity-50"
        >
          {isLoading ? 'Creating...' : 'Create Class & Start Session'}
        </button>
      </form>
    </div>
  );
};

export default ClassCreationPanel;
