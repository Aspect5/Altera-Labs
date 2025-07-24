// frontend/components/SyllabusInput.tsx

import React, { useState, useRef } from 'react';

interface SyllabusInputProps {
  // Add props for managing the class name state from App.tsx
  className: string;
  setClassName: (name: string) => void;
  // The onProcess function will now take the file object as an argument.
  onProcessSyllabus: (syllabusFile: File) => void;
  isLoading: boolean;
}

const SyllabusInput: React.FC<SyllabusInputProps> = ({ className, setClassName, onProcessSyllabus, isLoading }) => {
  // State to hold the selected file object.
  const [selectedFile, setSelectedFile] = useState<File | null>(null);
  // A ref to the hidden file input element to trigger it programmatically.
  const fileInputRef = useRef<HTMLInputElement>(null);

  const handleFileChange = (event: React.ChangeEvent<HTMLInputElement>) => {
    if (event.target.files && event.target.files[0]) {
      setSelectedFile(event.target.files[0]);
    }
  };

  const handleProcessClick = () => {
    if (selectedFile && className.trim()) {
      onProcessSyllabus(selectedFile);
    } else {
      // Basic validation feedback
      alert("Please enter a class name and select a syllabus file.");
    }
  };

  const handleSelectFileClick = () => {
    // Trigger the hidden file input when the user clicks the button.
    fileInputRef.current?.click();
  };

  return (
    <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
      <h2 className="text-xl font-semibold text-cyan-400 mb-3">1. Create Your Class</h2>
      
      {/* Input for the Class Name */}
      <div className="mb-4">
        <label htmlFor="className" className="block text-sm font-medium text-slate-300 mb-1">
          Class Name
        </label>
        <input
          id="className"
          type="text"
          value={className}
          onChange={(e) => setClassName(e.target.value)}
          className="w-full p-2 bg-slate-900 border border-slate-700 rounded-md focus:ring-2 focus:ring-cyan-500 focus:outline-none text-slate-300"
          placeholder="e.g., Introduction to Real Analysis"
          disabled={isLoading}
        />
      </div>

      {/* Hidden File Input */}
      <input
        type="file"
        ref={fileInputRef}
        onChange={handleFileChange}
        className="hidden"
        accept=".pdf,.txt,.md" // Specify allowed file types
      />

      {/* Button to Trigger File Selection */}
      <button
        onClick={handleSelectFileClick}
        disabled={isLoading}
        className="w-full border-2 border-dashed border-slate-600 text-slate-400 font-semibold py-3 px-4 rounded-md hover:bg-slate-700/50 hover:border-cyan-500 transition-colors"
      >
        {selectedFile ? `Selected: ${selectedFile.name}` : 'Select Syllabus File (.pdf, .txt)'}
      </button>

      {/* Process Button */}
      <button
        onClick={handleProcessClick}
        disabled={isLoading || !selectedFile || !className.trim()}
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
          'Create Class & Knowledge Graph'
        )}
      </button>
    </div>
  );
};

export default SyllabusInput;
