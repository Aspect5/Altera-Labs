// frontend/src/pages/SetupPage.tsx

import React from 'react';
import ClassCreationPanel from '../../components/ClassCreationPanel';

interface SetupPageProps {
  className: string;
  setClassName: (name: string) => void;
  onCreateClass: (className: string, syllabusFile: File | null, homeworkFile: File | null) => void;
  isLoading: boolean;
  error: string | null;
}

const SetupPage: React.FC<SetupPageProps> = ({
  className,
  setClassName,
  onCreateClass,
  isLoading,
  error,
}) => {
  return (
    <div className="grid grid-cols-1 lg:grid-cols-12 gap-6 lg:gap-8 h-full">
      <div className="lg:col-span-4 flex flex-col gap-6">
        <ClassCreationPanel
          className={className}
          setClassName={setClassName}
          onCreateClass={onCreateClass}
          isLoading={isLoading}
        />
      </div>
      <div className="lg:col-span-8 space-y-6 flex flex-col">
        {error && (
          <div className="bg-red-900/50 border border-red-700 text-red-300 p-4 rounded-lg">
            <p className="font-bold">An Error Occurred</p>
            <p>{error}</p>
          </div>
        )}
        <div className="flex h-full items-center justify-center rounded-lg bg-slate-800/50 p-4 text-center shadow-inner">
          <div>
            <h3 className="text-xl font-semibold text-cyan-400">Welcome to Your AI Cognitive Partner</h3>
            <p className="mt-2 text-slate-400">Create a class on the left to begin your personalized learning journey.</p>
          </div>
        </div>
      </div>
    </div>
  );
};

export default SetupPage; 