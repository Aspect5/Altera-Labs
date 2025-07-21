
import React from 'react';

interface DiagnosticTracePanelProps {
    trace: string[];
}

const DiagnosticTracePanel: React.FC<DiagnosticTracePanelProps> = ({ trace }) => {
    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <h2 className="text-xl font-semibold text-cyan-400 mb-3">Diagnostic Process Trace</h2>
            <p className="text-sm text-slate-400 mb-3">A step-by-step log of the AI's reasoning process for the last diagnosis.</p>
            <div className="bg-slate-900 p-4 rounded-md text-slate-300 font-mono text-xs max-h-80 overflow-y-auto">
                <ol className="list-decimal list-inside space-y-2">
                    {trace.map((step, index) => (
                        <li key={index}>
                            <span className={step.startsWith('ERROR') ? 'text-red-400' : 'text-slate-300'}>
                                {step}
                            </span>
                        </li>
                    ))}
                </ol>
            </div>
        </div>
    );
};

export default DiagnosticTracePanel;
