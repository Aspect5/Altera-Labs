import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App';
import './index.css';

try {
  console.log('[index.tsx] Initializing application...');
  
  const rootElement = document.getElementById('root');
  if (!rootElement) {
    throw new Error("Fatal: Could not find the 'root' element in the DOM. The application cannot be mounted.");
  }
  console.log('[index.tsx] Root element found.');
  
  const root = ReactDOM.createRoot(rootElement);
  console.log('[index.tsx] React root created.');

  root.render(
    <React.StrictMode>
      <App />
    </React.StrictMode>
  );
  console.log('[index.tsx] Application rendered successfully.');

} catch (error) {
  console.error('[index.tsx] A fatal error occurred during application startup:', error);
  const body = document.body;
  if (body) {
    body.innerHTML = `
      <div style="background-color: #1a202c; color: #cbd5e0; font-family: monospace; padding: 2rem; height: 100vh; display: flex; flex-direction: column; align-items: center; justify-content: center; box-sizing: border-box;">
        <h1 style="color: #e53e3e; font-size: 1.875rem; margin-bottom: 1rem; border-bottom: 2px solid #c53030; padding-bottom: 0.5rem;">Application Failed to Start</h1>
        <p style="margin-bottom: 2rem; color: #a0aec0;">A critical error prevented the application from loading. Please check the browser's developer console for details.</p>
        <pre style="background-color: #2d3748; padding: 1.5rem; border-radius: 0.5rem; max-width: 90%; overflow-x: auto; white-space: pre-wrap; word-break: break-all; border: 1px solid #4a5568;">${(error as Error).stack || (error as Error).message}</pre>
      </div>
    `;
  }
}