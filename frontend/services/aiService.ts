// frontend/services/aiService.ts

/**
 * This service module is the exclusive communication layer between the frontend
 * application and the backend Flask server. All HTTP requests to the API
 * should be centralized here. It replaces the old geminiService.ts.
 */

// --- Type Imports ---
import { GraphNode, Edge, KnowledgeState } from '../types';

// --- API Configuration ---
const API_BASE_URL = '/api';

// --- Type Definitions for API Responses ---
interface StartSessionResponse {
  message: string;
  sessionId: string;
  proofCode: string;
  aiResponse: string;
}

interface ChatResponse {
  aiResponse: string;
  proofCode: string;
  isVerified: boolean | null;
}

interface FinalizeExamResponse {
    message: string;
    finalKnowledgeState: KnowledgeState;
}

interface ExplainConceptResponse {
  explanation: string;
}

interface AddClassResponse {
  classId: string;
  className: string;
  concepts: GraphNode[];
  edges: Edge[]; // Assuming backend will eventually provide this
  solutionStatus: 'SOLVED' | 'FAILED' | 'SYLLABUS_BASED'; // For Proving Agent feedback
}

// --- NEW: Type definition for the verifier service ---
interface VerifyStepResponse {
    verified: boolean;
    new_proof_state: string;
    feedback: string;
    is_complete: boolean;
    error: string | null;
}


// --- Generic API Error Handling ---
class ApiError extends Error {
  constructor(message: string, public status: number, public data: any) {
    super(message);
    this.name = 'ApiError';
  }
}

async function handleResponse<T>(response: Response): Promise<T> {
  const data = await response.json();
  if (!response.ok) {
    const errorMessage = data.error || `HTTP error! status: ${response.status}`;
    console.error("API Error:", errorMessage, "Data:", data);
    throw new ApiError(errorMessage, response.status, data);
  }
  return data;
}

// --- Service Functions ---

// UPDATED: Renamed and modified to handle both syllabus and homework
export const createClass = async (
  className: string,
  syllabusFile: File | null,
  homeworkFile: File | null
): Promise<AddClassResponse> => {
  const formData = new FormData();
  formData.append('className', className);
  if (syllabusFile) {
    formData.append('syllabus', syllabusFile);
  }
  if (homeworkFile) {
    formData.append('homework', homeworkFile);
  }

  const response = await fetch(`${API_BASE_URL}/add_class`, {
    method: 'POST',
    body: formData,
    credentials: 'include',
  });
  return handleResponse<AddClassResponse>(response);
};

export const getConceptExplanation = async (concept: string, context: string): Promise<ExplainConceptResponse> => {
  const response = await fetch(`${API_BASE_URL}/explain_concept`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ concept, context }),
    credentials: 'include',
  });
  return handleResponse<ExplainConceptResponse>(response);
};

export const startSession = async (mode: 'homework' | 'exam'): Promise<StartSessionResponse> => {
    const response = await fetch(`${API_BASE_URL}/start_session`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ mode }),
      credentials: 'include',
    });
    return handleResponse<StartSessionResponse>(response);
  };
  
  export const sendMessage = async (message: string): Promise<ChatResponse> => {
    console.log('aiService: Sending message to /api/chat:', message);
    const response = await fetch(`${API_BASE_URL}/chat`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ message }),
      credentials: 'include',
    });
    console.log('aiService: Raw response status:', response.status);
    const data = await handleResponse<ChatResponse>(response);
    console.log('aiService: Parsed response data:', data);
    return data;
  };

export const finalizeExam = async (knowledgeState: KnowledgeState): Promise<FinalizeExamResponse> => {
    const response = await fetch(`${API_BASE_URL}/finalize_exam`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ knowledgeState }),
        credentials: 'include',
    });
    return handleResponse<FinalizeExamResponse>(response);
};

/**
 * --- NEW FUNCTION ---
 * Sends a natural language proof step to the backend for verification by Lean.
 * @param proof_state The current Lean code of the proof.
 * @param step The natural language step from the user.
 * @returns A promise that resolves with the verification result.
 */
export const verifyProofStep = async (proof_state: string, step: string): Promise<VerifyStepResponse> => {
    const response = await fetch(`${API_BASE_URL}/verify_step`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ proof_state, step }),
        credentials: 'include',
    });
    return handleResponse<VerifyStepResponse>(response);
};

// ======================================================================================
// == NEW: Enhanced Lean Verification API Functions
// ======================================================================================

interface AutoSolveResponse {
    solved: boolean;
    final_proof: string;
    attempts: any[];
    attempts_used: number;
}

interface DeveloperModeResponse {
    message: string;
    developer_mode: boolean;
    max_attempts: number;
}

interface DeveloperLogsResponse {
    developer_mode: boolean;
    max_auto_solve_attempts: number;
    config: any;
    recent_logs: any[];
    attempt_logs: any[];
}

interface HomeworkUploadResponse {
    file_name: string;
    theorems_found: number;
    proof_states: string[];
    solutions: any[];
}

/**
 * Trigger AI auto-solving of a proof with configurable attempts.
 * @param proof_state The current Lean proof state.
 * @param max_attempts Optional maximum number of attempts.
 * @returns A promise that resolves with the auto-solve result.
 */
export const autoSolveProof = async (proof_state: string, max_attempts?: number): Promise<AutoSolveResponse> => {
    const response = await fetch(`${API_BASE_URL}/auto_solve_proof`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ proof_state, max_attempts }),
        credentials: 'include',
    });
    return handleResponse<AutoSolveResponse>(response);
};

/**
 * Toggle developer mode on/off.
 * @param enabled Whether to enable developer mode.
 * @param max_attempts Optional maximum number of auto-solve attempts.
 * @returns A promise that resolves with the developer mode status.
 */
export const toggleDeveloperMode = async (enabled: boolean, max_attempts?: number): Promise<DeveloperModeResponse> => {
    const response = await fetch(`${API_BASE_URL}/developer_mode`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ enabled, max_attempts }),
        credentials: 'include',
    });
    return handleResponse<DeveloperModeResponse>(response);
};

/**
 * Get developer mode logs and configuration.
 * @returns A promise that resolves with the developer logs.
 */
export const getDeveloperLogs = async (): Promise<DeveloperLogsResponse> => {
    const response = await fetch(`${API_BASE_URL}/developer_logs`, {
        method: 'GET',
        credentials: 'include',
    });
    return handleResponse<DeveloperLogsResponse>(response);
};

export const clearDeveloperLogs = async (): Promise<{message: string}> => {
    const response = await fetch(`${API_BASE_URL}/developer_logs/clear`, {
        method: 'POST',
        credentials: 'include',
    });
    return handleResponse<{message: string}>(response);
};

/**
 * Upload homework file for enhanced processing with auto-solve.
 * @param file The homework file to upload.
 * @returns A promise that resolves with the homework processing result.
 */
export const uploadHomework = async (file: File): Promise<HomeworkUploadResponse> => {
    const formData = new FormData();
    formData.append('file', file);

    const response = await fetch(`${API_BASE_URL}/upload_homework`, {
        method: 'POST',
        body: formData,
        credentials: 'include',
    });
    return handleResponse<HomeworkUploadResponse>(response);
};