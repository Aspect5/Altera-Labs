// frontend/services/aiService.ts

/**
 * This service module is the exclusive communication layer between the frontend
 * application and the backend Flask server. All HTTP requests to the API
 * should be centralized here. It replaces the old geminiService.ts.
 */

// --- Type Imports ---
import { GraphNode, Edge, KnowledgeState } from '../types';

// --- API Configuration ---
const API_BASE_URL = 'http://localhost:5000/api';

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

export const addClassFromSyllabus = async (className: string, syllabusFile: File): Promise<AddClassResponse> => {
  const formData = new FormData();
  formData.append('className', className);
  formData.append('syllabus', syllabusFile);

  const response = await fetch(`${API_BASE_URL}/add_class`, {
    method: 'POST',
    body: formData,
  });
  return handleResponse<AddClassResponse>(response);
};

export const getConceptExplanation = async (concept: string, context: string): Promise<ExplainConceptResponse> => {
  const response = await fetch(`${API_BASE_URL}/explain_concept`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ concept, context }),
  });
  return handleResponse<ExplainConceptResponse>(response);
};

export const startSession = async (mode: 'homework' | 'exam'): Promise<StartSessionResponse> => {
    const response = await fetch(`${API_BASE_URL}/start_session`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ mode }),
    });
    return handleResponse<StartSessionResponse>(response);
  };
  
  export const sendMessage = async (message: string): Promise<ChatResponse> => {
    const response = await fetch(`${API_BASE_URL}/chat`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ message }),
    });
    return handleResponse<ChatResponse>(response);
  };

export const finalizeExam = async (knowledgeState: KnowledgeState): Promise<FinalizeExamResponse> => {
    const response = await fetch(`${API_BASE_URL}/finalize_exam`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ knowledgeState }),
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
    });
    return handleResponse<VerifyStepResponse>(response);
};