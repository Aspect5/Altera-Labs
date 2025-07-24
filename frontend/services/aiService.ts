// frontend/services/aiService.ts

/**
 * This service module is the exclusive communication layer between the frontend
 * application and the backend Flask server. All HTTP requests to the API
 * should be centralized here. It replaces the old geminiService.ts.
 */

// --- Type Imports ---
import { GraphNode, Edge } from '../types';

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

interface AddClassResponse {
  classId: string;
  className: string;
  concepts: GraphNode[];
  edges: Edge[]; // Assuming backend will eventually provide this
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

/**
 * Uploads a syllabus file and class name to create a new class.
 * This function will be called by App.tsx to process the syllabus.
 * @param className The name of the class provided by the user.
 * @param syllabusFile The .pdf or .txt syllabus file.
 * @returns A promise that resolves with the new class data, including the extracted concepts.
 */
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

/**
 * --- NEW FUNCTION ---
 * Sends a selected concept and its surrounding context to the backend for an explanation.
 * @param concept The text selected by the user.
 * @param context The full message or text block from which the concept was selected.
 * @returns A promise that resolves with the AI's explanation.
 */
export const getConceptExplanation = async (concept: string, context: string): Promise<ExplainConceptResponse> => {
  const response = await fetch(`${API_BASE_URL}/explain_concept`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ concept, context }),
  });
  return handleResponse<ExplainConceptResponse>(response);
};

/**
 * Starts a new tutoring session on the backend.
 * @param mode The mode for the session, either 'homework' or 'exam'.
 * @returns A promise that resolves with the initial session data.
 */
export const startSession = async (mode: 'homework' | 'exam'): Promise<StartSessionResponse> => {
    const response = await fetch(`${API_BASE_URL}/start_session`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ mode }),
    });
    return handleResponse<StartSessionResponse>(response);
  };
  
  /**
   * Sends a user's message to the backend during an active session.
   * @param message The text of the user's message.
   * @returns A promise that resolves with the AI's response and updated proof state.
   */
  export const sendMessage = async (message: string): Promise<ChatResponse> => {
    const response = await fetch(`${API_BASE_URL}/chat`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ message }),
    });
    return handleResponse<ChatResponse>(response);
  };
