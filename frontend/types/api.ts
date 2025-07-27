// API-related types
export interface StartSessionResponse {
  message: string;
  sessionId: string;
  proofCode: string;
  aiResponse: string;
}

export interface ChatResponse {
  aiResponse: string;
  proofCode: string;
  isVerified: boolean | null;
}

export interface FinalizeExamResponse {
  message: string;
  finalKnowledgeState: any;
}

export interface ExplainConceptResponse {
  explanation: string;
}

export interface AddClassResponse {
  classId: string;
  className: string;
  concepts: any[];
  edges: any[];
  solutionStatus: 'SOLVED' | 'FAILED' | 'SYLLABUS_BASED';
}

export interface VerifyStepResponse {
  verified: boolean;
  new_proof_state: string;
  feedback: string;
  is_complete: boolean;
  error: string | null;
}

// Enhanced Lean Verification API Types
export interface AutoSolveResponse {
  solved: boolean;
  final_proof: string;
  attempts: any[];
  attempts_used: number;
}

export interface DeveloperModeResponse {
  message: string;
  developer_mode: boolean;
  max_attempts: number;
}

export interface DeveloperLogsResponse {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  config: any;
  recent_logs: any[];
  attempt_logs: any[];
}

export interface HomeworkUploadResponse {
  file_name: string;
  theorems_found: number;
  proof_states: string[];
  solutions: any[];
} 