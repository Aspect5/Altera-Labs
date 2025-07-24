// frontend/types.ts

export interface GraphNode {
    id: string;
    label: string;
    type: 'concept' | 'skill' | 'competency';
}

export interface Edge {
    id: string;
    source: string;
    target: string;
    label: 'is_prerequisite_for' | 'is_related_to';
}

export interface KnowledgeState {
    [nodeId: string]: {
        mu: number;      // Mean (belief of mastery)
        sigma: number;   // Standard deviation (uncertainty)
    };
}

// --- NEW: For the Socratic Verifier ---
export interface VerificationResult {
    verified: boolean;
    is_complete: boolean;
    feedback: string;
    new_proof_state: string;
    error: string | null;
}

// --- CORRECTED: The existing ChatMessage interface, now updated ---
export interface ChatMessage {
  role: 'user' | 'model' | 'system';
  content: string;
  suggestion?: {
    nodeId: string;
    label: string;
  };
  practiceNodeId?: string;
  // --- NEW: Optional field for verification results ---
  verification?: {
      verified: boolean;
      isComplete: boolean;
  };
}