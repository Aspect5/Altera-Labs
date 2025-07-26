import * as d3 from 'd3';

// Main graph structure types
export interface GraphNode {
    id: string;
    label: string;
    // --- Kept from the new version ---
    type: 'concept' | 'skill' | 'competency'; 
}

export interface Edge {
    // --- Kept from the new version ---
    id: string; 
    label: 'is_prerequisite_for' | 'is_related_to';

    source: string;
    target: string;
    weight: number; // 💡 RESTORED: This is critical for the graph and matrix
}

// Student model and state
export interface KnowledgeState {
    [nodeId: string]: {
        mu: number;      // Mean (belief of mastery)
        sigma: number;   // Standard deviation (uncertainty)
    };
}

// --- RESTORED: Types for AI Mentor actions ---
export interface PracticeSuggestion {
    nodeId: string;
    label: string;
}

export interface Reassessment {
    nodeId: string;
    reasoning: string;
    newMu: number;
    newSigma: number;
}

// --- RESTORED: Types for D3 Visualization ---
// Centralizing these types is good practice
export interface D3Node extends GraphNode, d3.SimulationNodeDatum {
    mu: number;
    sigma: number;
}

export interface D3Link extends d3.SimulationLinkDatum<D3Node> {
    source: string | D3Node;
    target: string | D3Node;
    weight: number;
}

// --- KEPT: For the Socratic Verifier ---
export interface VerificationResult {
    verified: boolean;
    is_complete: boolean;
    feedback: string;
    new_proof_state: string;
    error: string | null;
}

// --- MERGED: Chat message with all features ---
export interface ChatMessage {
  role: 'user' | 'model' | 'system';
  content: string;
  suggestion?: PracticeSuggestion; // Restored for clarity
  practiceNodeId?: string;
  verification?: {
      verified: boolean;
      isComplete: boolean;
  };
}