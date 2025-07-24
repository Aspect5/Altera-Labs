// frontend/types.ts

export interface GraphNode {
  id: string;
  label: string;
}

// FIXED: This is the correct shape for an Edge based on your components.
export interface Edge {
  source: string;
  target: string;
  weight: number;
}

export interface KnowledgeState {
  [nodeId: string]: {
    mu: number; // Mastery estimate (mean)
    sigma: number; // Uncertainty (standard deviation)
  };
}

export interface ChatMessage {
  role: 'user' | 'model' | 'system';
  content: string;
  suggestion?: {
    nodeId: string;
    label: string;
  };
  practiceNodeId?: string;
}

// D3 types for the simulation
export interface D3Node extends GraphNode {
    x?: number;
    y?: number;
    vx?: number;
    vy?: number;
    mu: number;
    sigma: number;
}

export interface D3Link {
    source: string | D3Node;
    target: string | D3Node;
    weight: number;
}
