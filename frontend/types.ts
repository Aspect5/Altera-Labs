
import * as d3 from 'd3';

export interface GraphNode {
  id: string;
  label: string;
}

export interface Edge {
  source: string; // node id
  target: string; // node id
  weight: number; // 0.0 to 1.0
}

export interface KnowledgeState {
  [nodeId: string]: {
    mu: number; // Mean skill estimate (0.0 to 1.0)
    sigma: number; // Uncertainty (e.g., 0.0 to 0.5, lower is more certain)
  };
}

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

export interface ChatMessage {
    role: 'user' | 'model' | 'system';
    content: string;
    suggestion?: PracticeSuggestion;
    practiceNodeId?: string; // Signals the UI to show correct/incorrect buttons
}


// For D3 simulation
export interface D3Node extends GraphNode, d3.SimulationNodeDatum {
    mu: number;
    sigma: number;
}

export interface D3Link extends d3.SimulationLinkDatum<D3Node> {
    source: string | D3Node;
    target: string | D3Node;
    weight: number;
}
