// Re-export all types from the modular type system
export * from './types';

// Legacy types that need to be preserved for backward compatibility
import * as d3 from 'd3';
import { GraphNode } from './types';

export interface D3Node extends GraphNode, d3.SimulationNodeDatum {
    mu: number;
    sigma: number;
}

export interface D3Link extends d3.SimulationLinkDatum<D3Node> {
    source: string | D3Node;
    target: string | D3Node;
    weight: number;
}

export interface VerificationResult {
    verified: boolean;
    is_complete: boolean;
    feedback: string;
    new_proof_state: string;
    error: string | null;
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

export interface UserPreferences {
    theme: 'default' | 'nature' | 'space' | 'ocean';
    notifications: boolean;
    autoSave: boolean;
}

export interface UserInsight {
    id: string;
    type: 'learning_pattern' | 'preference' | 'strength' | 'weakness';
    content: string;
    confidence: number; // 0-1
    createdAt: Date;
}