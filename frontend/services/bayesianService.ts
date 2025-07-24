import { GraphNode, Edge, KnowledgeState } from '../types';

// Constants for evidence
const CORRECT_EVIDENCE_MU = 1.0;
const INCORRECT_EVIDENCE_MU = 0.0;
const EVIDENCE_SIGMA = 0.1; // Low uncertainty in the evidence itself
const MASTERY_THRESHOLD = 0.85;

// Math approximation for the error function (erf)
const erf = (x: number): number => {
    // save the sign of x
    const sign = (x >= 0) ? 1 : -1;
    x = Math.abs(x);

    // constants
    const a1 = 0.254829592;
    const a2 = -0.284496736;
    const a3 = 1.421413741;
    const a4 = -1.453152027;
    const a5 = 1.061405429;
    const p = 0.3275911;

    // A&S formula 7.1.26
    const t = 1.0 / (1.0 + p * x);
    const y = 1.0 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * Math.exp(-x * x);
    return sign * y; // erf(-x) = -erf(x)
};

// Calculate Normal CDF
const normalCDF = (x: number, mu: number, sigma: number): number => {
    if (sigma < 1e-9) { // Handle cases with near-zero sigma
        return x < mu ? 0 : 1;
    }
    return 0.5 * (1 + erf((x - mu) / (sigma * Math.sqrt(2))));
};

// 4. Mastery Assessment
export const calculateMasteryProbability = (mu: number, sigma: number): number => {
    return 1 - normalCDF(MASTERY_THRESHOLD, mu, sigma);
};

export interface AdjacencyInfo {
    matrix: number[][];
    nodeOrder: string[];
    nodeIndexMap: Map<string, number>;
}

// Helper to build the adjacency matrix once
export const buildAdjacencyInfo = (nodes: GraphNode[], edges: Edge[]): AdjacencyInfo => {
    const nodeOrder = nodes.map(n => n.id);
    const nodeIndexMap = new Map(nodes.map((node, i) => [node.id, i]));
    const matrix = Array(nodes.length).fill(0).map(() => Array(nodes.length).fill(0));

    edges.forEach(edge => {
        const sourceIndex = nodeIndexMap.get(edge.source);
        const targetIndex = nodeIndexMap.get(edge.target);
        if (sourceIndex !== undefined && targetIndex !== undefined) {
            matrix[targetIndex][sourceIndex] = edge.weight;
        }
    });

    // Add identity for self-influence
    for(let i=0; i<nodes.length; i++) {
        matrix[i][i] = 1;
    }

    return { matrix, nodeOrder, nodeIndexMap };
};


// 2. Prior Estimation (for a single node)
export const calculatePriors = (
    targetNodeId: string, 
    knowledgeState: KnowledgeState, 
    adjacencyInfo: AdjacencyInfo
): { mu_prior: number; sigma_prior: number } => {
    
    const { matrix, nodeOrder, nodeIndexMap } = adjacencyInfo;
    const targetIndex = nodeIndexMap.get(targetNodeId);

    if (targetIndex === undefined) {
        throw new Error(`Node with id ${targetNodeId} not found in adjacency info.`);
    }

    let mu_prior = 0;
    let sigma_sq_prior = 0;
    
    const influenceVector = matrix[targetIndex]; // The row corresponding to the target node
    
    for (let j = 0; j < nodeOrder.length; j++) {
        const sourceNodeId = nodeOrder[j];
        const influenceWeight = influenceVector[j];
        if (influenceWeight > 0) {
            const sourceState = knowledgeState[sourceNodeId] || { mu: 0, sigma: 0.5 };
            mu_prior += influenceWeight * sourceState.mu;
            sigma_sq_prior += Math.pow(influenceWeight, 2) * Math.pow(sourceState.sigma, 2);
        }
    }

    mu_prior = Math.max(0, Math.min(1, mu_prior));

    return { mu_prior, sigma_prior: Math.sqrt(sigma_sq_prior) };
};

// 3. Bayesian Updating
export const performBayesianUpdate = (
    mu_prior: number, 
    sigma_prior: number, 
    isCorrect: boolean
): { mu_post: number; sigma_post: number } => {
    
    const mu_evidence = isCorrect ? CORRECT_EVIDENCE_MU : INCORRECT_EVIDENCE_MU;
    const sigma_evidence = EVIDENCE_SIGMA;

    const sigma_sq_prior = Math.pow(sigma_prior, 2);
    const sigma_sq_evidence = Math.pow(sigma_evidence, 2);

    // If prior uncertainty is effectively zero, we can't learn much more from propagation.
    // The new information comes almost entirely from the evidence.
    if (sigma_sq_prior < 1e-9) {
        return { mu_post: mu_evidence, sigma_post: sigma_evidence };
    }

    const precision_prior = 1 / sigma_sq_prior;
    const precision_evidence = 1 / sigma_sq_evidence;

    const mu_post = (mu_prior * precision_prior + mu_evidence * precision_evidence) / (precision_prior + precision_evidence);
    const sigma_sq_post = 1 / (precision_prior + precision_evidence);

    return {
        mu_post: Math.max(0, Math.min(1, mu_post)),
        sigma_post: Math.sqrt(sigma_sq_post)
    };
};
