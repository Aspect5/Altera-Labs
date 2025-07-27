// Component-related types
export interface GraphNode {
  id: string;
  label: string;
  description?: string;
  difficulty?: number;
  prerequisites?: string[];
  mu?: number;
  sigma?: number;
}

export interface Edge {
  source: string;
  target: string;
  weight: number;
  type?: string;
}

export interface KnowledgeState {
  [nodeId: string]: {
    mu: number;
    sigma: number;
  };
}

export interface ChatMessage {
  role: 'user' | 'model' | 'system';
  content: string;
  timestamp?: Date;
  suggestion?: {
    nodeId: string;
    label: string;
  };
  practiceNodeId?: string;
  verification?: {
    verified: boolean;
    isComplete: boolean;
  };
}

export interface ClassSummary {
  id: string;
  name: string;
  healthScore: number;
  lastSession?: string;
  conceptCount: number;
  conceptsMastered: number;
  totalConcepts: number;
  plantState: 'flourishing' | 'healthy' | 'wilting' | 'struggling';
  createdAt: Date;
  updatedAt: Date;
}

export interface QuickStats {
  totalConceptsMastered: number;
  currentStreak: number;
  flowStateTime: number;
  totalClasses: number;
  averageHealthScore: number;
}

export interface ClassData {
  id: string;
  name: string;
  healthScore: number;
  lastSession?: string;
  nodes: GraphNode[];
  edges: Edge[];
  knowledgeState: KnowledgeState;
}

export interface GamificationState {
  points: number;
  level: number;
  achievements: Achievement[];
  streak: number;
}

export interface Achievement {
  id: string;
  name: string;
  description: string;
  unlocked: boolean;
  unlockedAt?: Date;
  icon?: string;
} 