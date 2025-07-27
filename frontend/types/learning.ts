// Learning-related types
export interface LearningSession {
  id: string;
  startTime: Date;
  endTime?: Date;
  concepts: string[];
  progress: number;
  mode: 'homework' | 'exam' | 'practice';
}

export interface ConceptMastery {
  conceptId: string;
  mu: number; // Mastery level (0-1)
  sigma: number; // Uncertainty (0-1)
  lastUpdated: Date;
  practiceCount: number;
  correctCount: number;
}

export interface LearningPath {
  id: string;
  name: string;
  description: string;
  concepts: string[];
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  estimatedDuration: number; // in minutes
}

export interface PracticeProblem {
  id: string;
  conceptId: string;
  difficulty: number;
  question: string;
  solution: string;
  hints: string[];
  tags: string[];
}

export interface ExamResult {
  id: string;
  examId: string;
  score: number;
  maxScore: number;
  timeSpent: number;
  completedAt: Date;
  conceptScores: { [conceptId: string]: number };
} 