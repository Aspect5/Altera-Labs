// Gamification-related types
export interface GamificationConfig {
  pointsPerAction: { [action: string]: number };
  levelThresholds: number[];
  achievementDefinitions: AchievementDefinition[];
}

export interface AchievementDefinition {
  id: string;
  name: string;
  description: string;
  icon: string;
  condition: AchievementCondition;
  points: number;
}

export interface AchievementCondition {
  type: 'points' | 'streak' | 'concept_mastery' | 'session_completion';
  value: number;
  operator: 'gte' | 'eq' | 'lte';
}

export interface UserProgress {
  userId: string;
  totalPoints: number;
  currentLevel: number;
  experiencePoints: number;
  achievements: string[];
  streak: number;
  lastActivity: Date;
} 