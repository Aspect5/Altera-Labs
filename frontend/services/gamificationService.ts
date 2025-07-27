import { GamificationState, Achievement } from '../types';

// Achievement definitions
export const ACHIEVEMENTS: Achievement[] = [
  {
    id: 'first_proof',
    name: 'First Steps',
    description: 'Complete your first proof',
    icon: '🎯',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'streak_3',
    name: 'Consistent Learner',
    description: 'Maintain a 3-day learning streak',
    icon: '🔥',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'streak_7',
    name: 'Week Warrior',
    description: 'Maintain a 7-day learning streak',
    icon: '⚡',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'master_concept',
    name: 'Concept Master',
    description: 'Master 5 concepts (μ ≥ 0.9)',
    icon: '🧠',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'proof_expert',
    name: 'Proof Expert',
    description: 'Complete 10 proofs',
    icon: '📐',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'flow_state',
    name: 'Flow State',
    description: 'Spend 30 minutes in focused learning',
    icon: '🌊',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'helpful_peer',
    name: 'Helpful Peer',
    description: 'Help another student understand a concept',
    icon: '🤝',
    unlockedAt: null,
    progress: 0
  },
  {
    id: 'persistence',
    name: 'Persistence Pays',
    description: 'Work through 3 difficult problems',
    icon: '💪',
    unlockedAt: null,
    progress: 0
  }
];

// Points for different actions
export const POINTS = {
  PROOF_COMPLETED: 50,
  CONCEPT_MASTERED: 25,
  STREAK_DAY: 10,
  FLOW_STATE_MINUTE: 2,
  HELPING_OTHERS: 15,
  DIFFICULT_PROBLEM: 30,
  SESSION_COMPLETED: 20
};

class GamificationService {
  private state: GamificationState;

  constructor() {
    this.state = this.loadState();
  }

  private loadState(): GamificationState {
    const saved = localStorage.getItem('gamificationState');
    if (saved) {
      const parsed = JSON.parse(saved);
      return {
        ...parsed,
        achievements: parsed.achievements.map((a: any) => ({
          ...a,
          unlockedAt: a.unlockedAt ? new Date(a.unlockedAt) : null
        }))
      };
    }

    return {
      points: 0,
      level: 1,
      achievements: ACHIEVEMENTS.map(a => ({ ...a })),
      streak: 0
    };
  }

  private saveState(): void {
    localStorage.setItem('gamificationState', JSON.stringify(this.state));
  }

  private calculateLevel(points: number): number {
    return Math.floor(points / 1000) + 1;
  }

  private checkAchievements(): Achievement[] {
    const newlyUnlocked: Achievement[] = [];

    this.state.achievements.forEach(achievement => {
      if (achievement.unlockedAt) return; // Already unlocked

      let shouldUnlock = false;
      let progress = 0;

      switch (achievement.id) {
        case 'first_proof':
          progress = this.state.points >= POINTS.PROOF_COMPLETED ? 1 : 0;
          shouldUnlock = progress >= 1;
          break;

        case 'streak_3':
          progress = Math.min(this.state.streak / 3, 1);
          shouldUnlock = this.state.streak >= 3;
          break;

        case 'streak_7':
          progress = Math.min(this.state.streak / 7, 1);
          shouldUnlock = this.state.streak >= 7;
          break;

        case 'master_concept':
          // This would need to be updated based on knowledge state
          progress = 0;
          shouldUnlock = false;
          break;

        case 'proof_expert':
          // This would need to be tracked separately
          progress = 0;
          shouldUnlock = false;
          break;

        case 'flow_state':
          // This would need to be tracked separately
          progress = 0;
          shouldUnlock = false;
          break;

        case 'helpful_peer':
          // This would need to be triggered manually
          progress = 0;
          shouldUnlock = false;
          break;

        case 'persistence':
          // This would need to be tracked separately
          progress = 0;
          shouldUnlock = false;
          break;
      }

      if (shouldUnlock) {
        achievement.unlockedAt = new Date();
        achievement.progress = 1;
        newlyUnlocked.push(achievement);
      } else {
        achievement.progress = progress;
      }
    });

    return newlyUnlocked;
  }

  // Public methods
  public getState(): GamificationState {
    return { ...this.state };
  }

  public addPoints(amount: number, reason: string): Achievement[] {
    this.state.points += amount;
    this.state.level = this.calculateLevel(this.state.points);
    
    const newlyUnlocked = this.checkAchievements();
    this.saveState();
    
    console.log(`🎯 +${amount} points for ${reason}`);
    return newlyUnlocked;
  }

  public updateStreak(days: number): Achievement[] {
    this.state.streak = days;
    const newlyUnlocked = this.checkAchievements();
    this.saveState();
    return newlyUnlocked;
  }

  public unlockAchievement(achievementId: string): Achievement | null {
    const achievement = this.state.achievements.find(a => a.id === achievementId);
    if (achievement && !achievement.unlockedAt) {
      achievement.unlockedAt = new Date();
      achievement.progress = 1;
      this.saveState();
      return achievement;
    }
    return null;
  }

  public updateAchievementProgress(achievementId: string, progress: number): void {
    const achievement = this.state.achievements.find(a => a.id === achievementId);
    if (achievement && !achievement.unlockedAt) {
      achievement.progress = Math.min(progress, 1);
      if (progress >= 1) {
        achievement.unlockedAt = new Date();
      }
      this.saveState();
    }
  }

  // Convenience methods for common actions
  public proofCompleted(): Achievement[] {
    return this.addPoints(POINTS.PROOF_COMPLETED, 'completing a proof');
  }

  public conceptMastered(): Achievement[] {
    return this.addPoints(POINTS.CONCEPT_MASTERED, 'mastering a concept');
  }

  public sessionCompleted(): Achievement[] {
    return this.addPoints(POINTS.SESSION_COMPLETED, 'completing a session');
  }

  public flowStateMinute(): Achievement[] {
    return this.addPoints(POINTS.FLOW_STATE_MINUTE, 'flow state minute');
  }

  public helpedOthers(): Achievement[] {
    return this.addPoints(POINTS.HELPING_OTHERS, 'helping others');
  }

  public difficultProblem(): Achievement[] {
    return this.addPoints(POINTS.DIFFICULT_PROBLEM, 'solving difficult problem');
  }

  public reset(): void {
    this.state = {
      points: 0,
      level: 1,
      achievements: ACHIEVEMENTS.map(a => ({ ...a })),
      streak: 0
    };
    this.saveState();
  }
}

// Export singleton instance
export const gamificationService = new GamificationService(); 