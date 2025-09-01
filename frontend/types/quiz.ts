export type QuizItemType = 'mcq' | 'cloze' | 'short_answer';

export interface QuizItem {
  id: string;
  item_type: QuizItemType; // backend field name
  payload: any; // question, options, answers, hints
  concept_coverage: string[]; // concept ids
  difficulty: number; // 0..1
}

export interface Quiz {
  id: string;
  course_id: string;
  items: QuizItem[];
  blueprint: Record<string, any>;
}

export interface QuizAttemptResponse {
  itemId: string;
  response: any;
  isCorrect: boolean;
  latencyMs?: number;
}

export interface QuizAttemptResult {
  attemptId: string;
  updatedBkg: Record<string, { mu: number; sigma: number }>;
}


