import { Quiz, QuizAttemptResult } from '../types/quiz';

const API_BASE = '/api';

export async function uploadDocument(courseId: string, file: File): Promise<{ filePath: string }> {
  const form = new FormData();
  form.append('file', file);
  const res = await fetch(`${API_BASE}/courses/${courseId}/documents:upload`, {
    method: 'POST',
    body: form,
    credentials: 'include',
  });
  if (!res.ok) throw new Error('Upload failed');
  return res.json();
}

export async function ingestDocument(courseId: string, documentPath: string, force?: boolean): Promise<{ documentId: string; skipped?: boolean } | { skipped: boolean; documentId?: string }> {
  const res = await fetch(`${API_BASE}/courses/${courseId}/ingest`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ documentPath, force: !!force }),
    credentials: 'include',
  });
  if (!res.ok) throw new Error('Ingestion failed');
  return res.json();
}

export async function generateQuiz(courseId: string, studentId: string, params: { targetConcepts?: string[]; length?: number; difficulty?: number }): Promise<{ quizId: string }> {
  const res = await fetch(`${API_BASE}/courses/${courseId}/quizzes:generate`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ studentId, ...params }),
    credentials: 'include',
  });
  if (!res.ok) throw new Error('Quiz generation failed');
  return res.json();
}

export async function getQuiz(courseId: string, quizId: string): Promise<Quiz> {
  const res = await fetch(`${API_BASE}/courses/${courseId}/quizzes/${quizId}`, { credentials: 'include' });
  if (!res.ok) throw new Error('Failed to fetch quiz');
  return res.json();
}

export async function submitQuiz(studentId: string, quizId: string, responses: { itemId: string; response: any; isCorrect: boolean; latencyMs?: number }[]): Promise<QuizAttemptResult> {
  const res = await fetch(`${API_BASE}/students/${studentId}/quizzes/${quizId}:submit`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ responses }),
    credentials: 'include',
  });
  if (!res.ok) throw new Error('Submit failed');
  return res.json();
}


