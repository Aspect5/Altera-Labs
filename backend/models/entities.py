from dataclasses import dataclass
from typing import List, Dict, Optional


@dataclass
class Course:
    id: str
    name: str
    term: Optional[str]
    metadata: Dict


@dataclass
class Concept:
    id: str
    course_id: str
    slug: str
    title: str
    description: str


@dataclass
class ConceptEdge:
    course_id: str
    source_concept_id: str
    target_concept_id: str
    weight: float


@dataclass
class Document:
    id: str
    course_id: str
    original_filename: str
    mime_type: str
    checksum: str
    bytes: int
    normalized_text_path: str


@dataclass
class Chunk:
    id: str
    document_id: str
    course_id: str
    idx: int
    text: str
    embedding_vector_id: Optional[str]
    concept_tags: List[str]


@dataclass
class Quiz:
    id: str
    course_id: str
    blueprint: Dict


@dataclass
class QuizItem:
    id: str
    quiz_id: str
    item_type: str  # 'mcq' | 'cloze' | 'short_answer'
    payload: Dict
    concept_coverage: List[str]
    difficulty: float


@dataclass
class QuizAttempt:
    id: str
    quiz_id: str
    student_id: str


@dataclass
class QuizResponse:
    id: str
    attempt_id: str
    item_id: str
    response: Dict
    is_correct: bool
    latency_ms: Optional[int]


@dataclass
class StudentConceptState:
    student_id: str
    course_id: str
    concept_id: str
    mu: float
    sigma: float


