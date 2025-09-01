import json
import uuid
from pathlib import Path
from typing import Dict, Any, List

from config.quiz_bkg_config import DATA_ROOT, DEFAULT_MODEL


def _load_concepts(course_id: str) -> List[Dict[str, Any]]:
    concepts_path = Path(DATA_ROOT) / course_id / "concepts.json"
    if concepts_path.exists():
        try:
            return json.loads(concepts_path.read_text(encoding="utf-8"))
        except Exception:
            pass
    return []


def _load_chunks(course_id: str) -> List[Dict[str, Any]]:
    chunks_dir = Path(DATA_ROOT) / course_id / "documents"
    all_chunks: List[Dict[str, Any]] = []
    if not chunks_dir.exists():
        return []
    for doc_dir in chunks_dir.glob("*/chunks/chunks.jsonl"):
        with doc_dir.open("r", encoding="utf-8") as f:
            for line in f:
                try:
                    all_chunks.append(json.loads(line))
                except Exception:
                    continue
    return all_chunks


def _select_concepts(concepts: List[Dict[str, Any]], target_concepts: List[str] | None, length: int) -> List[str]:
    ids = [c.get("id") for c in concepts if c.get("id")]
    if target_concepts:
        ids = [cid for cid in ids if cid in target_concepts]
    return ids[: max(1, min(length, len(ids)))]


def generate_quiz(
    course_id: str,
    student_id: str,
    target_concepts: List[str] | None = None,
    length: int = 5,
    difficulty: float = 0.5,
) -> Dict[str, Any]:
    """
    Minimal stub quiz generator that samples chunks and creates basic MCQ items.
    Intended to be replaced with LLM-backed item writers.
    """
    quiz_id = str(uuid.uuid4())
    concepts = _load_concepts(course_id)
    chunks = _load_chunks(course_id)
    selected_cids = _select_concepts(concepts, target_concepts, length)

    # Fallback: if no concept metadata exists, synthesize concept ids from chunks
    if not selected_cids:
        num_items = max(1, min(length, len(chunks) if chunks else length))
        selected_cids = [f"concept_{i+1}" for i in range(num_items)]

    items: List[Dict[str, Any]] = []
    for i, cid in enumerate(selected_cids):
        # Find a supporting chunk text (round-robin)
        context_text = chunks[i % len(chunks)]["text"] if chunks else ""
        stem = f"Based on the material, which statement best reflects concept {cid}?"
        correct = "The statement directly aligned with the definition."
        distractors = [
            "A superficially similar but incorrect statement.",
            "An unrelated fact from the material.",
            "A common misconception about the concept.",
        ]
        item_id = str(uuid.uuid4())
        items.append(
            {
                "id": item_id,
                "item_type": "mcq",
                "payload": {
                    "stem": stem,
                    "options": [correct] + distractors,
                    "answer_index": 0,
                    "context": context_text,
                },
                "concept_coverage": [cid],
                "difficulty": difficulty,
            }
        )

    quiz_dir = Path(DATA_ROOT) / course_id / "quizzes" / quiz_id
    quiz_dir.mkdir(parents=True, exist_ok=True)
    (quiz_dir / "quiz.json").write_text(
        json.dumps({"id": quiz_id, "course_id": course_id, "blueprint": {}, "items": items}, indent=2),
        encoding="utf-8",
    )

    return {"quizId": quiz_id}


