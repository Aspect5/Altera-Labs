import hashlib
import json
import os
import uuid
from pathlib import Path
from typing import Dict, Any

import fitz

from config.quiz_bkg_config import DATA_ROOT
from services.ingestion.chunking import sliding_window_chunk
from services.embeddings.genai_embeddings import GenAIEmbeddingsClient


def _ensure_dirs(course_id: str, document_id: str) -> Dict[str, Path]:
    base = Path(DATA_ROOT) / course_id / "documents" / document_id
    paths = {
        "base": base,
        "raw": base / "raw",
        "normalized": base / "normalized",
        "chunks": base / "chunks",
    }
    for p in paths.values():
        p.mkdir(parents=True, exist_ok=True)
    return paths


def _normalize_to_text(file_path: Path) -> str:
    if file_path.suffix.lower() == ".pdf":
        with fitz.open(file_path) as doc:
            return "".join(page.get_text() for page in doc)
    else:
        return file_path.read_text(encoding="utf-8")


def _sha256_of_file(file_path: Path) -> str:
    h = hashlib.sha256()
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def ingest_document(course_id: str, uploaded_file_path: str, force: bool = False) -> Dict[str, Any]:
    """
    Filesystem MVP ingestion pipeline: normalize, chunk, embed, concept-tag (placeholder), persist.
    Returns documentId and paths.
    """
    document_id = str(uuid.uuid4())
    paths = _ensure_dirs(course_id, document_id)

    # Move/copy raw file into document folder
    src = Path(uploaded_file_path)
    raw_dst = paths["raw"] / src.name
    if src.resolve() != raw_dst.resolve():
        raw_dst.write_bytes(src.read_bytes())

    checksum = _sha256_of_file(raw_dst)

    metadata_path = Path(DATA_ROOT) / course_id / "metadata.json"
    course_meta: Dict[str, Any] = {}
    if metadata_path.exists():
        course_meta = json.loads(metadata_path.read_text(encoding="utf-8"))

    # Idempotency: check if a document with same checksum exists
    if not force:
        existing_docs = course_meta.get("documents", [])
        for d in existing_docs:
            if d.get("checksum") == checksum:
                return {"documentId": d.get("id"), "skipped": True}

    # Normalize
    text = _normalize_to_text(raw_dst)
    normalized_txt_path = paths["normalized"] / "text.txt"
    normalized_txt_path.write_text(text, encoding="utf-8")

    # Chunk
    chunks = sliding_window_chunk(text)

    # Embeddings
    embedder = GenAIEmbeddingsClient()
    vectors = embedder.embed_texts(chunks)

    # Persist chunks.jsonl
    chunks_jsonl = paths["chunks"] / "chunks.jsonl"
    with chunks_jsonl.open("w", encoding="utf-8") as f:
        for idx, (chunk_text, vec) in enumerate(zip(chunks, vectors)):
            record = {
                "id": str(uuid.uuid4()),
                "document_id": document_id,
                "course_id": course_id,
                "idx": idx,
                "text": chunk_text,
                "embedding_vector_id": None,
                "embedding": vec,
                "concept_tags": [],
            }
            f.write(json.dumps(record) + "\n")

    # Update course metadata
    course_dir = Path(DATA_ROOT) / course_id
    course_dir.mkdir(parents=True, exist_ok=True)
    documents_meta = course_meta.get("documents", [])
    documents_meta.append(
        {
            "id": document_id,
            "original_filename": src.name,
            "checksum": checksum,
            "bytes": os.path.getsize(raw_dst),
            "normalized_text_path": str(normalized_txt_path),
        }
    )
    course_meta["documents"] = documents_meta
    metadata_path.write_text(json.dumps(course_meta, indent=2), encoding="utf-8")

    return {"documentId": document_id, "skipped": False}


