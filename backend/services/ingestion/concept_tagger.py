from typing import Dict, List, Tuple


def cosine_similarity(a: List[float], b: List[float]) -> float:
    if not a or not b or len(a) != len(b):
        return 0.0
    dot = sum(x * y for x, y in zip(a, b))
    na = sum(x * x for x in a) ** 0.5
    nb = sum(y * y for y in b) ** 0.5
    if na == 0 or nb == 0:
        return 0.0
    return dot / (na * nb)


def tag_concepts_for_chunks(
    chunk_vectors: List[List[float]],
    concept_id_to_vector: Dict[str, List[float]],
    top_k: int = 3,
    min_similarity: float = 0.2,
) -> List[List[Tuple[str, float]]]:
    """
    Score each chunk against concept vectors and return top_k concept IDs with scores.
    """
    results: List[List[Tuple[str, float]]] = []
    concept_items = list(concept_id_to_vector.items())
    for vec in chunk_vectors:
        scored: List[Tuple[str, float]] = []
        for cid, cvec in concept_items:
            sim = cosine_similarity(vec, cvec)
            if sim >= min_similarity:
                scored.append((cid, sim))
        scored.sort(key=lambda x: x[1], reverse=True)
        results.append(scored[:top_k])
    return results


