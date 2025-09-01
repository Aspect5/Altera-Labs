import json
import os
from math import sqrt
from pathlib import Path
from typing import Dict, Tuple

from config.quiz_bkg_config import DATA_ROOT, EVIDENCE_SIGMA


def _clamp01(x: float) -> float:
    return 0.0 if x < 0.0 else 1.0 if x > 1.0 else x


def _build_prior_for_concept(
    concept_id: str,
    knowledge_state: Dict[str, Dict[str, float]],
    adjacency: Dict[str, Dict[str, float]],
) -> Tuple[float, float]:
    # adjacency[target][source] = weight
    mu_prior = 0.0
    sigma_sq_prior = 0.0
    incoming = adjacency.get(concept_id, {})
    for source_id, weight in incoming.items():
        source_state = knowledge_state.get(source_id, {"mu": 0.3, "sigma": 0.5})
        mu_prior += weight * source_state["mu"]
        sigma_sq_prior += (weight * source_state["sigma"]) ** 2
    return _clamp01(mu_prior), sqrt(sigma_sq_prior)


def _fuse(mu_prior: float, sigma_prior: float, mu_e: float, sigma_e: float) -> Tuple[float, float]:
    if sigma_prior <= 1e-9:
        return _clamp01(mu_e), sigma_e
    tau_p = 1.0 / (sigma_prior ** 2)
    tau_e = 1.0 / (sigma_e ** 2)
    mu_post = (mu_prior * tau_p + mu_e * tau_e) / (tau_p + tau_e)
    sigma_post = sqrt(1.0 / (tau_p + tau_e))
    return _clamp01(mu_post), sigma_post


def load_course_edges(course_id: str) -> Dict[str, Dict[str, float]]:
    edges_path = Path(DATA_ROOT) / course_id / "edges.json"
    if edges_path.exists():
        try:
            edges_list = json.loads(edges_path.read_text(encoding="utf-8"))
            adjacency: Dict[str, Dict[str, float]] = {}
            for e in edges_list:
                src = e.get("source") or e.get("source_concept_id")
                tgt = e.get("target") or e.get("target_concept_id")
                w = float(e.get("weight", 0.0))
                if src and tgt:
                    adjacency.setdefault(tgt, {})[src] = w
            return adjacency
        except Exception:
            pass
    return {}


def load_or_init_student_state(course_id: str, student_id: str) -> Dict[str, Dict[str, float]]:
    bkg_dir = Path(DATA_ROOT) / course_id / "bkg"
    bkg_dir.mkdir(parents=True, exist_ok=True)
    state_path = bkg_dir / f"{student_id}.json"
    if state_path.exists():
        try:
            return json.loads(state_path.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {}


def persist_snapshot(course_id: str, student_id: str, state: Dict[str, Dict[str, float]]) -> None:
    bkg_dir = Path(DATA_ROOT) / course_id / "bkg"
    bkg_dir.mkdir(parents=True, exist_ok=True)
    state_path = bkg_dir / f"{student_id}.json"
    hist_path = bkg_dir / f"{student_id}.history.jsonl"
    state_path.write_text(json.dumps(state, indent=2), encoding="utf-8")
    with hist_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(state) + "\n")


def update_with_item(
    course_id: str,
    student_id: str,
    knowledge_state: Dict[str, Dict[str, float]],
    item_concepts: Dict[str, float],  # conceptId -> weight (coverage)
    is_correct: bool,
) -> Dict[str, Dict[str, float]]:
    adjacency = load_course_edges(course_id)
    mu_e = 1.0 if is_correct else 0.0
    sigma_e = EVIDENCE_SIGMA

    for cid, weight in item_concepts.items():
        mu_prior, sigma_prior = _build_prior_for_concept(cid, knowledge_state, adjacency)
        mu_post, sigma_post = _fuse(mu_prior, sigma_prior, mu_e, sigma_e)
        knowledge_state[cid] = {"mu": mu_post, "sigma": sigma_post}

    persist_snapshot(course_id, student_id, knowledge_state)
    return knowledge_state


