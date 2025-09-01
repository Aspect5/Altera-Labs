import logging
from typing import List

from config.quiz_bkg_config import (
    VERTEX_PROJECT,
    VERTEX_LOCATION,
    EMBEDDING_MODEL,
)


class GenAIEmbeddingsClient:
    """
    Embeddings client using the Google Gen AI SDK routed via Vertex AI when
    project/location are provided by environment.
    """

    def __init__(self) -> None:
        try:
            from google import genai  # type: ignore
            if VERTEX_PROJECT and VERTEX_LOCATION:
                self._client = genai.Client(vertexai=True, project=VERTEX_PROJECT, location=VERTEX_LOCATION)
            else:
                self._client = genai.Client()
            logging.info(
                f"GenAIEmbeddingsClient ready: project={VERTEX_PROJECT}, location={VERTEX_LOCATION}, model={EMBEDDING_MODEL}"
            )
        except Exception as e:
            logging.warning(f"GenAI SDK init failed, using deterministic fallback embeddings: {e}")
            self._client = None

    def embed_texts(self, texts: List[str]) -> List[List[float]]:
        if not texts:
            return []
        if self._client is None:
            return [self._fallback_embedding(t) for t in texts]

        vectors: List[List[float]] = []
        for t in texts:
            try:
                # google-genai expects 'contents', not 'input'
                resp = self._client.models.embed_content(model=EMBEDDING_MODEL, contents=t)
                emb_list = None
                if hasattr(resp, "embeddings") and resp.embeddings:
                    emb_list = resp.embeddings
                elif isinstance(resp, dict) and resp.get("embeddings"):
                    emb_list = resp["embeddings"]
                if emb_list:
                    first = emb_list[0] if isinstance(emb_list, list) else emb_list
                    values = getattr(first, "values", None) or (first.get("values") if isinstance(first, dict) else None)
                    if values:
                        vectors.append(list(values))
                        continue
            except Exception as e:
                logging.warning(f"GenAI embed failed, falling back for one text: {e}")
            vectors.append(self._fallback_embedding(t))
        return vectors

    @staticmethod
    def _fallback_embedding(text: str, dim: int = 64) -> List[float]:
        h = abs(hash(text))
        vec = []
        for i in range(dim):
            vec.append(((h >> (i % 32)) & 0xFFFF) / 65535.0)
        return vec


