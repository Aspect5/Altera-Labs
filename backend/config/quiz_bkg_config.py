import os


# Centralized configuration for Quiz + BKG features

# LLM model configuration
DEFAULT_MODEL = os.environ.get("DEFAULT_LLM_MODEL", "gemini-2.5-flash")

# Vertex/GenAI project/location (prefer GOOGLE_*; fallback to VERTEX_AI_*)
VERTEX_PROJECT = os.environ.get("GOOGLE_CLOUD_PROJECT") or os.environ.get("VERTEX_AI_PROJECT_ID")
VERTEX_LOCATION = os.environ.get("GOOGLE_CLOUD_LOCATION") or os.environ.get("VERTEX_AI_LOCATION")

# Embedding model
EMBEDDING_MODEL = os.environ.get("VERTEX_EMBEDDING_MODEL", "text-embedding-004")

# Chunking
CHUNK_SIZE = int(os.environ.get("QUIZ_BKG_CHUNK_SIZE", 1200))
CHUNK_OVERLAP = int(os.environ.get("QUIZ_BKG_CHUNK_OVERLAP", 200))

# Evidence / Updating parameters
EVIDENCE_SIGMA = float(os.environ.get("QUIZ_BKG_EVIDENCE_SIGMA", 0.1))
SLIP = float(os.environ.get("QUIZ_BKG_SLIP", 0.1))
GUESS = float(os.environ.get("QUIZ_BKG_GUESS", 0.2))

# Storage roots (filesystem MVP)
DATA_ROOT = os.path.join(os.path.dirname(os.path.dirname(__file__)), "data", "courses")

# Operational controls
EMBED_BATCH_SIZE = int(os.environ.get("QUIZ_BKG_EMBED_BATCH", 16))
EMBED_MAX_RETRIES = int(os.environ.get("QUIZ_BKG_EMBED_RETRIES", 3))
EMBED_RETRY_BASE_DELAY_SEC = float(os.environ.get("QUIZ_BKG_EMBED_RETRY_BASE", 1.5))


