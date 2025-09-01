import os
import logging


def _env(name: str) -> str | None:
    return os.environ.get(name)


def initialize_vertex_genai_context() -> None:
    """
    Log the selected project/location for Vertex/GenAI usage.
    We rely on google-genai's Client to pick up ADC and env, so no explicit SDK init here.
    """
    project = _env("GOOGLE_CLOUD_PROJECT") or _env("VERTEX_AI_PROJECT_ID")
    location = _env("GOOGLE_CLOUD_LOCATION") or _env("VERTEX_AI_LOCATION") or "us-east1"
    if project:
        logging.info(f"Vertex/GenAI context: project={project}, location={location}")
    else:
        logging.warning("Vertex/GenAI: No project configured; cloud calls may warn or use fallbacks")


initialize_vertex_genai_context()


