# backend/state_analyzer.py (NEW FILE)

"""
This module is responsible for analyzing the user's interaction to update
the student model. It will eventually house the Affective Computing and
Knowledge Tracing models.
"""
from typing import Dict, Any

def analyze_user_interaction(session: Dict[str, Any], user_message: str) -> None:
    """
    Analyzes the latest user message and interaction data to update the
    student model with inferred affective state and other metrics.

    Args:
        session: The user's full session object.
        user_message: The text of the user's message.
    """
    # --- Affective Computing Placeholder ---
    # For now, a simple rule-based check. This will be replaced by a
    # sophisticated ML model analyzing interaction logs.
    if "don't get it" in user_message.lower() or "confused" in user_message.lower():
        session['student_model']['affective_state'] = 'CONFUSED'
    elif "hate this" in user_message.lower() or "frustrating" in user_message.lower():
        session['student_model']['affective_state'] = 'FRUSTRATED'
    else:
        session['student_model']['affective_state'] = 'NEUTRAL'
        
    # --- Knowledge Component (KC) Tagger Placeholder ---
    # This will eventually call the BKT model within the Dynamic Knowledge Graph.
    # For now, it does nothing.
    pass