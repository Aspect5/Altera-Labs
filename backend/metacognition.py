# backend/metacognition.py

"""
This module implements the "Metacognitive Scaffolding" logic for the Altera Labs
AI Cognitive Partner. It has been refactored to act as the central
"Pedagogical Policy Engine."

Its primary responsibility is to orchestrate the AI's response by:
1.  Calling the `state_analyzer` to get a rich understanding of the student's
    current cognitive and affective state.
2.  Using that state to make a dynamic, pedagogically-sound decision about
    how to interact with the user, moving beyond a rigid state machine.
"""

import logging
from enum import Enum, auto
from typing import Dict, Any

# --- Local Application Imports ---
from backend import prompts
from backend import socratic_auditor
from backend import state_analyzer

class MetacognitiveStage(Enum):
    """Defines the high-level stages of the pedagogical loop."""
    PLANNING_GOAL = auto()
    PLANNING_STRATEGY = auto()
    MONITORING = auto()
    REFLECTION = auto()

def initialize_session_stage(session: Dict[str, Any]) -> None:
    """
    Sets the initial stage for a new session. The full session object
    is now created in app.py to act as the Student Model placeholder.
    """
    session['metacognitive_stage'] = MetacognitiveStage.PLANNING_GOAL
    logging.info(f"Session {session.get('session_id')} initialized. Stage: {session['metacognitive_stage']}.")

def process_message(session: Dict[str, Any], user_message: str) -> Dict[str, Any]:
    """
    Acts as the Pedagogical Policy Engine.
    """
    session_id = session.get("session_id", "unknown")
    state_analyzer.analyze_user_interaction(session, user_message)
    
    current_stage = session['metacognitive_stage']
    
    # --- DYNAMIC RESPONSE FOR AFFECTIVE STATES ---
    affective_state = session['student_model']['affective_state']
    if affective_state in ['FRUSTRATED', 'CONFUSED']:
        prompt = prompts.DYNAMIC_HELPER_PROMPT.format(
            proof_code=session['student_model']['current_proof'],
            user_message=f"The user seems {affective_state.lower()} and said: '{user_message}'"
        )
        ai_response = socratic_auditor.get_llm_response(prompt)
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof'],
            "is_verified": None
        }

    # --- Standard Stage Logic ---
    if current_stage == MetacognitiveStage.PLANNING_GOAL:
        session['metacognitive_stage'] = MetacognitiveStage.PLANNING_STRATEGY
        return {"ai_response_text": prompts.PLANNING_PROMPT_STRATEGY, "proof_code": session['student_model']['current_proof']}

    elif current_stage == MetacognitiveStage.PLANNING_STRATEGY:
        session['metacognitive_stage'] = MetacognitiveStage.MONITORING
        return {"ai_response_text": prompts.MONITORING_PROMPT_START, "proof_code": session['student_model']['current_proof']}

    elif current_stage == MetacognitiveStage.MONITORING:
        return handle_monitoring_stage(session, user_message)
    
    elif current_stage == MetacognitiveStage.REFLECTION:
        return {
            "ai_response_text": prompts.REFLECTION_PROMPT_CLOSING,
            "proof_code": session['student_model']['current_proof'],
            "is_verified": None
        }
    
    return {}


def handle_monitoring_stage(session: Dict[str, Any], user_message: str) -> Dict[str, Any]:
    """
    Manages the logic for the core problem-solving loop (Monitoring stage).
    """
    session_id = session.get("session_id", "unknown")
    
    result = socratic_auditor.verify_step(
        session_id=session_id,
        proof_code=session['student_model']['current_proof'],
        user_message=user_message
    )

    # --- DYNAMIC RESPONSE FOR TACTIC FAILURE ---
    if result.get('is_verified') is None and 'sorry' in result.get('new_proof_code', ''):
        logging.warning(f"Tactic generation failed for session {session_id}. Generating dynamic response.")
        
        # Instead of a static prompt, we now call the LLM to generate a response.
        prompt = prompts.DYNAMIC_HELPER_PROMPT.format(
            proof_code=session['student_model']['current_proof'],
            user_message=user_message
        )
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof'],
            "is_verified": None
        }

    # --- Success Path ---
    session['student_model']['current_proof'] = result['new_proof_code']
    if 'sorry' not in session['student_model']['current_proof']:
        logging.info(f"Proof completed for session {session_id}. Transitioning to REFLECTION.")
        session['metacognitive_stage'] = MetacognitiveStage.REFLECTION
        result['ai_response_text'] += "\n\n" + prompts.REFLECTION_PROMPT_SUCCESS
    
    return result