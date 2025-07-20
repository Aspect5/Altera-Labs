# backend/metacognition.py

"""
This module implements the "Metacognitive Scaffolding" logic for the Altera Labs
AI Cognitive Partner, as described in the strategic research documents.

Its primary responsibility is to manage the user's session state and guide them
through the "Plan-Monitor-Reflect" cycle of expert problem-solving. This elevates
the tutor from a simple verifier to a cognitive coach.
"""

import logging
from enum import Enum, auto
from typing import Dict, Any

# These modules will be imported from our refactored backend package.
from backend import prompts
from backend import socratic_auditor

class MetacognitiveStage(Enum):
    """Defines the stages of the pedagogical loop."""
    PLANNING_GOAL = auto()      # User is defining the goal of the proof.
    PLANNING_STRATEGY = auto()  # User is outlining their initial strategy.
    MONITORING = auto()         # User is actively solving the proof, step-by-step.
    REFLECTION = auto()         # User is reflecting on the completed proof.

def initialize_session(session: Dict[str, Any]) -> Dict[str, Any]:
    """
    Initializes a new session with the first stage of the metacognitive loop.

    Args:
        session: The user's session dictionary.

    Returns:
        The AI's initial response dictionary for the planning phase.
    """
    session['metacognitive_stage'] = MetacognitiveStage.PLANNING_GOAL
    logging.info(f"Session {session.get('session_id')} initialized. Stage: {session['metacognitive_stage']}.")
    
    return {
        "ai_response_text": prompts.PLANNING_PROMPT_INITIAL,
        "proof_code": session['proof_code'],
        "is_verified": None
    }

def process_message(session: Dict[str, Any], user_message: str) -> Dict[str, Any]:
    """
    Processes a user's message based on their current metacognitive stage.

    This function acts as the central orchestrator, deciding whether to ask a
    planning question, delegate to the Socratic Auditor, or prompt for reflection.

    Args:
        session: The user's session dictionary, including the current stage.
        user_message: The text of the user's message.

    Returns:
        A dictionary containing the AI's response and any state changes.
    """
    session_id = session.get("session_id", "unknown")
    current_stage = session.get('metacognitive_stage', MetacognitiveStage.MONITORING)
    
    logging.info(f"Processing message for session {session_id}. Current stage: {current_stage}")

    if current_stage == MetacognitiveStage.PLANNING_GOAL:
        # User has described the goal, now ask for their strategy.
        session['metacognitive_stage'] = MetacognitiveStage.PLANNING_STRATEGY
        return {
            "ai_response_text": prompts.PLANNING_PROMPT_STRATEGY,
            "proof_code": session['proof_code'],
            "is_verified": None
        }

    elif current_stage == MetacognitiveStage.PLANNING_STRATEGY:
        # User has described their strategy, now transition to the main solving loop.
        session['metacognitive_stage'] = MetacognitiveStage.MONITORING
        # Acknowledge their plan and prompt for the first formal step.
        acknowledgement = (
            "That sounds like a solid plan. Let's get started!\n\n"
            "What is the first formal step or tactic you'd like to try?"
        )
        return {
            "ai_response_text": acknowledgement,
            "proof_code": session['proof_code'],
            "is_verified": None
        }

    elif current_stage == MetacognitiveStage.MONITORING:
        # The main problem-solving loop. Delegate to the Socratic Auditor.
        result = socratic_auditor.verify_step(
            session_id=session_id,
            proof_code=session['proof_code'],
            user_message=user_message
        )
        
        # Update the session's proof code with the result from the auditor.
        session['proof_code'] = result['new_proof_code']

        # Check for proof completion to transition to the next stage.
        if 'sorry' not in session['proof_code']:
            logging.info(f"Proof completed for session {session_id}. Transitioning to REFLECTION.")
            session['metacognitive_stage'] = MetacognitiveStage.REFLECTION
            # Append the reflection prompt to the final verification message.
            final_response = result['ai_response_text'] + "\n\n" + prompts.REFLECTION_PROMPT_SUCCESS
            result['ai_response_text'] = final_response
        
        return result

    elif current_stage == MetacognitiveStage.REFLECTION:
        # The proof is done. The user is now providing their reflections.
        # For now, just provide a simple closing message.
        return {
            "ai_response_text": "Thank you for sharing your thoughts. This reflection is a key part of becoming a better problem solver!",
            "proof_code": session['proof_code'],
            "is_verified": None
        }
        
    else:
        # Fallback for any unknown state.
        logging.error(f"Unknown metacognitive stage for session {session_id}: {current_stage}")
        return {
            "ai_response_text": "I seem to have lost my train of thought. Let's get back to the proof.",
            "proof_code": session['proof_code'],
            "is_verified": None
        }
