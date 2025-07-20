# backend/socratic_auditor.py

"""
This module implements the core logic for the "Socratic Verifier" loop,
as outlined in the Altera Labs strategic research documents. It is responsible for:
1.  Translating a user's natural language input into a Lean 4 tactic.
2.  Running the Lean 4 compiler to verify the tactic's logical soundness.
3.  Translating cryptic compiler errors into pedagogical, Socratic hints.

This architecture is a direct implementation of the "Hybrid Socratic Auditor"
strategy, separating the probabilistic task of tactic generation from the
deterministic task of formal verification.
"""

import os
import json
import logging
import subprocess
from pathlib import Path
from typing import Dict, Any, Tuple, Optional

# In a fully refactored app, these would be in separate modules.
# For now, we keep the necessary components here.
from google import genai
from google.genai import types as genai_types
from backend import prompts

# --- AI Model Configuration ---
# This setup is simplified for this module. A real application would have a
# centralized client management system.
GEMINI_CLIENT = None
if os.getenv('GEMINI_API_KEY'):
    GEMINI_CLIENT = genai.Client(api_key=os.getenv('GEMINI_API_KEY'))
STABLE_MODEL_NAME = 'gemini-2.5-flash'


def get_llm_response(prompt: str, is_json: bool = False) -> str:
    """Gets a response from a Gemini model."""
    if not GEMINI_CLIENT:
        logging.warning("GEMINI_CLIENT not initialized. Falling back to stub.")
        # This assumes a local_llm_stub.py exists at the same level
        from backend import local_llm_stub
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)
    
    config_args = {}
    if is_json:
        config_args["response_mime_type"] = "application/json"
    config = genai_types.GenerateContentConfig(**config_args)

    response = GEMINI_CLIENT.models.generate_content(
        model=STABLE_MODEL_NAME,
        contents=prompt,
        config=config
    )
    return response.text

# --- Constants ---
# This path is relative to the current file's location.
LEAN_PROJECT_PATH = Path(__file__).parent / 'lean_verifier'
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')

# A dedicated directory for temporary proof files to ensure session isolation.
TEMP_PROOFS_DIR = LEAN_PROJECT_PATH / 'TempProofs'
TEMP_PROOFS_DIR.mkdir(exist_ok=True)


def _run_lean_build(session_id: str, proof_code: str) -> Tuple[bool, str]:
    """
    Runs the Lean compiler on a temporary file for a specific session.
    """
    temp_proof_file = TEMP_PROOFS_DIR / f"{session_id}.lean"
    
    try:
        temp_proof_file.write_text(proof_code, encoding='utf-8')
        process = subprocess.run(
            [LAKE_EXECUTABLE_PATH, 'build', 'LeanVerifier'],
            cwd=LEAN_PROJECT_PATH,
            capture_output=True,
            text=True,
            timeout=45,
            check=False
        )

        if process.returncode == 0:
            return True, "Tactic verified successfully!"
        else:
            return False, process.stderr or "An unknown build error occurred."

    except subprocess.TimeoutExpired:
        logging.error(f"Lean build timed out for session {session_id}")
        return False, "Verification timed out. The tactic may be too complex or contain an error."
    except Exception as e:
        logging.error(f"An unexpected error occurred during Lean build for session {session_id}: {e}")
        return False, "A server error occurred during verification."
    finally:
        if temp_proof_file.exists():
            temp_proof_file.unlink()


def _generate_tactic(proof_state: str, user_message: str) -> Optional[str]:
    """
    Uses the LLM to translate a user's message into a Lean 4 tactic.
    """
    prompt = prompts.TACTIC_GENERATION_PROMPT.format(proof_state=proof_state, user_message=user_message)
    try:
        response_str = get_llm_response(prompt, is_json=True)
        tactic_data = json.loads(response_str)
        return tactic_data.get("tactic")
    except (json.JSONDecodeError, KeyError) as e:
        logging.error(f"Failed to parse tactic from LLM response: {e}")
        return None


def _generate_socratic_hint(proof_state: str, tactic: str, error_message: str) -> str:
    """
    Uses the LLM to translate a technical Lean error into a pedagogical hint.
    """
    prompt = prompts.SOCRATIC_HINT_PROMPT.format(
        proof_state=proof_state,
        tactic=tactic,
        error_message=error_message
    )
    return get_llm_response(prompt)


def verify_step(session_id: str, proof_code: str, user_message: str) -> Dict[str, Any]:
    """
    The main public function for the Socratic Auditor.
    """
    logging.info(f"Verifying step for session {session_id}: '{user_message}'")
    
    lean_tactic = _generate_tactic(proof_code, user_message)

    if not lean_tactic:
        logging.warning(f"Could not generate a tactic for: '{user_message}'")
        return {
            "is_verified": None,
            "ai_response_text": "I'm not sure how to turn that into a formal proof step. Could you try rephrasing it as a command or tactic?",
            "new_proof_code": proof_code
        }

    if 'sorry' not in proof_code:
         return {
            "is_verified": False,
            "ai_response_text": "The proof is already complete!",
            "new_proof_code": proof_code
        }
    
    proof_attempt_code = proof_code.replace('sorry', f'{lean_tactic}\n  sorry', 1)
    
    is_verified, result_msg = _run_lean_build(session_id, proof_attempt_code)
    
    if is_verified:
        final_proof_code = proof_attempt_code.replace('\n  sorry', '')
        return {
            "is_verified": True,
            "ai_response_text": result_msg,
            "new_proof_code": final_proof_code
        }
    else:
        socratic_hint = _generate_socratic_hint(proof_code, lean_tactic, result_msg)
        return {
            "is_verified": False,
            "ai_response_text": socratic_hint,
            "new_proof_code": proof_code
        }
