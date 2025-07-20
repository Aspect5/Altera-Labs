# backend/socratic_auditor.py

"""
This module serves as the primary interface to the AI model and the Lean 4
formal verifier. It is the "Socratic Auditor" responsible for translating
natural language, verifying tactics, and generating AI-driven pedagogical feedback.
"""
import os
import subprocess
import json
import logging
from pathlib import Path
from typing import Tuple

# --- AI Model Imports ---
from google import genai
from google.genai import types as genai_types

# --- Local Imports (Fallback) ---
try:
    from backend import local_llm_stub
except ImportError:
    import local_llm_stub

# --- AI Model and Configuration ---
# This logic is moved from app.py to here.
GEMINI_API_KEY = os.getenv('GEMINI_API_KEY')
GEMINI_CLIENT = None
STABLE_MODEL_NAME = 'gemini-1.5-flash'

if GEMINI_API_KEY:
    try:
        GEMINI_CLIENT = genai.Client(api_key=GEMINI_API_KEY)
        logging.info("Successfully initialized Gemini client in socratic_auditor.")
    except Exception as e:
        logging.critical(f"FATAL: Failed to initialize Gemini client in socratic_auditor: {e}")
else:
    logging.warning("WARNING: GEMINI_API_KEY not found. AI features will use local stub.")

# --- Constants ---
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')
BACKEND_DIR = Path(__file__).parent
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
LEAN_MAIN_FILE = LEAN_PROJECT_PATH / 'Main.lean'

# --- Core Functions ---

def get_llm_response(prompt: str, is_json: bool = False) -> str:
    """
    Gets a response from a Gemini model. This is the single point of contact
    for all AI interactions in the application.
    """
    if not GEMINI_CLIENT:
        logging.warning(f"Gemini client not available. Falling back to local stub for prompt: {prompt[:100]}...")
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)
    try:
        safety_settings = [
            genai_types.SafetySetting(category='HARM_CATEGORY_HARASSMENT', threshold='BLOCK_NONE'),
            genai_types.SafetySetting(category='HARM_CATEGORY_HATE_SPEECH', threshold='BLOCK_NONE'),
            genai_types.SafetySetting(category='HARM_CATEGORY_SEXUALLY_EXPLICIT', threshold='BLOCK_NONE'),
            genai_types.SafetySetting(category='HARM_CATEGORY_DANGEROUS_CONTENT', threshold='BLOCK_NONE'),
        ]
        
        config_args = {"safety_settings": safety_settings}
        if is_json:
            config_args["response_mime_type"] = "application/json"

        config = genai_types.GenerateContentConfig(**config_args)

        response = GEMINI_CLIENT.models.generate_content(
            model=STABLE_MODEL_NAME,
            contents=prompt,
            config=config
        )
        
        if response and response.prompt_feedback and response.prompt_feedback.block_reason:
            raise ValueError(f"Prompt was blocked: {response.prompt_feedback.block_reason.name}")
        
        if response and response.text:
            return response.text
        else:
            raise ValueError("Received an empty response from the API.")

    except Exception as e:
        logging.error(f"Gemini API call failed: {e}. Falling back to local stub.")
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)

def verify_step(session_id: str, proof_code: str, user_message: str) -> dict:
    """
    Orchestrates the verification of a single user step.
    1. Tries to generate a tactic from the user message.
    2. If successful, runs the tactic against the Lean verifier.
    3. If the verifier fails, uses the AI to generate a Socratic hint.
    """
    # This function now correctly returns a dictionary
    tactic_prompt = f"""
    Translate the user's natural language statement into a single, valid Lean 4 tactic.
    Current Proof State:
    ```lean
    {proof_code}
    ```
    User's statement: "{user_message}"
    
    Respond with valid JSON containing a single key "tactic". If no tactic can be generated, the value should be null.
    """
    try:
        tactic_response_str = get_llm_response(tactic_prompt, is_json=True)
        tactic_data = json.loads(tactic_response_str)
        lean_tactic = tactic_data.get("tactic")
    except (json.JSONDecodeError, ValueError) as e:
        logging.error(f"Failed to generate or parse tactic from LLM: {e}")
        lean_tactic = None

    if not lean_tactic:
        return {"new_proof_code": proof_code, "ai_response_text": "", "is_verified": None}

    is_success, verifier_output = run_lean_compiler(proof_code, lean_tactic)

    if is_success:
        new_proof_code = verifier_output
        return {"new_proof_code": new_proof_code, "ai_response_text": "Tactic verified successfully!", "is_verified": True}
    else:
        # Generate a Socratic hint from the error
        socratic_prompt = f"""
        A student's Lean 4 tactic failed. Be a helpful Socratic tutor. Explain the error conceptually and ask a guiding question.
        Current Proof State:
        ```lean
        {proof_code}
        ```
        Student's failed tactic: `{lean_tactic}`
        Compiler Error:
        ```
        {verifier_output}
        ```
        Your Socratic hint (do not give the code answer):
        """
        hint = get_llm_response(socratic_prompt)
        return {"new_proof_code": proof_code, "ai_response_text": hint, "is_verified": False}


def run_lean_compiler(current_proof: str, tactic: str) -> Tuple[bool, str]:
    """
    Runs the Lean compiler with the new tactic and returns (success, output).
    Output is the new proof state on success, or the error message on failure.
    """
    if 'sorry' not in current_proof:
        return False, "Proof is already complete."
        
    # Inject the new tactic
    new_proof_code_with_tactic = current_proof.replace('sorry', f'{tactic}\n  sorry', 1)

    try:
        LEAN_MAIN_FILE.write_text(new_proof_code_with_tactic, encoding='utf-8')
        
        process = subprocess.run(
            [LAKE_EXECUTABLE_PATH, 'build'], cwd=LEAN_PROJECT_PATH,
            capture_output=True, text=True, timeout=30, check=False
        )
        
        if process.returncode == 0:
            final_proof_code = new_proof_code_with_tactic.replace('\n  sorry', '')
            return True, final_proof_code
        else:
            return False, process.stderr
            
    except Exception as e:
        logging.error(f"Error running Lean compiler: {e}")
        return False, "An unexpected server error occurred during verification."