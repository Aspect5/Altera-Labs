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

# --- AI Model Imports (Corrected for Vertex AI) ---
import vertexai
from vertexai.generative_models import GenerativeModel, Part, HarmCategory, HarmBlockThreshold

# --- Local Imports (Fallback) ---
try:
    from backend import local_llm_stub
except ImportError:
    import local_llm_stub

# --- AI Model and Configuration ---
# This logic is now updated for the Vertex AI SDK
PROJECT_ID = os.getenv("GOOGLE_CLOUD_PROJECT")
LOCATION = os.getenv("GOOGLE_CLOUD_LOCATION", "us-central1")
STABLE_MODEL_NAME = 'gemini-2.5-pro' # The model you want to use

try:
    vertexai.init(project=PROJECT_ID, location=LOCATION)
    logging.info("Successfully initialized Vertex AI client in socratic_auditor.")
    # Model object is now created on-demand in get_llm_response
except Exception as e:
    logging.critical(f"FATAL: Failed to initialize Vertex AI client: {e}")

# --- Constants ---
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')
BACKEND_DIR = Path(__file__).parent
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
LEAN_MAIN_FILE = LEAN_PROJECT_PATH / 'Main.lean'

# --- Core Functions ---

def get_llm_response(prompt: str, is_json: bool = False) -> str:
    """
    Gets a response from a Gemini model via the Vertex AI SDK.
    """
    try:
        model = GenerativeModel(STABLE_MODEL_NAME)
        
        # Vertex AI uses a different safety setting format
        safety_settings = {
            HarmCategory.HARM_CATEGORY_HARASSMENT: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_HATE_SPEECH: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_SEXUALLY_EXPLICIT: HarmBlockThreshold.BLOCK_NONE,
            HarmCategory.HARM_CATEGORY_DANGEROUS_CONTENT: HarmBlockThreshold.BLOCK_NONE,
        }
        
        # And a different response mime type format
        generation_config = {}
        if is_json:
            generation_config["response_mime_type"] = "application/json"
        
        response = model.generate_content(
            [prompt],
            generation_config=generation_config,
            safety_settings=safety_settings
        )
        
        if response and response.candidates and response.candidates[0].finish_reason.name == "SAFETY":
             raise ValueError("Response was blocked by safety settings.")

        if response and response.text:
            return response.text
        else:
            raise ValueError("Received an empty response from the API.")

    except Exception as e:
        logging.error(f"Vertex AI API call failed: {e}. Falling back to local stub.")
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