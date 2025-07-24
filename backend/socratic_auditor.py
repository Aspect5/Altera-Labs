# backend/socratic_auditor.py

"""
This module is the core of the AI Cognitive Partner's reasoning capabilities.
It serves as the primary interface to the Google Cloud Vertex AI models and the
Lean 4 formal verifier. It is the "Socratic Auditor" responsible for:
1.  Translating a user's natural language into formal Lean 4 tactics.
2.  Running the generated tactics against the Lean 4 compiler for verification.
3.  Translating cryptic compiler errors into high-quality, pedagogical,
    Socratic feedback for the student.
"""

import os
import subprocess
import json
import logging
from pathlib import Path
from typing import Tuple, Dict, Any

# --- AI Model Imports ---
# This file is now exclusively using the Google Cloud Vertex AI platform.
import vertexai
from vertexai.generative_models import GenerativeModel, Part, HarmCategory, HarmBlockThreshold

# --- Local Imports ---
# A fallback stub for local development or when the API is unavailable.
try:
    from backend import local_llm_stub
except ImportError:
    # This allows the file to be run standalone for testing if needed.
    import local_llm_stub

# --- Global Configuration ---

# Configure logging to provide visibility into the module's operations.
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# --- Vertex AI Configuration ---
# Load configuration from environment variables for security and flexibility.
try:
    PROJECT_ID = os.environ["GOOGLE_CLOUD_PROJECT"]
    LOCATION = os.environ["GOOGLE_CLOUD_LOCATION"]
    # Initialize the Vertex AI client. This is a one-time setup.
    vertexai.init(project=PROJECT_ID, location=LOCATION)
    logging.info(f"Vertex AI initialized successfully for project '{PROJECT_ID}' in '{LOCATION}'.")
except KeyError as e:
    logging.critical(f"FATAL: Environment variable {e} not set. Vertex AI cannot be initialized.")
    # Exit or handle this case gracefully if the application cannot run without Vertex AI.
    PROJECT_ID = None
    LOCATION = None
except Exception as e:
    logging.critical(f"FATAL: An unexpected error occurred during Vertex AI initialization: {e}")
    PROJECT_ID = None
    LOCATION = None


# --- Lean Verifier Configuration ---
# Use pathlib for robust, cross-platform path management.
BACKEND_DIR = Path(__file__).parent.resolve()
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
# The file that will be dynamically overwritten with the proof to be checked.
LEAN_MAIN_FILE = LEAN_PROJECT_PATH / 'LeanVerifier.lean'
# The path to the 'lake' executable. It's recommended to have this in the system's PATH.
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')


def get_llm_response(prompt: str, model_name: str = "gemini-1.5-flash-001", is_json: bool = False) -> str:
    """
    Handles all communication with the Vertex AI Generative Model.

    This function sends a prompt to the specified model and handles the response,
    including error cases and fallbacks.

    Args:
        prompt (str): The prompt to send to the language model.
        model_name (str): The name of the Vertex AI model to use.
        is_json (bool): If True, requests a JSON response from the model.

    Returns:
        str: The text response from the model.
    """
    if not PROJECT_ID:
        logging.warning("Vertex AI not initialized. Falling back to local stub.")
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)

    try:
        # Instantiate the model
        model = GenerativeModel(model_name)

        # Configure safety settings to be less restrictive for this specific use case.
        # This may need adjustment based on policy and observed model behavior.
        safety_settings = {
            HarmCategory.HARM_CATEGORY_HARASSMENT: HarmBlockThreshold.BLOCK_ONLY_HIGH,
            HarmCategory.HARM_CATEGORY_HATE_SPEECH: HarmBlockThreshold.BLOCK_ONLY_HIGH,
            HarmCategory.HARM_CATEGORY_SEXUALLY_EXPLICIT: HarmBlockThreshold.BLOCK_ONLY_HIGH,
            HarmCategory.HARM_CATEGORY_DANGEROUS_CONTENT: HarmBlockThreshold.BLOCK_ONLY_HIGH,
        }
        
        # Configure the generation parameters.
        generation_config = {
            "temperature": 0.3, # Lower temperature for more deterministic, less "creative" output
            "top_p": 0.95,
            "max_output_tokens": 1024,
        }
        if is_json:
            generation_config["response_mime_type"] = "application/json"

        # Generate the content
        response = model.generate_content(
            [prompt],
            generation_config=generation_config,
            safety_settings=safety_settings
        )
        
        # Robustly check for a valid response
        if response and response.candidates:
            if response.candidates[0].finish_reason.name == "SAFETY":
                logging.warning("Response was blocked by safety settings.")
                return '{"error": "Response blocked by safety settings."}' if is_json else "My response was blocked by safety settings. Please try rephrasing your request."
            if response.text:
                return response.text
        
        # If no valid text is found, raise an error
        raise ValueError("Received an empty or invalid response from the API.")

    except Exception as e:
        logging.error(f"Vertex AI API call failed: {e}. Falling back to local stub.")
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)


def run_lean_compiler(current_proof_state: str, tactic: str) -> Tuple[bool, str]:
    """
    Runs the Lean compiler to verify a tactic against the current proof state.

    This function dynamically writes the proof and tactic to a Lean file and
    executes the compiler, capturing the result.

    Args:
        current_proof_state (str): The complete Lean code of the proof so far.
        tactic (str): The new tactic to be verified.

    Returns:
        A tuple containing:
        - bool: True if the tactic is valid, False otherwise.
        - str: The new proof state on success, or the compiler's error message on failure.
    """
    if 'sorry' not in current_proof_state:
        logging.warning("Attempted to verify a step on an already completed proof.")
        return False, "This proof is already complete."
        
    # Replace the 'sorry' placeholder with the new tactic to be tested.
    # The 'sorry' is kept on the next line to allow for continued proof development.
    proof_with_tactic = current_proof_state.replace('sorry', f'by {tactic}\n  sorry', 1)

    try:
        # Write the updated proof to the main Lean file for the compiler to access.
        LEAN_MAIN_FILE.write_text(proof_with_tactic, encoding='utf-8')
        
        # Execute the Lean compiler (`lake build`) as a subprocess.
        process = subprocess.run(
            [LAKE_EXECUTABLE_PATH, 'build'],
            cwd=LEAN_PROJECT_PATH,
            capture_output=True,
            text=True,
            timeout=30,  # A timeout to prevent long-running or hung processes.
            check=False  # Do not raise an exception on non-zero exit codes.
        )
        
        if process.returncode == 0:
            # Success! The tactic is valid.
            # The new proof state is the code with the 'sorry' placeholder advanced.
            new_proof_state = proof_with_tactic.replace('\n  sorry', '')
            logging.info(f"Tactic '{tactic}' verified successfully.")
            return True, new_proof_state
        else:
            # Failure. The tactic is invalid.
            # The error message is captured from stderr.
            error_message = process.stderr or "Lean compiler failed without a specific error message."
            logging.warning(f"Tactic '{tactic}' failed verification. Error: {error_message}")
            return False, error_message
            
    except FileNotFoundError:
        logging.error(f"'{LAKE_EXECUTABLE_PATH}' not found. Please ensure Lean is installed and in the system's PATH.")
        return False, "Server configuration error: Lean compiler not found."
    except subprocess.TimeoutExpired:
        logging.error("Lean compiler process timed out.")
        return False, "The verification process timed out. The tactic might be too complex."
    except Exception as e:
        logging.error(f"An unexpected error occurred while running the Lean compiler: {e}")
        return False, "An unexpected server error occurred during verification."


def verify_step(proof_state: str, user_message: str, mode: str = 'homework') -> Dict[str, Any]:
    """
    Orchestrates the full "Socratic Auditor" loop for a single user step.

    This is the main entry point called by the metacognition engine. It handles
    tactic generation, verification, and Socratic feedback generation based on the
    session mode.

    Args:
        proof_state (str): The current Lean code of the proof.
        user_message (str): The user's message in natural language.
        mode (str): The current session mode ('homework' or 'exam').

    Returns:
        A dictionary containing the results of the verification, e.g.:
        {
            "is_verified": bool,
            "new_proof_code": str,
            "ai_response_text": str,
            "lean_tactic": str
        }
    """
    # === Step 1: Translate Natural Language to a Lean Tactic ===
    # This prompt is carefully structured to request a JSON object for reliable parsing.
    tactic_prompt = f"""
    You are an expert in the Lean 4 proof assistant. Your task is to translate a user's informal mathematical statement into a single, precise Lean 4 tactic.

    Current Proof State:
    ```lean
    {proof_state}
    ```

    User's informal statement: "{user_message}"

    Based on the proof state and the user's statement, determine the most likely Lean 4 tactic.
    Respond with a single JSON object containing one key: "tactic".
    The value should be a string containing only the tactic, for example: "rw [add_comm]".
    If you cannot determine a plausible tactic, the value should be null.
    """
    
    lean_tactic = None
    try:
        tactic_response_str = get_llm_response(tactic_prompt, is_json=True)
        # Clean the response to handle potential markdown formatting from the LLM
        cleaned_response = tactic_response_str.strip().replace("```json", "").replace("```", "")
        tactic_data = json.loads(cleaned_response)
        lean_tactic = tactic_data.get("tactic")
    except (json.JSONDecodeError, ValueError, TypeError) as e:
        logging.error(f"Failed to generate or parse tactic from LLM response '{tactic_response_str}': {e}")
        lean_tactic = None

    if not lean_tactic:
        # If no tactic could be generated, inform the user.
        return {
            "is_verified": None,
            "new_proof_code": proof_state,
            "ai_response_text": "I'm not sure how to translate that into a formal step. Could you try rephrasing it?",
            "lean_tactic": None
        }

    # === Step 2: Run the Tactic Against the Lean Verifier ===
    is_success, verifier_output = run_lean_compiler(proof_state, lean_tactic)

    # === Step 3: Generate a Response Based on Verification Result and Mode ===
    if is_success:
        return {
            "is_verified": True,
            "new_proof_code": verifier_output, # On success, this is the new state
            "ai_response_text": "That's a valid step. Well done! What's next?",
            "lean_tactic": lean_tactic
        }
    else:
        # Verification failed. Now, generate pedagogical feedback.
        compiler_error = verifier_output # On failure, this is the error message
        
        # In 'exam' mode, we provide minimal feedback.
        if mode == 'exam':
            ai_response_text = "That step was not valid."
        else: # In 'homework' mode, we generate a Socratic hint.
            socratic_prompt = f"""
            You are a world-class Socratic tutor for mathematics and formal proofs. A student is working on a proof in Lean 4 and their proposed step failed. Your goal is to help them understand their mistake without giving them the answer.

            Current Proof State:
            ```lean
            {proof_state}
            ```

            The student's informal idea was: "{user_message}"
            This was translated to the Lean tactic: `{lean_tactic}`
            This tactic failed with the following compiler error:
            ```
            {compiler_error}
            ```

            Analyze the error. In 1-2 sentences, explain the *conceptual* reason for the error in a friendly and encouraging tone. Then, ask a single, guiding question to prompt the student to rethink their approach. Do not mention file paths or line numbers. Do not provide the correct code.
            """
            ai_response_text = get_llm_response(socratic_prompt)

        return {
            "is_verified": False,
            "new_proof_code": proof_state, # The state does not change on failure
            "ai_response_text": ai_response_text,
            "lean_tactic": lean_tactic
        }