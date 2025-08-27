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
# Use Google Gen AI SDK (Vertex-compatible) to avoid deprecation
from google import genai
from google.genai.types import GenerateContentConfig

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

# --- Lean Verifier Configuration ---
# Use pathlib for robust, cross-platform path management.
BACKEND_DIR = Path(__file__).parent.resolve()
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
# The file that will be dynamically overwritten with the proof to be checked.
LEAN_MAIN_FILE = LEAN_PROJECT_PATH / 'LeanVerifier.lean'
# The path to the 'lake' executable with cross-platform compatibility
import platform
if platform.system() == 'Windows':
    LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake.exe')
else:
    LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')


def get_llm_response(prompt: str, model_name: str = None, is_json: bool = False) -> str:
    """
    Handles all communication with the Google Generative AI Model.

    This function sends a prompt to the specified model and handles the response,
    including error cases and fallbacks.

    Args:
        prompt (str): The prompt to send to the language model.
        model_name (str): The name of the Google AI model to use. Defaults to DEFAULT_LLM_MODEL env var.
        is_json (bool): If True, requests a JSON response from the model.

    Returns:
        str: The text response from the model.
    """
    # Use environment variable for default model if not specified
    if model_name is None:
        model_name = os.environ.get("DEFAULT_LLM_MODEL", "gemini-2.5-flash")
    
    # Use Google Gen AI SDK with Vertex backend
    try:
        # Initialize client with project and location from environment
        project_id = os.environ.get("VERTEX_AI_PROJECT_ID")
        location = os.environ.get("VERTEX_AI_LOCATION")
        
        if project_id and location:
            client = genai.Client(vertexai=True, project=project_id, location=location)

            # Configure generation parameters
            if is_json:
                config = GenerateContentConfig(
                    temperature=0.3,
                    top_p=0.95,
                    max_output_tokens=20000,
                    response_mime_type="application/json",
                )
            else:
                config = GenerateContentConfig(
                    temperature=0.3,
                    top_p=0.95,
                    max_output_tokens=20000,
                )

            # Generate content using the Gen AI SDK
            response = client.models.generate_content(
                model=model_name,
                contents=prompt,
                config=config,
            )

            text = getattr(response, "output_text", None) or getattr(response, "text", None)
            if response and text:
                return text
            else:
                raise ValueError("Received an empty or invalid response from Vertex AI")
                
        else:
            raise ValueError("VERTEX_AI_PROJECT_ID and VERTEX_AI_LOCATION must be set for Vertex AI")
            
    except Exception as e:
        logging.error(f"Vertex AI API call failed: {e}, falling back to local stub")
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


class ProvingAgent:
    """
    A class that handles mathematical problem solving and verification using Lean 4.
    This agent can convert natural language problems to Lean 4, verify solutions,
    and generate solution graphs for concept extraction.
    """
    
    def __init__(self):
        self.lean_project_path = LEAN_PROJECT_PATH
        self.lake_executable = LAKE_EXECUTABLE_PATH
    
    def solve_problem(self, problem_description: str) -> Dict[str, Any]:
        """
        Solve a mathematical problem described in natural language.
        
        Args:
            problem_description (str): Natural language description of the problem
            
        Returns:
            Dict containing solution status and details
        """
        try:
            # Convert natural language to Lean 4
            lean_code = self.convert_to_lean(problem_description)
            
            # Verify with Lean 4
            verification_result = self.verify_with_lean(lean_code)
            
            # Generate solution graph if successful
            if verification_result['status'] == 'SOLVED':
                solution_graph = self.generate_solution_graph(lean_code, problem_description)
                verification_result['solution_graph'] = solution_graph
            
            return verification_result
            
        except Exception as e:
            logging.error(f"Error in solve_problem: {e}")
            return {
                'status': 'ERROR',
                'error': str(e),
                'feedback': 'An error occurred while processing the problem.'
            }
    
    def convert_to_lean(self, problem_description: str) -> str:
        """
        Convert natural language problem description to Lean 4 code.
        
        Args:
            problem_description (str): Natural language description
            
        Returns:
            str: Lean 4 code
        """
        prompt = f"""
        You are an expert in Lean 4 and group theory. Convert the following problem description into valid Lean 4 code.
        
        Problem: {problem_description}
        
        Generate a complete Lean 4 theorem or lemma that represents this problem. Include all necessary imports and make sure the code is syntactically correct.
        
        Respond with only the Lean 4 code, no explanations.
        """
        
        try:
            lean_code = get_llm_response(prompt)
            return lean_code.strip()
        except Exception as e:
            logging.error(f"Error converting to Lean: {e}")
            raise
    
    def verify_with_lean(self, lean_code: str) -> Dict[str, Any]:
        """
        Verify Lean 4 code using the Lean compiler.
        
        Args:
            lean_code (str): Lean 4 code to verify
            
        Returns:
            Dict containing verification status and feedback
        """
        try:
            # Create a temporary file with the Lean code
            temp_file = self.lean_project_path / 'temp_proof.lean'
            with open(temp_file, 'w') as f:
                f.write(lean_code)
            
            # Run Lean compiler
            result = subprocess.run(
                [self.lake_executable, 'build'],
                cwd=self.lean_project_path,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # Clean up temporary file
            temp_file.unlink(missing_ok=True)
            
            if result.returncode == 0:
                return {
                    'status': 'SOLVED',
                    'feedback': 'The proof is correct and verified by Lean 4.',
                    'lean_output': result.stdout
                }
            else:
                return {
                    'status': 'FAILED',
                    'feedback': f'Lean 4 verification failed: {result.stderr}',
                    'lean_output': result.stderr
                }
                
        except subprocess.TimeoutExpired:
            return {
                'status': 'FAILED',
                'feedback': 'Verification timed out. The proof may be too complex.',
                'lean_output': 'Timeout'
            }
        except Exception as e:
            return {
                'status': 'ERROR',
                'feedback': f'Error during verification: {str(e)}',
                'lean_output': str(e)
            }
    
    def generate_solution_graph(self, lean_code: str, problem_description: str) -> Dict[str, Any]:
        """
        Generate a solution graph showing the concepts and steps used in the proof.
        
        Args:
            lean_code (str): The verified Lean 4 code
            problem_description (str): Original problem description
            
        Returns:
            Dict containing solution graph structure
        """
        prompt = f"""
        Analyze the following Lean 4 proof and generate a solution graph showing the mathematical concepts and logical steps used.
        
        Problem: {problem_description}
        Proof: {lean_code}
        
        Generate a JSON object with the following structure:
        {{
            "concepts": ["list", "of", "mathematical", "concepts"],
            "steps": [
                {{
                    "step": "description of the step",
                    "concept": "mathematical concept used",
                    "difficulty": "easy|medium|hard"
                }}
            ],
            "prerequisites": ["list", "of", "prerequisite", "concepts"]
        }}
        """
        
        try:
            response = get_llm_response(prompt, is_json=True)
            return json.loads(response)
        except Exception as e:
            logging.error(f"Error generating solution graph: {e}")
            return {
                'concepts': [],
                'steps': [],
                'prerequisites': []
            }