# backend/app.py

import os
import uuid
import subprocess
import re
import json
import logging
import threading
import shutil
from pathlib import Path
from typing import Dict, Any, Tuple

# --- Third-party Imports ---
from dotenv import load_dotenv
from flask import Flask, request, jsonify
from flask_cors import CORS
from werkzeug.utils import secure_filename
from google import genai
from google.genai import types as genai_types
import fitz  # PyMuPDF library

# --- Local Imports (Fallback) ---
try:
    from backend import local_llm_stub
except ImportError:
    import local_llm_stub


# --- Configuration & Setup ---

load_dotenv()
app = Flask(__name__)
app.logger.setLevel(logging.INFO)
CORS(app, resources={r"/api/*": {"origins": "*"}})

# --- Constants ---
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')
BACKEND_DIR = Path(__file__).parent
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
LEAN_MAIN_FILE = LEAN_PROJECT_PATH / 'Main.lean'
ALLOWED_EXTENSIONS = {'txt', 'pdf', 'md'}
MAX_FILE_SIZE_MB = 10
app.config['MAX_CONTENT_LENGTH'] = MAX_FILE_SIZE_MB * 1024 * 1024

# --- AI Model and Configuration ---
GEMINI_API_KEY = os.getenv('GEMINI_API_KEY')
GEMINI_CLIENT = None
STABLE_MODEL_NAME = 'gemini-1.5-flash'

if GEMINI_API_KEY:
    try:
        GEMINI_CLIENT = genai.Client(api_key=GEMINI_API_KEY)
        app.logger.info("Successfully initialized Gemini client.")
    except Exception as e:
        app.logger.critical(f"FATAL: Failed to initialize Gemini client: {e}")
else:
    app.logger.warning("WARNING: GEMINI_API_KEY not found. AI features will use local stub.")

# --- Thread-Safe In-Memory Storage ---
STATE_LOCK = threading.Lock()
SESSIONS: Dict[str, Dict[str, Any]] = {}
CLASSES: Dict[str, Dict[str, Any]] = {}

# --- Utility & Core Logic ---

def extract_text_from_pdf(file_stream) -> str:
    """Extracts text content from a PDF file stream."""
    try:
        with fitz.open(stream=file_stream.read(), filetype="pdf") as doc:
            return "".join(page.get_text() for page in doc)
    except Exception as e:
        app.logger.error(f"PyMuPDF failed to extract text: {e}")
        raise

def get_llm_response(prompt: str, is_json: bool = False) -> str:
    """Gets a response from a Gemini model, with a fallback to a local stub."""
    if not GEMINI_CLIENT:
        app.logger.warning(f"Gemini client not available. Falling back to local stub for prompt: {prompt[:100]}...")
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
        app.logger.error(f"Gemini API call failed: {e}. Falling back to local stub.")
        return local_llm_stub.generate_response(prompt, is_json_output=is_json)


def run_lean_verifier(session_id: str, lean_tactic: str) -> Tuple[bool, str, str]:
    """Injects a Lean tactic, runs the compiler, and returns the result."""
    with STATE_LOCK:
        if session_id not in SESSIONS:
            return False, "Session not found.", ""
        current_proof = SESSIONS[session_id]['proof_code']
    
    if 'sorry' not in current_proof:
        return False, "Proof is already complete or in an invalid state.", current_proof
    
    new_proof_code_with_tactic = current_proof.replace('sorry', f'{lean_tactic}\n  sorry', 1)
    
    try:
        LEAN_MAIN_FILE.parent.mkdir(parents=True, exist_ok=True)
        LEAN_MAIN_FILE.write_text(new_proof_code_with_tactic, encoding='utf-8')
    except IOError as e:
        app.logger.error(f"Failed to write to Lean file: {e}")
        return False, "Server I/O error.", current_proof
        
    try:
        process = subprocess.run(
            [LAKE_EXECUTABLE_PATH, 'build'], cwd=LEAN_PROJECT_PATH,
            capture_output=True, text=True, timeout=30, check=False
        )
        
        if process.returncode == 0:
            final_proof_code = new_proof_code_with_tactic.replace('\n  sorry', '')
            with STATE_LOCK:
                SESSIONS[session_id]['proof_code'] = final_proof_code
            return True, "Tactic verified successfully!", final_proof_code
        else:
            return False, process.stderr, current_proof
            
    except subprocess.TimeoutExpired:
        app.logger.error("Lean verifier timed out.")
        return False, "Verification timed out. The tactic may be too complex.", current_proof
    except Exception as e:
        app.logger.error(f"Error running Lean verifier: {e}")
        return False, "An unexpected server error occurred during verification.", current_proof

# --- API Endpoints ---

@app.route('/api/health', methods=['GET'])
def health_check():
    return jsonify({"status": "ok"})

@app.route('/api/startSession', methods=['POST'])
def start_session():
    session_id = str(uuid.uuid4())
    initial_proof = "import Mathlib.Data.Real.Basic\n\nexample (a b : ℝ) : a * b = b * a := by\n  sorry"
    initial_ai_response = "Hello! I am your AI partner for Lean 4. The initial proof state is loaded. What is your first step?"
    with STATE_LOCK:
        SESSIONS[session_id] = {"proof_code": initial_proof}
    app.logger.info(f"New session started: {session_id}")
    return jsonify({"sessionId": session_id, "proof_code": initial_proof, "ai_response_text": initial_ai_response})

@app.route('/api/message', methods=['POST'])
def handle_message():
    data = request.get_json()
    if not data or 'sessionId' not in data or 'message' not in data:
        return jsonify({"error": "Missing sessionId or message"}), 400
    
    session_id, user_message = data['sessionId'], data['message']
    
    with STATE_LOCK:
        if session_id not in SESSIONS:
            return jsonify({"error": "Invalid session ID"}), 404
        current_proof_state = SESSIONS[session_id]['proof_code']

    try:
        # --- NEW, more nuanced Intent Routing ---
        intent_prompt = f"""
        Analyze the user's message in the context of a formal proof session in Lean 4. Classify the intent as one of ["PROOF_STEP", "CONCEPTUAL_STEP", "QUESTION", "META_COMMENT"].
        - PROOF_STEP: The user is proposing a direct, formal Lean tactic (e.g., "rw [mul_comm]", "apply mul_comm").
        - CONCEPTUAL_STEP: The user is describing a logical step in natural language (e.g., "use the commutativity of multiplication", "we know a * b = b * a").
        - QUESTION: The user is asking for a definition, a hint, or about the state of the proof (e.g., "what does 'ℝ' mean?", "what should I do next?").
        - META_COMMENT: The user is making a general comment (e.g., "this is hard", "one moment", "test").
        
        User Message: "{user_message}"
        
        Respond with valid JSON containing a single key "intent".
        """
        intent_response_str = get_llm_response(intent_prompt, is_json=True)
        intent_data = json.loads(intent_response_str)
        intent = intent_data.get("intent", "META_COMMENT")
        app.logger.info(f"Session {session_id}: User intent classified as {intent}")

        # --- Logic based on Intent ---
        ai_response_text = ""
        new_proof_state = current_proof_state
        is_verified = None

        if intent == "PROOF_STEP" or intent == "CONCEPTUAL_STEP":
            tactic_prompt = f"""
            Translate the user's natural language statement into a single, valid Lean 4 tactic. Do not add comments or explanations. If no single tactic is appropriate, return null.
            Current Proof State:
            ```lean
            {current_proof_state}
            ```
            User's statement: "{user_message}"
            
            Respond with valid JSON containing a single key "tactic". If no tactic can be generated, the value should be null.
            Example for valid input: {{"tactic": "rw [mul_comm]"}}
            Example for conceptual input: {{"tactic": null}}
            """
            tactic_response_str = get_llm_response(tactic_prompt, is_json=True)
            tactic_data = json.loads(tactic_response_str)
            lean_tactic = tactic_data.get("tactic")

            if lean_tactic:
                is_verified, result_msg, new_proof_state = run_lean_verifier(session_id, lean_tactic)

                if is_verified:
                    ai_response_text = result_msg
                else:
                    socratic_prompt = f"""
                    A student's proof tactic in Lean 4 failed. Be a helpful Socratic tutor. Explain the error conceptually and ask a guiding question.
                    Current Proof State:
                    ```lean
                    {current_proof_state}
                    ```
                    Student's failed tactic: `{lean_tactic}`
                    Compiler Error:
                    ```
                    {result_msg}
                    ```
                    Your Socratic hint (do not give the code answer):
                    """
                    ai_response_text = get_llm_response(socratic_prompt)
            else:
                # Handle conceptual steps that don't map to a single tactic
                is_verified = None
                conceptual_prompt = f"""
                You are an AI assistant. The user has described a conceptual step. Acknowledge their idea and guide them toward the formal Lean 4 tactic that achieves it.
                Current Proof State:
                ```lean
                {current_proof_state}
                ```
                Student's idea: "{user_message}"
                Your guidance:
                """
                ai_response_text = get_llm_response(conceptual_prompt)

        
        else: # QUESTION or META_COMMENT
            chat_prompt = f"""
            You are an AI assistant helping a student with a formal proof. The student is asking a question or making a comment.
            Provide a helpful, conversational response.
            Current Proof State:
            ```lean
            {current_proof_state}
            ```
            Student's message: "{user_message}"
            Your response:
            """
            ai_response_text = get_llm_response(chat_prompt)
            
        return jsonify({"ai_response_text": ai_response_text, "proof_code": new_proof_state, "is_verified": is_verified})

    except json.JSONDecodeError as e:
        app.logger.error(f"JSON parsing failed for AI response: {e}")
        return jsonify({"error": "An internal error occurred: Could not understand the AI's response."}), 500
    except Exception as e:
        app.logger.error(f"Error in handle_message for session {session_id}: {e}")
        return jsonify({"error": "An internal error occurred while handling your message."}), 500


@app.route('/api/addClass', methods=['POST'])
def add_class():
    if 'syllabus' not in request.files or 'className' not in request.form:
        return jsonify({"error": "Missing form data"}), 400
    file, class_name = request.files['syllabus'], request.form['className']
    if not file.filename or '.' not in file.filename or file.filename.rsplit('.', 1)[1].lower() not in ALLOWED_EXTENSIONS:
        return jsonify({"error": f"Invalid file type. Allowed: {', '.join(ALLOWED_EXTENSIONS)}"}), 400
    try:
        syllabus_text = extract_text_from_pdf(file) if file.filename.lower().endswith('.pdf') else file.read().decode('utf-8')
        prompt = f"From the syllabus text below, extract the 5-10 most important concepts. Return a single JSON array of strings in a 'concepts' key.\nExample: {{\"concepts\": [\"Concept 1\", \"Concept 2\"]}}\nSyllabus Text:\n---\n{syllabus_text[:8000]}\n---"
        concepts_json_str = get_llm_response(prompt, is_json=True)
        concepts = json.loads(concepts_json_str).get("concepts", [])
        class_id = str(uuid.uuid4())
        with STATE_LOCK:
            CLASSES[class_id] = {"name": class_name, "concepts": concepts}
        app.logger.info(f"Added new class '{class_name}' with ID {class_id}")
        return jsonify({"classId": class_id, "className": class_name, "concepts": concepts})
    except Exception as e:
        app.logger.error(f"Error in /addClass: {e}")
        return jsonify({"error": "An unexpected server error occurred while analyzing the syllabus."}), 500

@app.route('/api/explainConcept', methods=['POST'])
def explain_concept():
    data = request.get_json()
    if not data or not data.get('concept'):
        return jsonify({"error": "Concept not provided"}), 400
    try:
        prompt = f"You are a university mathematics professor. Provide a clear, concise explanation of the following concept. Use LaTeX for all math notation ($inline$ and $$\\block$$).\n\nConcept: **{data['concept']}**"
        explanation = get_llm_response(prompt)
        return jsonify({"explanation": explanation})
    except Exception as e:
        app.logger.error(f"Failed to get explanation for '{data['concept']}': {e}")
        return jsonify({"error": "Failed to generate explanation."}), 500

# --- Main Execution ---
if __name__ == '__main__':
    app.logger.info("--- Altera Labs Backend Starting ---")
    if not shutil.which(LAKE_EXECUTABLE_PATH):
         app.logger.critical(f"Startup check FAILED: Lean executable not found at '{LAKE_EXECUTABLE_PATH}'. Ensure it is installed and in your system's PATH.")
    else:
        app.logger.info("Startup checks passed.")
        if not LEAN_PROJECT_PATH.exists():
            app.logger.warning(f"Lean project not found at {LEAN_PROJECT_PATH}, creating it...")
            try:
                subprocess.run([LAKE_EXECUTABLE_PATH, 'new', 'lean_verifier', 'math'], cwd=BACKEND_DIR, check=True)
                app.logger.info(f"Fetching mathlib for new project...")
                subprocess.run([LAKE_EXECUTABLE_PATH, 'build'], cwd=LEAN_PROJECT_PATH, check=True)
                app.logger.info(f"Mathlib fetched successfully.")
            except Exception as e:
                app.logger.critical(f"FATAL: Failed to create and build Lean project. Error: {e}")
        app.logger.info("------------------------------------")
        app.run(host='0.0.0.0', port=5000, debug=True)