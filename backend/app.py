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
# CORRECT IMPORTS based on the provided documentation
from google import genai
from google.genai import types as genai_types
import fitz  # PyMuPDF library

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
# Per documentation, the model name is passed directly.
STABLE_MODEL_NAME = 'gemini-1.5-flash' 

# CORRECTED INITIALIZATION: This pattern matches the documentation exactly.
if GEMINI_API_KEY:
    try:
        # Use genai.Client() for initialization.
        GEMINI_CLIENT = genai.Client(api_key=GEMINI_API_KEY)
        app.logger.info("Successfully initialized Gemini client.")
    except Exception as e:
        app.logger.critical(f"FATAL: Failed to initialize Gemini client: {e}")
else:
    app.logger.critical("FATAL: GEMINI_API_KEY not found. AI features will be disabled.")

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

# CORRECTED: This function now strictly follows the provided documentation.
def get_llm_response(prompt: str, is_json: bool = False) -> str:
    """Gets a response from a Gemini model using the central client."""
    if not GEMINI_CLIENT:
        raise ConnectionError("Gemini client is not configured.")
    try:
        safety_settings = [
            genai_types.SafetySetting(
                category='HARM_CATEGORY_HARASSMENT',
                threshold='BLOCK_MEDIUM_AND_ABOVE',
            ),
            genai_types.SafetySetting(
                category='HARM_CATEGORY_HATE_SPEECH',
                threshold='BLOCK_MEDIUM_AND_ABOVE',
            ),
            genai_types.SafetySetting(
                category='HARM_CATEGORY_SEXUALLY_EXPLICIT',
                threshold='BLOCK_MEDIUM_AND_ABOVE',
            ),
            genai_types.SafetySetting(
                category='HARM_CATEGORY_DANGEROUS_CONTENT',
                threshold='BLOCK_MEDIUM_AND_ABOVE',
            ),
        ]
        
        # All configuration goes into a single `config` object.
        config_args = {"safety_settings": safety_settings}
        if is_json:
            config_args["response_mime_type"] = "application/json"

        config = genai_types.GenerateContentConfig(**config_args)

        # The API call uses `client.models.generate_content`
        response = GEMINI_CLIENT.models.generate_content(
            model=STABLE_MODEL_NAME,
            contents=prompt,
            config=config
        )
        if response.prompt_feedback.block_reason:
            raise ValueError(f"Prompt was blocked: {response.prompt_feedback.block_reason.name}")
        return response.text
    except Exception as e:
        app.logger.error(f"Gemini API call failed: {e}")
        raise

def run_lean_verifier(session_id: str, lean_tactic: str) -> Tuple[bool, str, str]:
    """Injects a Lean tactic, runs the compiler, and returns the result."""
    with STATE_LOCK:
        if session_id not in SESSIONS:
            return False, "Session not found.", ""
        current_proof = SESSIONS[session_id]['proof_code']
    if 'sorry' not in current_proof:
        return False, "Proof is already complete or in an invalid state.", current_proof
    new_proof_code = current_proof.replace('sorry', lean_tactic, 1)
    try:
        LEAN_MAIN_FILE.write_text(new_proof_code, encoding='utf-8')
    except IOError as e:
        app.logger.error(f"Failed to write to Lean file: {e}")
        return False, "Server I/O error.", current_proof
    try:
        process = subprocess.run(
            [LAKE_EXECUTABLE_PATH, 'build'], cwd=LEAN_PROJECT_PATH,
            capture_output=True, text=True, timeout=30
        )
        if process.returncode == 0:
            with STATE_LOCK:
                SESSIONS[session_id]['proof_code'] = new_proof_code
            return True, "Tactic verified successfully!", new_proof_code
        else:
            return False, process.stderr, current_proof
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
        # Create a chat object for the session as per the documentation
        chat = GEMINI_CLIENT.chats.create(model=STABLE_MODEL_NAME)
        SESSIONS[session_id] = {
            "proof_code": initial_proof,
            "chat_session": chat, # Store the chat object
        }
    app.logger.info(f"New session started: {session_id}")
    return jsonify({"sessionId": session_id, "proof_code": initial_proof, "ai_response_text": initial_ai_response})

@app.route('/api/message', methods=['POST'])
def handle_message():
    data = request.get_json()
    if not data or not data.get('sessionId') or not data.get('message'):
        return jsonify({"error": "Missing sessionId or message"}), 400
    session_id, user_message = data['sessionId'], data['message']
    
    with STATE_LOCK:
        if session_id not in SESSIONS:
            return jsonify({"error": "Invalid session ID"}), 404
        chat_session = SESSIONS[session_id]['chat_session']
        current_proof_state = SESSIONS[session_id]['proof_code']

    try:
        # The complex intent logic can be simplified by just sending the context to the model.
        # For this example, we'll use the chat session to maintain context.
        contextual_prompt = f"Current Lean 4 proof state:\n```lean\n{current_proof_state}\n```\n\nUser message: \"{user_message}\"\n\nBased on the user's message, provide a helpful response. If it's a tactic, analyze it. If it's a question, answer it."
        
        response = chat_session.send_message(contextual_prompt)
        ai_response_text = response.text
        
        # The logic for running the Lean verifier can be re-integrated here
        # by parsing the AI's response to see if it suggests a tactic.
        # For now, we return the AI's direct response.
        new_proof_state = current_proof_state
        is_verified = None

        return jsonify({"ai_response_text": ai_response_text, "proof_code": new_proof_state, "is_verified": is_verified})
    except Exception as e:
        app.logger.error(f"Error in handle_message for session {session_id}: {e}")
        return jsonify({"error": "An internal error occurred while processing your message."}), 500


@app.route('/api/addClass', methods=['POST'])
def add_class():
    if 'syllabus' not in request.files or 'className' not in request.form:
        return jsonify({"error": "Missing form data"}), 400
    file, class_name = request.files['syllabus'], request.form['className']
    if not file.filename or '.' not in file.filename or file.filename.rsplit('.', 1)[1].lower() not in ALLOWED_EXTENSIONS:
        return jsonify({"error": f"Invalid file type. Allowed: {', '.join(ALLOWED_EXTENSIONS)}"}), 400
    try:
        syllabus_text = extract_text_from_pdf(file) if file.filename.lower().endswith('.pdf') else file.read().decode('utf-8')
        prompt = f"From the syllabus text below, extract the 5-10 most important concepts. Return a single JSON array of strings.\nExample: [\"Concept 1\", \"Concept 2\"]\nSyllabus Text:\n---\n{syllabus_text[:8000]}\n---"
        concepts_json_str = get_llm_response(prompt, is_json=True)
        concepts = json.loads(concepts_json_str)
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
        prompt = f"You are a university mathematics professor. Provide a clear, concise explanation of the following concept. Use LaTeX for all math notation ($inline$$ and $$\\block$$).\n\nConcept: **{data['concept']}**"
        explanation = get_llm_response(prompt)
        return jsonify({"explanation": explanation})
    except Exception as e:
        app.logger.error(f"Failed to get explanation for '{data['concept']}': {e}")
        return jsonify({"error": "Failed to generate explanation."}), 500

# --- Main Execution ---
if __name__ == '__main__':
    app.logger.info("--- Altera Labs Backend Starting ---")
    if not GEMINI_CLIENT:
        app.logger.critical("Startup check FAILED: Gemini client is not initialized. Check API key and logs.")
    elif not shutil.which(LAKE_EXECUTABLE_PATH):
         app.logger.critical(f"Startup check FAILED: Lean executable not found at '{LAKE_EXECUTABLE_PATH}'. Ensure it is installed and in your system's PATH.")
    else:
        app.logger.info("Startup checks passed.")
        if not LEAN_PROJECT_PATH.exists():
            app.logger.warning(f"Lean project not found at {LEAN_PROJECT_PATH}, creating it...")
            try:
                subprocess.run([LAKE_EXECUTABLE_PATH, 'new', 'lean_verifier', 'math'], cwd=BACKEND_DIR, check=True)
            except Exception as e:
                app.logger.critical(f"FATAL: Failed to create Lean project. Error: {e}")
        app.logger.info("------------------------------------")
        app.run(host='0.0.0.0', port=5000, debug=False)
