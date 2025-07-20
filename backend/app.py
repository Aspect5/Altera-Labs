# backend/app.py

"""
This is the main Flask application file for the Altera Labs backend.

It serves as the web layer, handling API requests and orchestrating the backend
modules to deliver the AI Cognitive Partner experience. The core logic for
proof verification and pedagogical strategy is delegated to the `socratic_auditor`
and `metacognition` modules, respectively.
"""

import os
import uuid
import json
import logging
import threading
import shutil
import subprocess
from pathlib import Path
from typing import Dict, Any

# --- Third-party Imports ---
from dotenv import load_dotenv
from flask import Flask, request, jsonify
from flask_cors import CORS
from werkzeug.utils import secure_filename
import fitz  # PyMuPDF library

# --- Local Application Imports ---
# Import the newly created modules for core logic and prompts.
from backend import prompts
from backend import metacognition
from backend.socratic_auditor import get_llm_response # LLM utility is now in the auditor module

# --- Configuration & Setup ---
load_dotenv()
app = Flask(__name__)
app.logger.setLevel(logging.INFO)
CORS(app, resources={r"/api/*": {"origins": "*"}})

# --- Constants ---
# Constants related to the Lean verifier are now primarily managed in socratic_auditor.py
# but we may need some paths here for setup.
LAKE_EXECUTABLE_PATH = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')
BACKEND_DIR = Path(__file__).parent
LEAN_PROJECT_PATH = BACKEND_DIR / 'lean_verifier'
ALLOWED_EXTENSIONS = {'txt', 'pdf', 'md'}
MAX_FILE_SIZE_MB = 10
app.config['MAX_CONTENT_LENGTH'] = MAX_FILE_SIZE_MB * 1024 * 1024

# --- Thread-Safe In-Memory Storage ---
# This remains in the main app file as it represents the global state of all user sessions.
STATE_LOCK = threading.Lock()
SESSIONS: Dict[str, Dict[str, Any]] = {}
CLASSES: Dict[str, Dict[str, Any]] = {}

# --- Utility Functions ---

def extract_text_from_pdf(file_stream) -> str:
    """Extracts text content from a PDF file stream."""
    try:
        with fitz.open(stream=file_stream.read(), filetype="pdf") as doc:
            return "".join(page.get_text() for page in doc)
    except Exception as e:
        app.logger.error(f"PyMuPDF failed to extract text: {e}")
        raise

# ======================================================================================
# == API Endpoints
# ======================================================================================

@app.route('/api/health', methods=['GET'])
def health_check():
    """A simple endpoint to confirm the server is running."""
    return jsonify({"status": "ok"})

@app.route('/api/startSession', methods=['POST'])
def start_session():
    """
    Starts a new proof-auditing session for a user.
    Initializes the session state, including the metacognitive loop.
    """
    session_id = str(uuid.uuid4())
    initial_proof = "import Mathlib.Data.Real.Basic\n\nexample (a b : ℝ) : a * b = b * a := by\n  sorry"
    
    with STATE_LOCK:
        # Create the session object.
        SESSIONS[session_id] = {
            "session_id": session_id,
            "proof_code": initial_proof,
            # The metacognitive stage will be set by the initialization function.
        }
        # Initialize the metacognitive loop for the new session.
        initial_response = metacognition.initialize_session(SESSIONS[session_id])

    app.logger.info(f"New session started: {session_id}")
    
    # The initial response now comes from the metacognition module.
    return jsonify({
        "sessionId": session_id,
        "proof_code": initial_response['proof_code'],
        "ai_response_text": initial_response['ai_response_text']
    })

@app.route('/api/message', methods=['POST'])
def handle_message():
    """
    Handles an incoming message from the user during a session.
    
    This endpoint is the core of the interactive loop. It delegates all logic
    to the `metacognition.process_message` function, which orchestrates the
    Plan-Monitor-Reflect cycle and the Socratic Auditor.
    """
    data = request.get_json()
    if not data or 'sessionId' not in data or 'message' not in data:
        return jsonify({"error": "Missing sessionId or message"}), 400
    
    session_id, user_message = data['sessionId'], data['message']
    
    with STATE_LOCK:
        if session_id not in SESSIONS:
            return jsonify({"error": "Invalid session ID"}), 404
        # Get a mutable reference to the current session.
        session = SESSIONS[session_id]

    try:
        # --- DELEGATION OF LOGIC ---
        # All complex logic is now handled by the metacognition module.
        result = metacognition.process_message(session, user_message)
        
        # The session object may have been modified by the metacognition module
        # (e.g., stage change, proof code update), so we update the global state.
        with STATE_LOCK:
            SESSIONS[session_id] = session
            
        return jsonify({
            "ai_response_text": result['ai_response_text'],
            "proof_code": result['new_proof_code'],
            "is_verified": result['is_verified']
        })

    except Exception as e:
        app.logger.error(f"Critical error in handle_message for session {session_id}: {e}")
        return jsonify({"error": "An internal server error occurred."}), 500


@app.route('/api/addClass', methods=['POST'])
def add_class():
    """Handles syllabus upload to create a new 'class' with extracted concepts."""
    if 'syllabus' not in request.files or 'className' not in request.form:
        return jsonify({"error": "Missing form data"}), 400
    
    file, class_name = request.files['syllabus'], request.form['className']
    
    if not file.filename or '.' not in file.filename or file.filename.rsplit('.', 1)[1].lower() not in ALLOWED_EXTENSIONS:
        return jsonify({"error": f"Invalid file type. Allowed: {', '.join(ALLOWED_EXTENSIONS)}"}), 400
        
    try:
        syllabus_text = extract_text_from_pdf(file) if file.filename.lower().endswith('.pdf') else file.read().decode('utf-8')
        
        # Use the centralized prompt from prompts.py
        prompt = prompts.SYLLABUS_EXTRACTION_PROMPT.format(syllabus_text=syllabus_text[:8000])
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
    """Provides a detailed explanation for a given concept."""
    data = request.get_json()
    if not data or not data.get('concept'):
        return jsonify({"error": "Concept not provided"}), 400
        
    try:
        # Use the centralized prompt from prompts.py
        prompt = prompts.CONCEPT_EXPLANATION_PROMPT.format(concept=data['concept'])
        explanation = get_llm_response(prompt)
        return jsonify({"explanation": explanation})
        
    except Exception as e:
        app.logger.error(f"Failed to get explanation for '{data['concept']}': {e}")
        return jsonify({"error": "Failed to generate explanation."}), 500

# --- Main Execution ---
if __name__ == '__main__':
    app.logger.info("--- Altera Labs Backend Starting ---")
    
    # Perform startup checks
    if not shutil.which(LAKE_EXECUTABLE_PATH):
         app.logger.critical(f"Startup check FAILED: Lean executable not found at '{LAKE_EXECUTABLE_PATH}'.")
    else:
        app.logger.info("Startup checks passed.")
        # Ensure the Lean project exists and its dependencies are fetched.
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
