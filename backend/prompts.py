# backend/app.py

"""
This is the main Flask application file for the Altera Labs backend.

It serves as the web layer, handling API requests and orchestrating the backend
modules to deliver the AI Cognitive Partner experience. It uses Flask's session
management to handle individual user states and delegates core logic to other modules.
"""

import os
import uuid
import json
import logging
from pathlib import Path
from typing import Dict, Any

# --- Third-party Imports ---
from dotenv import load_dotenv
from flask import Flask, request, jsonify, session
from flask_cors import CORS
import fitz  # PyMuPDF

# --- Local Application Imports ---
from backend import prompts
from backend import metacognition
from backend import rag_manager
from backend.socratic_auditor import get_llm_response

# --- Configuration & Setup ---
load_dotenv()

app = Flask(__name__)
app.logger.setLevel(logging.INFO)
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-secret-key-replace-in-prod")
CORS(app, resources={r"/api/*": {"origins": "*"}}, supports_credentials=True)

CLASSES: Dict[str, Dict[str, Any]] = {}

# --- Utility Functions ---
def extract_text_from_pdf(file_stream) -> str:
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
    return jsonify({"status": "ok", "message": "Altera Labs backend is running."})

@app.route('/api/start_session', methods=['POST'])
def start_session():
    """Starts a new tutoring session for a user."""
    data = request.get_json()
    if not data:
        return jsonify({"error": "Invalid request body."}), 400

    session['mode'] = data.get('mode', 'homework')
    session['user_id'] = data.get('userId', str(uuid.uuid4()))
    
    session['student_model'] = {
        "metacognitive_stage": metacognition.MetacognitiveStage.PLANNING_GOAL.value,
        "current_proof_state": "import Mathlib.Data.Real.Basic\n\nexample (a b : ℝ) : a * b = b * a := by\n  sorry",
        "error_history": [],
        "affective_state": "NEUTRAL",
        "knowledge_components": {}
    }
    session.modified = True

    app.logger.info(f"New session started for user {session['user_id']} in {session['mode']} mode.")
    
    return jsonify({
        "message": f"Session started in {session['mode']} mode.",
        "sessionId": session['user_id'],
        "proofCode": session['student_model']['current_proof_state'],
        "aiResponse": prompts.PLANNING_PROMPT_INITIAL
    })

@app.route('/api/chat', methods=['POST'])
def handle_chat_message():
    """Handles a standard chat message from the user."""
    if 'user_id' not in session:
        return jsonify({"error": "No active session. Please start a session first."}), 401
    
    data = request.get_json()
    if not data or 'message' not in data:
        return jsonify({"error": "Request body must be JSON with a 'message' field."}), 400
    
    user_message = data['message']
    
    try:
        updated_student_model, ai_response = metacognition.process_message(
            student_model=session['student_model'],
            user_message=user_message,
            mode=session.get('mode', 'homework')
        )

        session['student_model'] = updated_student_model
        session.modified = True

        return jsonify({
            "aiResponse": ai_response['ai_response_text'],
            "proofCode": updated_student_model['current_proof_state'],
            "isVerified": ai_response.get('is_verified')
        })

    except Exception as e:
        app.logger.error(f"Critical error in handle_chat_message for user {session['user_id']}: {e}", exc_info=True)
        return jsonify({"error": "An internal server error occurred."}), 500

@app.route('/api/explain_concept', methods=['POST'])
def explain_concept():
    """
    --- NEW ENDPOINT ---
    Handles a request for an explanation of a specific concept (text selection).
    """
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    
    data = request.get_json()
    if not data or 'concept' not in data:
        return jsonify({"error": "Request must be JSON with a 'concept' field."}), 400
        
    concept = data.get('concept')
    # The surrounding text from the chat provides valuable context for the AI.
    context = data.get('context', '') 

    try:
        # Use a new, specific prompt for this task.
        prompt = prompts.CONCEPT_EXPLANATION_PROMPT.format(concept=concept, context=context)
        explanation = get_llm_response(prompt)
        return jsonify({"explanation": explanation})
        
    except Exception as e:
        app.logger.error(f"Failed to get explanation for '{concept}': {e}", exc_info=True)
        return jsonify({"error": "Failed to generate explanation."}), 500


@app.route('/api/upload_assignment', methods=['POST'])
def upload_assignment():
    """Handles file uploads for homework or exam assignments."""
    if 'user_id' not in session:
        return jsonify({"error": "No active session. Please start a session first."}), 401

    if 'file' not in request.files:
        return jsonify({"error": "No file part in the request."}), 400
    
    file = request.files['file']

    if file.filename == '':
        return jsonify({"error": "No file selected."}), 400

    if file:
        file_path, error = rag_manager.save_assignment_file(session['user_id'], file)
        if error:
            return jsonify({"error": error}), 500
        
        return jsonify({"message": "File uploaded successfully.", "filePath": file_path}), 200
    
    return jsonify({"error": "Invalid file."}), 400


@app.route('/api/add_class', methods=['POST'])
def add_class():
    """Handles syllabus upload to create a new 'class' with extracted concepts."""
    if 'syllabus' not in request.files or 'className' not in request.form:
        return jsonify({"error": "Request must be multipart/form-data with 'syllabus' file and 'className' field."}), 400
    
    file, class_name = request.files['syllabus'], request.form['className']
        
    try:
        syllabus_text = extract_text_from_pdf(file) if file.filename.lower().endswith('.pdf') else file.read().decode('utf-8')
        
        prompt = prompts.SYLLABUS_EXTRACTION_PROMPT.format(syllabus_text=syllabus_text[:8000])
        concepts_json_str = get_llm_response(prompt, is_json=True)
        concepts = json.loads(concepts_json_str).get("concepts", [])
        
        class_id = str(uuid.uuid4())
        CLASSES[class_id] = {"name": class_name, "concepts": concepts}
            
        app.logger.info(f"Added new class '{class_name}' with ID {class_id}")
        return jsonify({"classId": class_id, "className": class_name, "concepts": concepts})
        
    except Exception as e:
        app.logger.error(f"Error in /add_class: {e}", exc_info=True)
        return jsonify({"error": "An unexpected server error occurred while analyzing the syllabus."}), 500

# --- Main Execution ---
if __name__ == '__main__':
    app.logger.info("--- Altera Labs Backend Starting ---")
    app.run(host='0.0.0.0', port=5000, debug=True)

