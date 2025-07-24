# backend/app.py

import os
import uuid
import json
import logging
import sys # --- ADDED: To allow exiting on critical errors ---
from pathlib import Path
from typing import Dict, Any

from dotenv import load_dotenv
from flask import Flask, request, jsonify, session
from flask_cors import CORS
import fitz
import vertexai # --- ADDED: Import the Vertex AI library ---

from backend import prompts
from backend import metacognition
from backend import rag_manager
from backend.socratic_auditor import get_llm_response
from backend.lean_verifier import lean_verifier_instance 

# --- FIXED: Load environment variables and initialize AI services at startup ---
load_dotenv()

# Initialize Vertex AI
try:
    PROJECT_ID = os.environ.get("VERTEX_AI_PROJECT_ID")
    LOCATION = os.environ.get("VERTEX_AI_LOCATION")

    if not PROJECT_ID or not LOCATION:
        logging.critical("FATAL: VERTEX_AI_PROJECT_ID and VERTEX_AI_LOCATION environment variables must be set.")
        sys.exit(1) 

    vertexai.init(project=PROJECT_ID, location=LOCATION)
    logging.info(f"Vertex AI initialized successfully for project '{PROJECT_ID}' in '{LOCATION}'.")

except Exception as e:
    logging.critical(f"FATAL: An unexpected error occurred during Vertex AI initialization: {e}")
    sys.exit(1) 

# --- Flask App Initialization ---
app = Flask(__name__)
app.logger.setLevel(logging.INFO)
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-secret-key-replace-in-prod")
CORS(app, resources={r"/api/*": {"origins": "*"}}, supports_credentials=True)

CLASSES: Dict[str, Dict[str, Any]] = {}

def extract_text_from_pdf(file_stream) -> str:
    try:
        with fitz.open(stream=file_stream.read(), filetype="pdf") as doc:
            return "".join(page.get_text() for page in doc)
    except Exception as e:
        app.logger.error(f"PyMuPDF failed to extract text: {e}")
        raise

# ======================================================================================
# == API Endpoints (No changes needed below this line)
# ======================================================================================

@app.route('/api/health', methods=['GET'])
def health_check():
    return jsonify({"status": "ok"})

@app.route('/api/start_session', methods=['POST'])
def start_session():
    data = request.get_json()
    session['mode'] = data.get('mode', 'homework')
    session['user_id'] = data.get('userId', str(uuid.uuid4()))
    session['student_model'] = {
        "metacognitive_stage": metacognition.MetacognitiveStage.PLANNING_GOAL.value,
        "current_proof_state": "import Mathlib.Data.Real.Basic\n\nexample (a b : ℝ) : a * b = b * a := by\n  sorry",
        "error_history": [], "affective_state": "NEUTRAL", "knowledge_components": {}
    }
    session.modified = True
    return jsonify({
        "message": f"Session started in {session['mode']} mode.",
        "sessionId": session['user_id'],
        "proofCode": session['student_model']['current_proof_state'],
        "aiResponse": prompts.PLANNING_PROMPT_INITIAL
    })

@app.route('/api/chat', methods=['POST'])
def handle_chat_message():
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    data = request.get_json()
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
        app.logger.error(f"Error in handle_chat_message: {e}", exc_info=True)
        return jsonify({"error": "Internal server error."}), 500

@app.route('/api/explain_concept', methods=['POST'])
def explain_concept():
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    data = request.get_json()
    concept = data.get('concept')
    context = data.get('context', '')
    try:
        prompt = prompts.CONCEPT_EXPLANATION_PROMPT.format(concept=concept, context=context)
        explanation = get_llm_response(prompt)
        return jsonify({"explanation": explanation})
    except Exception as e:
        app.logger.error(f"Failed to get explanation for '{concept}': {e}", exc_info=True)
        return jsonify({"error": "Failed to generate explanation."}), 500

@app.route('/api/finalize_exam', methods=['POST'])
def finalize_exam():
    if 'user_id' not in session:
        return jsonify({"error": "No active session to finalize."}), 401
    data = request.get_json()
    if not data or 'knowledgeState' not in data:
        return jsonify({"error": "Request must be JSON with a 'knowledgeState' field."}), 400
    final_knowledge_state = data['knowledgeState']
    try:
        app.logger.info(f"Finalizing exam for user {session['user_id']}.")
        return jsonify({
            "message": "Exam finalized successfully.",
            "finalKnowledgeState": final_knowledge_state
        })
    except Exception as e:
        app.logger.error(f"Error finalizing exam for user {session['user_id']}: {e}", exc_info=True)
        return jsonify({"error": "An internal server error occurred while finalizing the exam."}), 500

@app.route('/api/verify_step', methods=['POST'])
def verify_step():
    """
    --- NEW ENDPOINT ---
    Receives a natural language proof step and uses the Lean Verifier
    service to check it.
    """
    data = request.get_json()
    if not data or 'proof_state' not in data or 'step' not in data:
        return jsonify({"error": "Request must include 'proof_state' and 'step'."}), 400
    
    current_proof_state = data['proof_state']
    natural_language_step = data['step']
    
    try:
        # Delegate the core logic to our new verifier service
        result = lean_verifier_instance.verify_step(current_proof_state, natural_language_step)
        return jsonify(result)
        
    except Exception as e:
        app.logger.error(f"Error during proof verification: {e}", exc_info=True)
        return jsonify({"error": "An internal server error occurred during verification."}), 500


@app.route('/api/upload_assignment', methods=['POST'])
def upload_assignment():
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    if 'file' not in request.files:
        return jsonify({"error": "No file part."}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({"error": "No selected file."}), 400
    if file:
        file_path, error = rag_manager.save_assignment_file(session['user_id'], file)
        if error:
            return jsonify({"error": error}), 500
        return jsonify({"message": "File uploaded successfully.", "filePath": file_path}), 200
    return jsonify({"error": "Invalid file."}), 400

@app.route('/api/add_class', methods=['POST'])
def add_class():
    if 'syllabus' not in request.files or 'className' not in request.form:
        return jsonify({"error": "Missing form data."}), 400
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
        return jsonify({"error": "Server error analyzing syllabus."}), 500

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True)
