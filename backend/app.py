# backend/app.py

import os
import uuid
import json
import logging
import sys # --- ADDED: To allow exiting on critical errors ---
import random # --- ADDED: For Proving Agent MVP simulation ---
from pathlib import Path
from typing import Dict, Any

from dotenv import load_dotenv
from flask import Flask, request, jsonify, session
from flask_cors import CORS
import fitz
import vertexai # --- ADDED: Import the Vertex AI library ---

from . import prompts
from . import metacognition
from . import rag_manager
from .socratic_auditor import get_llm_response
from .lean_verifier import lean_verifier_instance 

# --- FIXED: Load environment variables and initialize AI services at startup ---
load_dotenv()

# Initialize Vertex AI
try:
    PROJECT_ID = os.environ.get("VERTEX_AI_PROJECT_ID")
    LOCATION = os.environ.get("VERTEX_AI_LOCATION")

    if PROJECT_ID and LOCATION:
        vertexai.init(project=PROJECT_ID, location=LOCATION)
        logging.info(f"Vertex AI initialized successfully for project '{PROJECT_ID}' in '{LOCATION}'.")
    else:
        logging.warning("VERTEX_AI_PROJECT_ID and VERTEX_AI_LOCATION not set. Running in development mode without Vertex AI.")

except Exception as e:
    logging.warning(f"Vertex AI initialization failed: {e}. Continuing without Vertex AI.")

# --- Flask App Initialization ---
app = Flask(__name__)
app.logger.setLevel(logging.INFO)
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-secret-key-replace-in-prod")
CORS(app, resources={r"/api/*": {"origins": "*"}}, supports_credentials=True)

# --- PERSISTENT CLASS STORAGE ---
CLASSES_FILE = Path("/workspaces/Altera-Labs/data/classes.json")
CLASSES_FILE.parent.mkdir(exist_ok=True)

def load_classes() -> Dict[str, Dict[str, Any]]:
    """Load classes from persistent storage."""
    if CLASSES_FILE.exists():
        try:
            with open(CLASSES_FILE, 'r') as f:
                return json.load(f)
        except Exception as e:
            app.logger.error(f"Failed to load classes: {e}")
            return {}
    return {}

def save_classes(classes: Dict[str, Dict[str, Any]]) -> None:
    """Save classes to persistent storage."""
    try:
        with open(CLASSES_FILE, 'w') as f:
            json.dump(classes, f, indent=2)
        app.logger.info(f"Saved {len(classes)} classes to persistent storage")
    except Exception as e:
        app.logger.error(f"Failed to save classes: {e}")

# Load existing classes on startup
CLASSES: Dict[str, Dict[str, Any]] = load_classes()
app.logger.info(f"Loaded {len(CLASSES)} existing classes from persistent storage")

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
    mode = data.get('mode', 'homework')
    session['user_id'] = str(uuid.uuid4())
    session['mode'] = mode
    session['student_model'] = {
        'current_proof_state': "theorem example (a b : ℝ) : a * b = b * a := by\n  sorry",
        'affective_state': 'NEUTRAL',
        'confidence': 0.5,
        'difficulty_progress': 0.0,
        'progress_history': []
    }
    
    # --- FIXED: Properly initialize the metacognitive stage ---
    metacognition.initialize_session_stage(session)
    
    # --- FIXED: Generate dynamic initial response instead of static prompt ---
    try:
        initial_prompt = f"""
You are a helpful math tutor starting a new session with a student.
The session mode is: {mode}

Provide a warm, encouraging welcome message that:
1. Greets the student warmly
2. Explains that you're here to help them with their mathematical thinking
3. Asks them to start by understanding the goal of what they're trying to prove
4. Encourages them to explain the problem in their own words

Keep your response conversational and supportive. Do NOT mention syllabus analysis or class concepts.
"""
        initial_response = get_llm_response(initial_prompt)
        
        return jsonify({
            "message": f"Session started in {session['mode']} mode.",
            "sessionId": session['user_id'],
            "proofCode": session['student_model']['current_proof_state'],
            "aiResponse": initial_response
        })
    except Exception as e:
        app.logger.error(f"Error generating initial response: {e}")
        # Fallback to a simple welcome message
        return jsonify({
            "message": f"Session started in {session['mode']} mode.",
            "sessionId": session['user_id'],
            "proofCode": session['student_model']['current_proof_state'],
            "aiResponse": "Hello! I'm here to help you with your mathematical thinking. Let's start by understanding what we're trying to prove. Can you explain the goal in your own words?"
        })

@app.route('/api/chat', methods=['POST'])
def handle_chat_message():
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    data = request.get_json()
    user_message = data['message']
    try:
        ai_response = metacognition.process_message(session, user_message)
        session.modified = True
        return jsonify({
            "aiResponse": ai_response['ai_response_text'],
            "proofCode": ai_response.get('proof_code', session['student_model']['current_proof_state']),
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

def create_and_get_class(class_name: str, file_stream: Any, file_type: str) -> Dict[str, Any]:
    # Check if class already exists to prevent reprocessing
    for class_id, existing_class in CLASSES.items():
        if existing_class['className'] == class_name:
            app.logger.info(f"Class '{class_name}' already exists, returning existing data")
            return existing_class
    
    # This is a helper to centralize the class creation logic
    # TODO: In the future, this is where the "Proving Agent" logic will go.
    class_id = str(uuid.uuid4())
    
    # For now, we just extract text regardless of type
    if file_stream.filename.endswith('.pdf'):
        document_text = extract_text_from_pdf(file_stream)
    else:
        document_text = file_stream.read().decode('utf-8')
    
    prompt = prompts.SYLLABUS_GRAPH_PROMPT.format(syllabus_text=document_text)
    # --- FIXED: Pass is_json=True to ensure the LLM returns valid JSON ---
    response_json = get_llm_response(prompt, is_json=True)
    graph_data = json.loads(response_json)

    new_class = {
        "classId": class_id,
        "className": class_name,
        "concepts": graph_data.get("nodes", []),
        "edges": graph_data.get("edges", []),
    }
    CLASSES[class_id] = new_class
    
    # Save to persistent storage
    save_classes(CLASSES)
    
    app.logger.info(f"Added new class '{class_name}' with {len(new_class['concepts'])} concepts and {len(new_class['edges'])} edges.")
    return new_class

@app.route('/api/add_class', methods=['POST'])
def add_class():
    if 'className' not in request.form:
        return jsonify({"error": "Request must include 'className'."}), 400

    class_name = request.form['className']
    syllabus_file = request.files.get('syllabus')
    homework_file = request.files.get('homework')

    if not syllabus_file and not homework_file:
        return jsonify({"error": "Request must include a 'syllabus' or 'homework' file."}), 400

    try:
        if syllabus_file:
            # If a syllabus is provided, it's the source of truth.
            new_class = create_and_get_class(class_name, syllabus_file, 'syllabus')
            new_class['solutionStatus'] = 'SYLLABUS_BASED'
        else:
            # If only homework is provided, simulate the Proving Agent
            new_class = create_and_get_class(class_name, homework_file, 'homework')
            # MVP Simulation: Randomly decide if the agent "solved" it.
            new_class['solutionStatus'] = random.choice(['SOLVED', 'FAILED'])
        
        return jsonify(new_class)

    except Exception as e:
        app.logger.error(f"Failed to add class '{class_name}': {e}", exc_info=True)
        return jsonify({"error": "Failed to process the document."}), 500
    
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True)
