# backend/app.py

import os
import uuid
import json
import logging
import sys # --- ADDED: To allow exiting on critical errors ---
import random # --- ADDED: For Proving Agent MVP simulation ---
from pathlib import Path
from typing import Dict, Any
from datetime import datetime

try:
    from dotenv import load_dotenv
except ImportError:
    # Gracefully continue if python-dotenv isn't installed (e.g., Windows env not set up yet)
    def load_dotenv(*args, **kwargs):  # type: ignore
        logging.warning("python-dotenv not installed; skipping .env loading. Environment variables must be set externally.")
        return False
from flask import Flask, request, jsonify, session
from flask_cors import CORS
import fitz
 # --- ADDED: Import the Vertex AI library ---

import prompts
import metacognition
import rag_manager
from services.ingestion.document_ingestor import ingest_document
from services.quiz.quiz_generator import generate_quiz
from services.bkg.update_engine import load_or_init_student_state, update_with_item
from config.quiz_bkg_config import DATA_ROOT
from socratic_auditor import get_llm_response

# Centralize Vertex/GenAI environment init once per process
try:
    import vertex_init  # noqa: F401
except Exception as _e:
    logging.warning(f"Vertex/GenAI init module not loaded: {_e}")
from lean_verifier import lean_verifier_instance
from config.developer_config import developer_config, developer_logger
from llm_performance_tester import performance_tester 

# --- FIXED: Load environment variables and initialize AI services at startup ---
# Try loading .env from repo root and backend directory for cross-platform compatibility
try:
    repo_root = Path(__file__).resolve().parent.parent
    backend_dir = Path(__file__).resolve().parent
    # Load root .env first, then backend/.env to allow local overrides
    load_dotenv(repo_root / ".env")
    load_dotenv(backend_dir / ".env")
except Exception as e:
    logging.warning(f".env loading encountered an issue: {e}")

# Initialize Google AI
try:
    PROJECT_ID = os.environ.get("VERTEX_AI_PROJECT_ID")
    LOCATION = os.environ.get("VERTEX_AI_LOCATION")
    DEFAULT_MODEL = os.environ.get("DEFAULT_LLM_MODEL", "gemini-2.5-flash")
    
    if PROJECT_ID and LOCATION:
        logging.info(f"Google AI configured for project '{PROJECT_ID}' in '{LOCATION}' with model '{DEFAULT_MODEL}'.")
    else:
        logging.warning("VERTEX_AI_PROJECT_ID and VERTEX_AI_LOCATION not set. Running in development mode with local stub.")

except Exception as e:
    logging.warning(f"Google AI initialization failed: {e}. Continuing with local stub.")

# --- Flask App Initialization ---
app = Flask(__name__)
app.logger.setLevel(logging.INFO)
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-secret-key-replace-in-prod")
CORS(app, resources={r"/api/*": {"origins": "*"}}, supports_credentials=True)

# --- PERSISTENT CLASS STORAGE ---
CLASSES_FILE = Path.cwd() / "data" / "classes.json"
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

def contains_math(user_message: str) -> bool:
    """
    Helper function to detect if a user message contains mathematical content
    that should trigger Lean 4 verification.
    """
    math_keywords = [
        'prove', 'proof', 'theorem', 'lemma', 'corollary', 'show', 'verify',
        'group', 'subgroup', 'identity', 'inverse', 'associative', 'commutative',
        'element', 'operation', 'binary', 'closure', 'abelian', 'cyclic',
        'order', 'generator', 'coset', 'normal', 'quotient', 'homomorphism',
        'isomorphism', 'automorphism', 'kernel', 'image', 'direct product',
        'semi-direct', 'free', 'presentation', 'word', 'relation'
    ]
    
    message_lower = user_message.lower()
    return any(keyword in message_lower for keyword in math_keywords)

@app.route('/api/chat', methods=['POST'])
def handle_chat_message():
    if 'user_id' not in session:
        return jsonify({"error": "No active session."}), 401
    data = request.get_json()
    user_message = data['message']
    
    try:
        # Check if the message contains mathematical content
        if contains_math(user_message):
            # Use ProvingAgent for mathematical verification
            from socratic_auditor import ProvingAgent
            proving_agent = ProvingAgent()
            result = proving_agent.solve_problem(user_message)
            
            # Handle different result statuses
            if result['status'] == 'SOLVED':
                ai_response = f"Excellent! Your mathematical reasoning is correct. {result['feedback']}"
                is_verified = True
            elif result['status'] == 'FAILED':
                ai_response = f"I see an issue with your approach. {result['feedback']}"
                is_verified = False
            else:  # ERROR
                ai_response = f"Let me help you with that. {result['feedback']}"
                is_verified = None
                
            return jsonify({
                "aiResponse": ai_response,
                "proofCode": session['student_model']['current_proof_state'],
                "isVerified": is_verified,
                "verificationStatus": result['status']
            })
        else:
            # Use regular metacognition processing for non-mathematical content
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
    # Expect multipart/form-data with file + metadata fields
    class_id = request.form.get('classId')
    document_type = request.form.get('documentType', 'assignment')
    if not class_id:
        return jsonify({"error": "Request must include 'classId'."}), 400
    if 'file' not in request.files:
        return jsonify({"error": "No file part."}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({"error": "No selected file."}), 400
    if file:
        file_path, error = rag_manager.save_assignment_file(session['user_id'], file)
        if error:
            return jsonify({"error": error}), 500
        # Persist document metadata to the class record
        try:
            classes = load_classes()
            if class_id not in classes:
                return jsonify({"error": "Class not found."}), 404
            # Initialize documents array if missing
            documents = classes[class_id].get('documents', [])
            document_meta = {
                'documentId': str(uuid.uuid4()),
                'filename': file.filename,
                'documentType': document_type,
                'filePath': file_path,
                'uploadTimestamp': datetime.now().isoformat(),
                'status': 'uploaded'
            }
            documents.append(document_meta)
            classes[class_id]['documents'] = documents
            # Save and update in-memory cache
            save_classes(classes)
            global CLASSES
            CLASSES[class_id] = classes[class_id]
            return jsonify({
                "message": "File uploaded successfully.",
                "filePath": file_path,
                "document": document_meta
            }), 200
        except Exception as e:
            app.logger.error(f"Failed to persist document metadata: {e}", exc_info=True)
            return jsonify({"error": "File saved but metadata persistence failed."}), 500
    return jsonify({"error": "Invalid file."}), 400

# ======================================================================================
# == Quiz/BKG API Endpoints (MVP per implementation plan)
# ======================================================================================

@app.route('/api/courses/<course_id>/documents:upload', methods=['POST'])
def api_course_upload_document(course_id):
    if 'file' not in request.files:
        return jsonify({"error": "No file part."}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({"error": "No selected file."}), 400

    # Save to backend/user_uploads/<uuid>/<filename> first
    temp_path, error = rag_manager.save_assignment_file(course_id, file)
    if error:
        return jsonify({"error": error}), 500
    return jsonify({"filePath": temp_path}), 200


@app.route('/api/courses/<course_id>/ingest', methods=['POST'])
def api_course_ingest_document(course_id):
    data = request.get_json() or {}
    document_path = data.get('documentPath')
    force = bool(data.get('force', False))
    if not document_path:
        return jsonify({"error": "documentPath is required"}), 400
    result = ingest_document(course_id, document_path, force=force)
    return jsonify(result)


@app.route('/api/courses/<course_id>/quizzes:generate', methods=['POST'])
def api_generate_quiz(course_id):
    data = request.get_json() or {}
    student_id = data.get('studentId') or (session.get('user_id') if 'user_id' in session else None)
    if not student_id:
        return jsonify({"error": "studentId is required"}), 400
    target_concepts = data.get('targetConcepts')
    length = int(data.get('length', 5))
    difficulty = float(data.get('difficulty', 0.5))
    result = generate_quiz(course_id, student_id, target_concepts, length, difficulty)
    return jsonify(result)


@app.route('/api/courses/<course_id>/quizzes/<quiz_id>', methods=['GET'])
def api_get_quiz(course_id, quiz_id):
    quiz_path = Path(DATA_ROOT) / course_id / 'quizzes' / quiz_id / 'quiz.json'
    if not quiz_path.exists():
        return jsonify({"error": "Quiz not found"}), 404
    return jsonify(json.loads(quiz_path.read_text(encoding='utf-8')))


@app.route('/api/students/<student_id>/quizzes/<quiz_id>:submit', methods=['POST'])
def api_submit_quiz(student_id, quiz_id):
    data = request.get_json() or {}
    responses = data.get('responses', [])

    # Load quiz
    # courseId is part of stored quiz
    # Find course by searching known location
    for course_dir in (Path(DATA_ROOT)).glob('*'):
        qpath = course_dir / 'quizzes' / quiz_id / 'quiz.json'
        if qpath.exists():
            quiz = json.loads(qpath.read_text(encoding='utf-8'))
            course_id = quiz.get('course_id')
            break
    else:
        return jsonify({"error": "Quiz not found"}), 404

    state = load_or_init_student_state(course_id, student_id)

    # Map responses by itemId
    correctness_by_item: dict = {}
    for r in responses:
        item_id = r.get('itemId')
        resp = r.get('response')
        correctness_by_item[item_id] = bool(r.get('isCorrect')) if 'isCorrect' in r else None

    for item in quiz.get('items', []):
        item_id = item.get('id')
        if item_id not in correctness_by_item:
            continue
        is_correct = bool(correctness_by_item[item_id])
        concepts = item.get('concept_coverage', [])
        # equal weights for now
        weights = {cid: 1.0 for cid in concepts}
        state = update_with_item(course_id, student_id, state, weights, is_correct)

    return jsonify({
        "attemptId": str(uuid.uuid4()),
        "updatedBkg": state,
    })


@app.route('/api/students/<student_id>/courses/<course_id>/bkg', methods=['GET'])
def api_get_bkg(student_id, course_id):
    from services.bkg.update_engine import load_or_init_student_state
    state = load_or_init_student_state(course_id, student_id)
    return jsonify(state)

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

    # Initialize default knowledge state for each concept
    default_knowledge_state = {}
    for concept in graph_data.get("nodes", []):
        default_knowledge_state[concept['id']] = {
            'mu': 0.3,  # Default belief of mastery (30%)
            'sigma': 0.5  # Default uncertainty
        }
    
    new_class = {
        "classId": class_id,
        "className": class_name,
        "concepts": graph_data.get("nodes", []),
        "edges": graph_data.get("edges", []),
        "knowledgeState": default_knowledge_state,
        # Mission 1: initialize documents array for class-level document tracking
        "documents": [],
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

# ======================================================================================
# == Dashboard API Endpoints
# ======================================================================================

@app.route('/api/dashboard/classes', methods=['GET'])
def get_dashboard_classes():
    """Get all classes with their health data for the dashboard."""
    try:
        dashboard_classes = []
        for class_id, class_data in CLASSES.items():
            # Calculate health score based on knowledge state
            knowledge_state = class_data.get('knowledgeState', {})
            concepts = class_data.get('concepts', [])
            
            if concepts:
                total_mu = sum(knowledge_state.get(concept['id'], {}).get('mu', 0) for concept in concepts)
                health_score = round((total_mu / len(concepts)) * 100)
            else:
                health_score = 0
            
            # Count mastered concepts (mu >= 0.7)
            concepts_mastered = sum(1 for concept in concepts 
                                  if knowledge_state.get(concept['id'], {}).get('mu', 0) >= 0.7)
            
            # Determine plant state
            if health_score >= 80:
                plant_state = 'flourishing'
            elif health_score >= 60:
                plant_state = 'healthy'
            elif health_score >= 40:
                plant_state = 'wilting'
            else:
                plant_state = 'struggling'
            
            dashboard_class = {
                'id': class_id,
                'name': class_data['className'],
                'healthScore': health_score,
                'conceptsMastered': concepts_mastered,
                'totalConcepts': len(concepts),
                'lastSession': class_data.get('lastSession'),
                'plantState': plant_state,
                'createdAt': class_data.get('createdAt'),
                'updatedAt': class_data.get('updatedAt'),
            }
            dashboard_classes.append(dashboard_class)
        
        return jsonify(dashboard_classes)
        
    except Exception as e:
        app.logger.error(f"Failed to get dashboard classes: {e}", exc_info=True)
        return jsonify({"error": "Failed to retrieve dashboard data."}), 500

@app.route('/api/dashboard/stats', methods=['GET'])
def get_dashboard_stats():
    """Get quick stats for the dashboard."""
    try:
        total_concepts_mastered = 0
        total_classes = len(CLASSES)
        total_health_score = 0
        
        for class_data in CLASSES.values():
            knowledge_state = class_data.get('knowledgeState', {})
            concepts = class_data.get('concepts', [])
            
            # Count mastered concepts
            concepts_mastered = sum(1 for concept in concepts 
                                  if knowledge_state.get(concept['id'], {}).get('mu', 0) >= 0.7)
            total_concepts_mastered += concepts_mastered
            
            # Calculate health score
            if concepts:
                total_mu = sum(knowledge_state.get(concept['id'], {}).get('mu', 0) for concept in concepts)
                health_score = (total_mu / len(concepts)) * 100
                total_health_score += health_score
        
        average_health_score = round(total_health_score / total_classes) if total_classes > 0 else 0
        
        # TODO: Calculate from session data
        current_streak = 3
        flow_state_time = 45
        
        stats = {
            'totalConceptsMastered': total_concepts_mastered,
            'currentStreak': current_streak,
            'flowStateTime': flow_state_time,
            'totalClasses': total_classes,
            'averageHealthScore': average_health_score,
        }
        
        return jsonify(stats)
        
    except Exception as e:
        app.logger.error(f"Failed to get dashboard stats: {e}", exc_info=True)
        return jsonify({"error": "Failed to retrieve dashboard stats."}), 500

@app.route('/api/dashboard/class/<class_id>', methods=['GET'])
def get_class_data(class_id):
    """Get detailed class data for a specific class."""
    try:
        if class_id not in CLASSES:
            return jsonify({"error": "Class not found."}), 404
        
        class_data = CLASSES[class_id]
        
        # Ensure knowledge state exists and is properly initialized
        knowledge_state = class_data.get('knowledgeState', {})
        concepts = class_data.get('concepts', [])
        
        # Initialize knowledge state for any missing concepts
        for concept in concepts:
            if concept['id'] not in knowledge_state:
                knowledge_state[concept['id']] = {
                    'mu': 0.3,  # Default belief of mastery (30%)
                    'sigma': 0.5  # Default uncertainty
                }
        
        # Transform the data to match frontend expectations
        response_data = {
            'id': class_data.get('classId'),
            'name': class_data.get('className'),
            'healthScore': class_data.get('healthScore', 0),
            'lastSession': class_data.get('lastSession'),
            'nodes': concepts,  # Transform concepts to nodes
            'edges': class_data.get('edges', []),
            'knowledgeState': knowledge_state
        }
        
        return jsonify(response_data)
        
    except Exception as e:
        app.logger.error(f"Failed to get class data for {class_id}: {e}", exc_info=True)
        return jsonify({"error": "Failed to retrieve class data."}), 500

@app.route('/api/dashboard/class/<class_id>', methods=['DELETE'])
def delete_class(class_id):
    """Delete a class from persistent storage by its id."""
    try:
        if class_id not in CLASSES:
            return jsonify({"error": "Class not found."}), 404

        # Remove from in-memory storage
        deleted = CLASSES.pop(class_id, None)
        # Persist change
        save_classes(CLASSES)
        app.logger.info(f"Deleted class '{deleted.get('className') if deleted else class_id}' ({class_id})")
        return jsonify({"message": "Class deleted successfully."})
    except Exception as e:
        app.logger.error(f"Failed to delete class {class_id}: {e}", exc_info=True)
        return jsonify({"error": "Failed to delete class."}), 500

@app.route('/api/dashboard/update_session', methods=['POST'])
def update_session_data():
    """Update session data when a class session ends."""
    try:
        data = request.get_json()
        class_id = data.get('classId')
        knowledge_state = data.get('knowledgeState', {})
        
        if not class_id or class_id not in CLASSES:
            return jsonify({"error": "Invalid class ID."}), 400
        
        # Update the class data
        CLASSES[class_id]['knowledgeState'] = knowledge_state
        CLASSES[class_id]['lastSession'] = datetime.now().isoformat()
        CLASSES[class_id]['updatedAt'] = datetime.now().isoformat()
        
        # Save to persistent storage
        save_classes(CLASSES)
        
        return jsonify({"message": "Session data updated successfully."})
        
    except Exception as e:
        app.logger.error(f"Failed to update session data: {e}", exc_info=True)
        return jsonify({"error": "Failed to update session data."}), 500

# ======================================================================================
# == NEW: Enhanced Lean Verification Endpoints
# ======================================================================================

@app.route('/api/auto_solve_proof', methods=['POST'])
def auto_solve_proof():
    """Trigger AI auto-solving of a proof with configurable attempts."""
    try:
        data = request.get_json()
        proof_state = data.get('proof_state', '')
        max_attempts = data.get('max_attempts', None)
        
        if not proof_state:
            return jsonify({"error": "Proof state is required."}), 400
        
        # Run auto-solve
        result = lean_verifier_instance.auto_solve_proof(proof_state, max_attempts)
        
        return jsonify(result)
        
    except Exception as e:
        app.logger.error(f"Auto-solve failed: {e}", exc_info=True)
        return jsonify({"error": f"Auto-solve failed: {str(e)}"}), 500

@app.route('/api/developer_mode', methods=['POST'])
def toggle_developer_mode():
    """Toggle developer mode on/off."""
    try:
        data = request.get_json()
        enabled = data.get('enabled', False)
        max_attempts = data.get('max_attempts', 5)
        
        lean_verifier_instance.set_developer_mode(enabled)
        lean_verifier_instance.set_max_attempts(max_attempts)
        
        return jsonify({
            "message": f"Developer mode {'enabled' if enabled else 'disabled'}",
            "developer_mode": enabled,
            "max_attempts": max_attempts
        })
        
    except Exception as e:
        app.logger.error(f"Failed to toggle developer mode: {e}", exc_info=True)
        return jsonify({"error": f"Failed to toggle developer mode: {str(e)}"}), 500

@app.route('/api/developer_logs', methods=['GET'])
def get_developer_logs():
    """Get developer mode logs and configuration."""
    try:
        logs = lean_verifier_instance.get_developer_logs()
        return jsonify(logs)
        
    except Exception as e:
        app.logger.error(f"Failed to get developer logs: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get developer logs: {str(e)}"}), 500

@app.route('/api/developer_logs/clear', methods=['POST'])
def clear_developer_logs():
    """Clear all developer logs."""
    try:
        developer_logger.clear_logs()
        app.logger.info("Developer logs cleared successfully")
        return jsonify({"message": "Developer logs cleared successfully"})
        
    except Exception as e:
        app.logger.error(f"Failed to clear developer logs: {e}", exc_info=True)
        return jsonify({"error": f"Failed to clear developer logs: {str(e)}"}), 500

@app.route('/api/upload_homework', methods=['POST'])
def upload_homework():
    """Enhanced homework processing with auto-solve functionality."""
    try:
        if 'file' not in request.files:
            return jsonify({"error": "No file provided."}), 400
        
        file = request.files['file']
        if file.filename == '':
            return jsonify({"error": "No file selected."}), 400
        
        # Extract text from file
        file_content = ""
        if file.filename.endswith('.pdf'):
            file_content = extract_text_from_pdf(file.stream)
        elif file.filename.endswith('.txt'):
            file_content = file.read().decode('utf-8')
        else:
            return jsonify({"error": "Unsupported file type. Please upload PDF or TXT."}), 400
        
        # Parse mathematical content into Lean theorem statements
        # This is a simplified version - in practice, you'd want more sophisticated parsing
        lean_theorems = []
        lines = file_content.split('\n')
        current_theorem = ""
        
        for line in lines:
            if any(keyword in line.lower() for keyword in ['theorem', 'lemma', 'proposition']):
                if current_theorem:
                    lean_theorems.append(current_theorem.strip())
                current_theorem = line
            elif current_theorem and line.strip():
                current_theorem += "\n" + line
        
        if current_theorem:
            lean_theorems.append(current_theorem.strip())
        
        # If no theorems found, create a basic one from the content
        if not lean_theorems:
            lean_theorems = [f"theorem homework_problem : True := by\n  sorry"]
        
        # Initialize proof states with "sorry"
        proof_states = []
        for theorem in lean_theorems:
            if "sorry" not in theorem:
                theorem += "\n  sorry"
            proof_states.append(theorem)
        
        # Enable developer mode for homework auto-solve to log attempts
        original_developer_mode = lean_verifier_instance.developer_mode
        lean_verifier_instance.developer_mode = True
        
        # Trigger auto-solve for each proof
        solutions = []
        for i, proof_state in enumerate(proof_states):
            try:
                result = lean_verifier_instance.auto_solve_proof(proof_state)
                solutions.append({
                    "theorem_index": i,
                    "original_state": proof_states[i],
                    "solution": result
                })
            except Exception as e:
                solutions.append({
                    "theorem_index": i,
                    "original_state": proof_states[i],
                    "solution": {"solved": False, "error": str(e)}
                })
        
        # Restore original developer mode setting
        lean_verifier_instance.developer_mode = original_developer_mode
        
        return jsonify({
            "file_name": file.filename,
            "theorems_found": len(lean_theorems),
            "proof_states": proof_states,
            "solutions": solutions
        })
        
    except Exception as e:
        app.logger.error(f"Homework upload failed: {e}", exc_info=True)
        return jsonify({"error": f"Homework upload failed: {str(e)}"}), 500

# ======================================================================================
# == LLM Performance Testing Endpoints
# ======================================================================================

@app.route('/api/performance/run_tests', methods=['POST'])
def run_performance_tests():
    """Run the complete LLM performance test suite."""
    try:
        app.logger.info("Starting LLM performance test suite")
        
        # Run the full test suite
        report = performance_tester.run_full_test_suite()
        
        # Save the report
        filename = f"llm_performance_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md"
        filepath = performance_tester.save_report(report, filename)
        
        # Return summary and file path
        return jsonify({
            "message": "Performance test suite completed successfully",
            "report_file": filename,
            "summary": {
                "total_tests": report.total_tests,
                "successful_tests": report.successful_tests,
                "failed_tests": report.failed_tests,
                "success_rate": report.success_rate,
                "average_attempts": report.average_attempts,
                "average_time": report.average_time
            },
            "results_by_difficulty": report.results_by_difficulty,
            "results_by_category": report.results_by_category,
            "llm_quality_metrics": report.llm_quality_metrics
        })
        
    except Exception as e:
        app.logger.error(f"Performance testing failed: {e}", exc_info=True)
        return jsonify({"error": f"Performance testing failed: {str(e)}"}), 500

@app.route('/api/performance/test_cases', methods=['GET'])
def get_test_cases():
    """Get all available test cases."""
    try:
        test_cases = []
        for test_case in performance_tester.test_cases:
            test_cases.append({
                "name": test_case.name,
                "description": test_case.description,
                "proof_state": test_case.proof_state,
                "expected_tactic": test_case.expected_tactic,
                "difficulty": test_case.difficulty,
                "category": test_case.category,
                "max_attempts": test_case.max_attempts
            })
        
        return jsonify({
            "test_cases": test_cases,
            "total_count": len(test_cases)
        })
        
    except Exception as e:
        app.logger.error(f"Failed to get test cases: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get test cases: {str(e)}"}), 500

@app.route('/api/performance/run_single_test', methods=['POST'])
def run_single_test():
    """Run a single test case by name."""
    try:
        data = request.get_json()
        test_name = data.get('test_name')
        
        if not test_name:
            return jsonify({"error": "test_name is required"}), 400
        
        # Find the test case
        test_case = None
        for tc in performance_tester.test_cases:
            if tc.name == test_name:
                test_case = tc
                break
        
        if not test_case:
            return jsonify({"error": f"Test case '{test_name}' not found"}), 404
        
        # Run the test
        result = performance_tester.run_single_test(test_case)
        
        return jsonify({
            "test_name": test_case.name,
            "success": result.success,
            "attempts_used": result.attempts_used,
            "total_time": result.total_time,
            "attempts": result.attempts,
            "final_proof": result.final_proof,
            "error_messages": result.error_messages,
            "llm_response_quality": result.llm_response_quality
        })
        
    except Exception as e:
        app.logger.error(f"Single test execution failed: {e}", exc_info=True)
        return jsonify({"error": f"Single test execution failed: {str(e)}"}), 500

@app.route('/api/performance/reports', methods=['GET'])
def get_performance_reports():
    """Get list of available performance reports."""
    try:
        reports_dir = os.path.join(os.path.dirname(__file__), "reports")
        if not os.path.exists(reports_dir):
            return jsonify({"reports": [], "total_count": 0})
        
        reports = []
        for filename in os.listdir(reports_dir):
            if filename.endswith('.md'):
                filepath = os.path.join(reports_dir, filename)
                stat = os.stat(filepath)
                reports.append({
                    "filename": filename,
                    "created": datetime.fromtimestamp(stat.st_mtime).isoformat(),
                    "size": stat.st_size
                })
        
        # Sort by creation time (newest first)
        reports.sort(key=lambda x: x['created'], reverse=True)
        
        return jsonify({
            "reports": reports,
            "total_count": len(reports)
        })
        
    except Exception as e:
        app.logger.error(f"Failed to get performance reports: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get performance reports: {str(e)}"}), 500

@app.route('/api/performance/download_report/<filename>', methods=['GET'])
def download_performance_report(filename):
    """Download a specific performance report."""
    try:
        reports_dir = os.path.join(os.path.dirname(__file__), "reports")
        filepath = os.path.join(reports_dir, filename)
        
        if not os.path.exists(filepath):
            return jsonify({"error": f"Report '{filename}' not found"}), 404
        
        with open(filepath, 'r') as f:
            content = f.read()
        
        return jsonify({
            "filename": filename,
            "content": content
        })
        
    except Exception as e:
        app.logger.error(f"Failed to download report: {e}", exc_info=True)
        return jsonify({"error": f"Failed to download report: {str(e)}"}), 500

@app.route('/api/performance/stats', methods=['GET'])
def get_performance_stats():
    """Get comprehensive performance statistics."""
    try:
        stats = lean_verifier_instance.get_performance_stats()
        return jsonify(stats)
        
    except Exception as e:
        app.logger.error(f"Failed to get performance stats: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get performance stats: {str(e)}"}), 500

@app.route('/api/performance/cache/toggle', methods=['POST'])
def toggle_cache():
    """Toggle proof caching on/off."""
    try:
        data = request.get_json() or {}
        enabled = data.get('enabled')
        
        cache_status = lean_verifier_instance.toggle_cache(enabled)
        return jsonify({
            "cache_enabled": cache_status,
            "message": f"Proof caching {'enabled' if cache_status else 'disabled'}"
        })
        
    except Exception as e:
        app.logger.error(f"Failed to toggle cache: {e}", exc_info=True)
        return jsonify({"error": f"Failed to toggle cache: {str(e)}"}), 500

@app.route('/api/performance/cache/clear', methods=['POST'])
def clear_cache():
    """Clear the proof cache."""
    try:
        lean_verifier_instance.clear_cache()
        return jsonify({"message": "Proof cache cleared successfully"})
        
    except Exception as e:
        app.logger.error(f"Failed to clear cache: {e}", exc_info=True)
        return jsonify({"error": f"Failed to clear cache: {str(e)}"}), 500

@app.route('/api/performance/environment/optimize', methods=['POST'])
def optimize_environment():
    """Manually trigger Lean environment optimization."""
    try:
        data = request.get_json() or {}
        force_rebuild = data.get('force_rebuild', False)
        
        success = lean_verifier_instance.optimize_environment(force_rebuild)
        
        if success:
            return jsonify({
                "success": True,
                "message": "Lean environment optimization completed successfully"
            })
        else:
            return jsonify({
                "success": False,
                "message": "Lean environment optimization failed"
            }), 500
        
    except Exception as e:
        app.logger.error(f"Failed to optimize environment: {e}", exc_info=True)
        return jsonify({"error": f"Failed to optimize environment: {str(e)}"}), 500

@app.route('/api/performance/cache/stats', methods=['GET'])
def get_cache_stats():
    """Get detailed cache statistics."""
    try:
        from proof_cache import proof_cache
        stats = proof_cache.get_cache_stats()
        return jsonify(stats)
        
    except Exception as e:
        app.logger.error(f"Failed to get cache stats: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get cache stats: {str(e)}"}), 500

@app.route('/api/performance/environment/stats', methods=['GET'])
def get_environment_stats():
    """Get Lean environment statistics."""
    try:
        from lean_environment_manager import get_lean_environment_status
        stats = get_lean_environment_status()
        return jsonify(stats)
        
    except Exception as e:
        app.logger.error(f"Failed to get environment stats: {e}", exc_info=True)
        return jsonify({"error": f"Failed to get environment stats: {str(e)}"}), 500

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True)
