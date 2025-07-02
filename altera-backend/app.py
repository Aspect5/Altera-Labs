# app.py

import os
import uuid
import subprocess
import json
from flask import Flask, request, jsonify
from flask_cors import CORS
from dotenv import load_dotenv
import requests
from typing import Any, Dict
import fitz

# Load environment variables
load_dotenv()

# --- Configuration & Debugging ---
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
REQUESTS_CA_BUNDLE = os.getenv("REQUESTS_CA_BUNDLE")
LAKE_EXECUTABLE = os.getenv("LAKE_EXECUTABLE_PATH", "lake")

# --- Verifier Configuration ---
LEAN_PROJECT_PATH = os.path.join(os.path.dirname(__file__), 'lean_verifier')
# REFACTOR: Using the main project file known to Lake.
LEAN_TARGET_FILENAME = "LeanVerifier.lean"
LEAN_TARGET_FILE_PATH = os.path.join(LEAN_PROJECT_PATH, LEAN_TARGET_FILENAME)

print("--- Altera Labs Backend Starting ---")
print(f"GEMINI_API_KEY Loaded: {'Yes' if GEMINI_API_KEY else 'No'}")
print(f"LAKE_EXECUTABLE Path: {LAKE_EXECUTABLE}")
print(f"Lean Project Path: {LEAN_PROJECT_PATH}")
print("------------------------------------")

# Initialize Flask App and CORS
app = Flask(__name__)
CORS(app)

# --- In-Memory Data Storage ---
db = {"sessions": {}, "classes": {}}

LEAN_PROOF_BOILERPLATE = """
import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic

-- This is the formal statement of the theorem we are trying to prove.
theorem uniqueness_of_identity_element {G : Type*} [Group G] :
  ∀ (e f : G), is_identity e → is_identity f → e = f :=
begin
  -- Let e and f be two identity elements in the group G.
  intros e f he hf,
  -- Our goal is to prove that e = f.
  -- The proof state is now ready for your first step.

  -- STUDENT TACTICS WILL BE INSERTED HERE

end
"""

# --- Gemini API Helper Function ---
def call_gemini(prompt, is_json_output=False):
    if not GEMINI_API_KEY:
        return "Error: GEMINI_API_KEY not configured."

    model_name = "gemini-1.5-flash-latest"
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={GEMINI_API_KEY}"
    
    payload: Dict[str, Any] = { "contents": [{"role": "user", "parts": [{"text": prompt}]}] }
    
    if is_json_output:
        # For structured responses like the intent classifier
        payload["generationConfig"] = { "responseMimeType": "application/json" }

    headers = {'Content-Type': 'application/json'}
    ssl_verify = REQUESTS_CA_BUNDLE if REQUESTS_CA_BUNDLE else True

    try:
        response = requests.post(url, headers=headers, data=json.dumps(payload), verify=ssl_verify)
        response.raise_for_status()
        result = response.json()
        if 'candidates' in result and result['candidates'] and result['candidates'][0]['content']['parts']:
            return result['candidates'][0]['content']['parts'][0]['text']
        else:
            print("Gemini API response malformed:", result)
            return "Error: Could not parse response from AI."
    except requests.exceptions.RequestException as e:
        print(f"Error calling Gemini API: {e}")
        return "Error: Could not connect to the AI service."

# --- Lean Verifier Function (Unchanged, but now called conditionally) ---
def run_lean_verifier(lean_code: str) -> tuple[bool, str]:
    if not os.path.isdir(LEAN_PROJECT_PATH):
        error_msg = f"Lean project directory not found at: {LEAN_PROJECT_PATH}"
        return False, error_msg
    try:
        with open(LEAN_TARGET_FILE_PATH, 'w', encoding='utf-8') as f:
            f.write(lean_code)
        # REFACTOR: Build the default project target, not a specific file.
        process = subprocess.run(
            [LAKE_EXECUTABLE, 'build'],
            cwd=LEAN_PROJECT_PATH, capture_output=True, text=True, check=True, timeout=30
        )
        return True, "Proof step verified successfully."
    except FileNotFoundError:
        return False, f"Error: The lake executable was not found at '{LAKE_EXECUTABLE}'. Check LAKE_EXECUTABLE_PATH."
    except subprocess.TimeoutExpired:
        return False, "Lean verification timed out."
    except subprocess.CalledProcessError as e:
        error_message = e.stderr.strip()
        if "goals accomplished" in error_message:
             return True, "Proof completed successfully."
        return False, error_message
    except Exception as e:
        return False, f"An unexpected error occurred during verification: {str(e)}"

# --- API Endpoints ---
@app.route("/")
def index():
    return "Altera Labs Backend is running."

@app.route("/addClass", methods=["POST"])
def add_class():
    if 'className' not in request.form or 'syllabus' not in request.files:
        return jsonify({"error": "Missing className or syllabus"}), 400

    class_name = request.form['className']
    syllabus_file = request.files['syllabus']
    class_id = str(uuid.uuid4())
    
    syllabus_text = ""
    try:
        # Simple check for PDF mimetype or extension
        is_pdf = syllabus_file.filename and syllabus_file.filename.lower().endswith('.pdf')
        if syllabus_file.mimetype == 'application/pdf' or is_pdf:
            with fitz.open(stream=syllabus_file.read(), filetype="pdf") as doc:
                for page in doc:
                    syllabus_text += page.get_text() # type: ignore
        else:
            syllabus_text = syllabus_file.read().decode('utf-8')
    except Exception as e:
        print(f"Error processing syllabus: {e}")
        return jsonify({"error": f"Could not process syllabus file. Error: {e}"}), 500

    # We need a JSON prompt for this
    prompt = f"""
Extract the key mathematical or computer science concepts from this syllabus. 
Return them as a JSON object with a single key "concepts" which is an array of strings. 
If the content is unreadable or not a syllabus, return an empty array. 

Syllabus content:
---
{syllabus_text[:8000]}
---
"""
    concepts_json_str = call_gemini(prompt, is_json_output=True)
    
    concepts = []
    try:
        concepts_data = json.loads(concepts_json_str)
        concepts = concepts_data.get("concepts", [])
    except (json.JSONDecodeError, TypeError):
        print("Failed to decode JSON from Gemini for concepts.")

    if "classes" not in db:
        db["classes"] = {}
        
    db["classes"][class_id] = {
        "name": class_name,
        "concepts": concepts
    }
    
    # Return everything the frontend needs to render the new class card
    return jsonify({
        "status": "success", 
        "classId": class_id, 
        "className": class_name,
        "concepts": concepts
    })


@app.route("/explainConcept", methods=["POST"])
def explain_concept():
    data = request.get_json()
    if not data or 'concept' not in data:
        return jsonify({"error": "Missing 'concept' in request"}), 400
    
    concept = data['concept']
    prompt = f"Please provide a concise, university-level explanation for the following concept: '{concept}'. Focus on the core definition and its significance."
    explanation = call_gemini(prompt)

    return jsonify({"explanation": explanation})

@app.route("/startSession", methods=["POST"])
def start_session():
    session_id = str(uuid.uuid4())
    db["sessions"][session_id] = {
        "proof_code": LEAN_PROOF_BOILERPLATE,
        "history": [],
        "problem": "Uniqueness of the Identity Element"
    }
    print(f"New session started: {session_id}")
    return jsonify({
        "sessionId": session_id,
        "proof_code": LEAN_PROOF_BOILERPLATE,
        "ai_response_text": "Welcome! We're going to prove that the identity element in a group is unique. The formal proof state is on the right. What is your first logical step?"
    })

## NEW: Function to classify user intent
def classify_user_intent(user_message: str) -> str:
    """
    Uses an LLM to classify the user's message into one of three categories.
    """
    prompt = f"""
Analyze the user's message and classify its primary intent into one of three categories: PROOF_STEP, QUESTION, or META_COMMENT.
Return a JSON object with a single key "intent".

1.  **PROOF_STEP**: The user is describing a logical action to advance a mathematical proof.
    *   Examples: "apply the definition of identity", "use theorem 2.1", "rewrite he at hf", "let's assume e*f = f"

2.  **QUESTION**: The user is asking for a definition, an explanation, or for help.
    *   Examples: "what is a group?", "I don't understand", "can you help me?", "why did that work?"

3.  **META_COMMENT**: The user is making a conversational remark, expressing an emotion, or testing the system.
    *   Examples: "hello", "this is hard", "I'm stuck", "test", "ok thanks"

User Message: "{user_message}"

JSON:
"""
    response_str = call_gemini(prompt, is_json_output=True)
    try:
        data = json.loads(response_str)
        intent = data.get("intent", "META_COMMENT") # Default to meta_comment on failure
        if intent not in ["PROOF_STEP", "QUESTION", "META_COMMENT"]:
            return "META_COMMENT" # Sanitize output
        return intent
    except (json.JSONDecodeError, TypeError):
        return "META_COMMENT" # Default to meta_comment on any error


## REFACTOR: Complete overhaul of sendMessage to use the Intent Router
@app.route("/sendMessage", methods=["POST"])
def send_message():
    data = request.get_json()
    session_id = data.get("sessionId")
    user_message = data.get("message")

    if not all([session_id, user_message]):
        return jsonify({"error": "Missing sessionId or message"}), 400
    if session_id not in db["sessions"]:
        return jsonify({"error": "Session not found"}), 404

    session = db["sessions"][session_id]
    current_proof_code = session["proof_code"]
    
    # --- STEP 1: CLASSIFY INTENT ---
    intent = classify_user_intent(user_message)
    print(f"Session {session_id}: User Message='{user_message}', Intent='{intent}'")

    ai_response_text = ""
    is_verified = None # Use None to signify "not a proof step"

    # --- STEP 2: ROUTE BASED ON INTENT ---

    if intent == "PROOF_STEP":
        # --- This is our original verifier loop ---
        tactic_generation_prompt = f"""
You are an expert in Lean 4. Translate the student's natural language statement into a single Lean 4 tactic, given the current proof state.
Current Proof State:
```lean
{current_proof_code}
```
Student's Statement: "{user_message}"
Tactic:
"""
        generated_tactic = call_gemini(tactic_generation_prompt).strip().replace("`", "")
        print(f"Generated Tactic: {generated_tactic}")
        
        placeholder = "-- STUDENT TACTICS WILL BE INSERTED HERE"
        candidate_code = current_proof_code.replace(placeholder, f"  {generated_tactic},\n  {placeholder}")
        
        is_verified, verifier_output = run_lean_verifier(candidate_code)

        if is_verified:
            session["proof_code"] = candidate_code
            ai_response_text = f"Excellent! The step `{generated_tactic}` is correct. The proof state has been updated. What's next?"
            # Add completion check here later
        else:
            hint_generation_prompt = f"""
As a Socratic AI tutor, a student's proof step failed. Their goal was '{user_message}', we tried `{generated_tactic}`, and the Lean verifier gave this error:
'{verifier_output}'
Do not show the raw error. Formulate a gentle Socratic question or hint to guide them.
Your Hint:
"""
            ai_response_text = call_gemini(hint_generation_prompt)

    elif intent == "QUESTION":
        # --- Handle questions socratically ---
        qa_prompt = f"""
A student is working on a proof for the uniqueness of the identity element and asked a question.
Answer their question concisely, then ask a follow-up Socratic question to guide them back to the proof.
Student's Question: "{user_message}"
Your Answer:
"""
        ai_response_text = call_gemini(qa_prompt)
        is_verified = None

    elif intent == "META_COMMENT":
        # --- Handle conversational comments and tests ---
        
        # REFACTOR: New, improved prompt to give the AI more personality and freedom.
        meta_prompt = f"""
            You are Altera, a friendly and personable AI cognitive partner.
            A student working on a proof has sent a conversational message instead of a proof step. Your goal is to build rapport and keep the student engaged. 
            Acknowledge their specific comment in a human-like way, then gently guide them back to the task. Avoid being repetitive.

            --- EXAMPLES ---
            Student's Comment: "are you awake?"
            Your Encouraging Response: "I am! Ready to tackle this proof when you are."

            Student's Comment: "this is hard"
            Your Encouraging Response: "It can definitely be challenging, but breaking it down step-by-step helps a lot. What's on your mind for the next move?"

            Student's Comment: "making sure you work"
            Your Encouraging Response: "Test successful! I'm here and ready. What's our first logical step?"

            Student's Comment: "thanks"
            Your Encouraging Response: "You're welcome! What should we look at next?"
            --- END EXAMPLES ---

            Now, respond to the student's actual comment below.

            Student's Comment: "{user_message}"
            Your Encouraging Response:
            """
        ai_response_text = call_gemini(meta_prompt)
        is_verified = None

    # Add conversation to history
    session["history"].append({"role": "user", "parts": [{"text": user_message}]})
    session["history"].append({"role": "model", "parts": [{"text": ai_response_text}]})

    return jsonify({
        "ai_response_text": ai_response_text,
        "proof_code": session["proof_code"],
        "is_verified": is_verified, # Can be True, False, or null
    })


if __name__ == '__main__':
    app.run(debug=True, port=5000)