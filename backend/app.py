# app.py

import os
import uuid
import subprocess
import json
from flask import Flask, request, jsonify
from flask.wrappers import Response
from flask_cors import CORS
from dotenv import load_dotenv
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from typing import Any, Dict, List, Optional, Union
import fitz # PyMuPDF

# Load environment variables from a .env file
load_dotenv()

# --- Configuration & Debugging ---
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
REQUESTS_CA_BUNDLE = os.getenv("REQUESTS_CA_BUNDLE") # For corporate proxies
LAKE_EXECUTABLE = os.getenv("LAKE_EXECUTABLE_PATH", "lake")

# --- Verifier Configuration ---
LEAN_PROJECT_PATH = os.path.join(os.path.dirname(__file__), 'lean_verifier')
LEAN_TARGET_FILENAME = "LeanVerifier.lean"
LEAN_TARGET_FILE_PATH = os.path.join(LEAN_PROJECT_PATH, LEAN_TARGET_FILENAME)

print("--- Altera Labs Backend Starting ---")
print(f"GEMINI_API_KEY Loaded: {'Yes' if GEMINI_API_KEY else 'No'}")
print(f"LAKE_EXECUTABLE Path: {LAKE_EXECUTABLE}")
print(f"Lean Project Path: {LEAN_PROJECT_PATH}")
print("------------------------------------")

# Initialize Flask App and enable Cross-Origin Resource Sharing
app = Flask(__name__)
CORS(app)

# --- In-Memory Data Storage ---
db: Dict[str, Dict[str, Any]] = {"sessions": {}, "classes": {}}

# --- Boilerplate Lean Code ---
LEAN_PROOF_BOILERPLATE = """
import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic

theorem uniqueness_of_identity_element {G : Type*} [Group G] :
  ∀ (e f : G), (∀ a, e * a = a) → (∀ a, f * a = a) → e = f :=
begin
  intros e f he hf,
  -- STUDENT TACTICS WILL BE INSERTED HERE
end
"""

# --- Intelligent Model Selection & API Call Logic ---

_RETRY = Retry(total=3, backoff_factor=0.5, status_forcelist=[429, 500, 502, 503, 504])
_LAST_SUCCESSFUL_MODEL: Optional[str] = None
_PREFERRED_MODEL_TIERS = [ "gemini-2.5-pro", "gemini-2.5-flash" ]

def local_llm_stub(prompt: str, is_json_output: bool = False) -> Union[str, Dict[str, Any]]:
    """A stub for a local model, used as a final fallback."""
    print("[Fallback] Using local LLM stub.")
    if is_json_output:
        return {"error": "All remote models failed, and local LLM is a stub."}
    return "Error: All remote AI models are currently unavailable. Please try again later."

def call_gemini(prompt: str, history: List[Dict[str, Any]], *, is_json_output: bool = False) -> Union[str, Dict[str, Any]]:
    """Intelligently queries a curated list of high-quality Gemini models with retries."""
    global _LAST_SUCCESSFUL_MODEL
    if not GEMINI_API_KEY:
        return local_llm_stub(prompt, is_json_output)

    sess = requests.Session()
    sess.mount("https://", HTTPAdapter(max_retries=_RETRY))
    headers = {"Content-Type": "application/json"}
    
    models_to_try: List[str] = []
    seen_models = set()
    if _LAST_SUCCESSFUL_MODEL:
        models_to_try.append(_LAST_SUCCESSFUL_MODEL)
        seen_models.add(_LAST_SUCCESSFUL_MODEL)
    for model in _PREFERRED_MODEL_TIERS:
        if model not in seen_models: models_to_try.append(model)
    
    print(f"[Gemini] Models to try, in order: {models_to_try}")

    contents = history + [{"role": "user", "parts": [{"text": prompt}]}]
    gen_config = {"responseMimeType": "application/json"} if is_json_output else {}
    
    for model_name in models_to_try:
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={GEMINI_API_KEY}"
        payload = {"contents": contents, "generationConfig": gen_config}
        try:
            resp = sess.post(url, headers=headers, json=payload, timeout=25, verify=REQUESTS_CA_BUNDLE or True)
            if resp.ok:
                _LAST_SUCCESSFUL_MODEL = model_name
                response_data = resp.json()
                try:
                    text_content = response_data['candidates'][0]['content']['parts'][0]['text']
                    return json.loads(text_content) if is_json_output else text_content
                except (KeyError, IndexError, json.JSONDecodeError) as e:
                    print(f"[Gemini] Error parsing successful response from {model_name}: {e}")
            else:
                print(f"[Gemini] {model_name} failed with HTTP {resp.status_code}: {resp.text}")
                if _LAST_SUCCESSFUL_MODEL == model_name: _LAST_SUCCESSFUL_MODEL = None
        except requests.exceptions.RequestException as e:
            print(f"[Gemini] Request to {model_name} failed: {e}")
            if _LAST_SUCCESSFUL_MODEL == model_name: _LAST_SUCCESSFUL_MODEL = None
    return local_llm_stub(prompt, is_json_output)

# --- Lean Verifier Function ---
def run_lean_verifier(lean_code: str) -> tuple[bool, str]:
    if not os.path.isdir(LEAN_PROJECT_PATH): return False, f"Lean project directory not found: {LEAN_PROJECT_PATH}"
    try:
        with open(LEAN_TARGET_FILE_PATH, 'w', encoding='utf-8') as f: f.write(lean_code)
        process = subprocess.run([LAKE_EXECUTABLE, 'build'], cwd=LEAN_PROJECT_PATH, capture_output=True, text=True, check=True, timeout=30)
        return True, "Proof step verified successfully."
    except FileNotFoundError: return False, f"Error: lake executable not found at '{LAKE_EXECUTABLE}'."
    except subprocess.TimeoutExpired: return False, "Lean verification timed out."
    except subprocess.CalledProcessError as e:
        error_message = e.stderr.strip()
        return ("goals accomplished" in error_message, error_message)
    except Exception as e: return False, f"An unexpected error occurred: {str(e)}"

# --- API Endpoints ---

@app.route("/")
def index() -> str: return "Altera Labs Backend is running."

@app.route("/addClass", methods=["POST"])
def add_class() -> Union[Response, tuple[Response, int]]:
    if 'className' not in request.form or 'syllabus' not in request.files:
        return jsonify({"error": "Missing className or syllabus file"}), 400
    class_name, syllabus_file = request.form['className'], request.files['syllabus']
    class_id, syllabus_text = str(uuid.uuid4()), ""
    try:
        if syllabus_file.filename and syllabus_file.filename.lower().endswith('.pdf'):
            with fitz.open(stream=syllabus_file.read(), filetype="pdf") as doc:
                syllabus_text = "".join(page.get_text() for page in doc) # type: ignore
        else: syllabus_text = syllabus_file.read().decode('utf-8')
    except Exception as e: return jsonify({"error": f"Could not process syllabus file: {e}"}), 500
    prompt = f'Extract key concepts from this syllabus into a JSON object with a "concepts" key (array of strings): --- {syllabus_text[:8000]} ---'
    concepts_response = call_gemini(prompt, history=[], is_json_output=True)
    concepts = concepts_response.get("concepts", []) if isinstance(concepts_response, dict) else []
    db["classes"][class_id] = { "name": class_name, "concepts": concepts }
    return jsonify({ "status": "success", "classId": class_id, "className": class_name, "concepts": concepts })

@app.route("/explainConcept", methods=["POST"])
def explain_concept() -> Union[Response, tuple[Response, int]]:
    data = request.get_json()
    if not data or 'concept' not in data: return jsonify({"error": "Missing 'concept' in request"}), 400
    prompt = f"Provide a concise, university-level explanation for '{data['concept']}', using LaTeX for math."
    explanation = call_gemini(prompt, history=[])
    return jsonify({"explanation": explanation})

@app.route("/startSession", methods=["POST"])
def start_session() -> Response:
    session_id = str(uuid.uuid4())
    initial_history = [{"role": "user", "parts": [{"text": "Start."}]}, {"role": "model", "parts": [{"text": "Welcome! We're proving the uniqueness of the identity element. The formal proof state is on the right. What is your first logical step?"}]}]
    db["sessions"][session_id] = { "proof_code": LEAN_PROOF_BOILERPLATE, "history": initial_history }
    print(f"New session started: {session_id}")
    return jsonify({ "sessionId": session_id, "proof_code": LEAN_PROOF_BOILERPLATE, "ai_response_text": initial_history[1]["parts"][0]["text"] })

def classify_user_intent(user_message: str, history: List[Dict[str, Any]]) -> str:
    prompt = f"""
Analyze the user's message and classify its intent. Choose one of:
- **PROOF_STRATEGY**: The user provides a multi-step plan, a full proof, or a high-level approach. (e.g., "First I'll show e*f=f, then e*f=e, then they must be equal.")
- **PROOF_STEP**: The user states a single, direct logical action to advance the proof. (e.g., "rewrite he at hf", "apply the definition of identity")
- **QUESTION**: The user asks for a definition, an explanation, or help. (e.g., "what is a group?", "why did that work?")
- **META_COMMENT**: A conversational remark. (e.g., "hello", "this is hard", "ok thanks")

Return a JSON object with a single key "intent".
User Message: "{user_message}"
JSON:
"""
    response = call_gemini(prompt, history, is_json_output=True)
    if isinstance(response, dict) and "intent" in response:
        intent = response["intent"]
        return intent if intent in ["PROOF_STRATEGY", "PROOF_STEP", "QUESTION", "META_COMMENT"] else "META_COMMENT"
    return "META_COMMENT"

@app.route("/sendMessage", methods=["POST"])
def send_message() -> Union[Response, tuple[Response, int]]:
    data = request.get_json()
    session_id, user_message = data.get("sessionId"), data.get("message")

    if not all([session_id, user_message]): return jsonify({"error": "Missing sessionId or message"}), 400
    if session_id not in db["sessions"]: return jsonify({"error": "Session not found"}), 404

    session = db["sessions"][session_id]
    intent = classify_user_intent(user_message, session["history"])
    print(f"Session {session_id}: User Message='{user_message}', Intent='{intent}'")

    ai_response_text: Union[str, Dict[str, Any]] = ""
    is_verified: Optional[bool] = None
    current_proof_code = session['proof_code']
    placeholder = "-- STUDENT TACTICS WILL BE INSERTED HERE"

    if intent == "PROOF_STRATEGY":
        # --- REVISED: Handle full proof strategies more intelligently ---
        print("[Strategy] User provided a full strategy. Attempting to translate to Lean.")
        strategy_prompt = f"""
Act as an expert mathematician and Lean 4 programmer. Your task is to translate a user's natural language proof strategy into a sequence of precise Lean 4 tactics.

**User's Proof Strategy:**
{user_message}

**Current Lean Proof State:**
```lean
{current_proof_code}
```

**Instructions:**
1.  Carefully read the user's entire strategy.
2.  Break it down into a series of small, logical, mathematical steps.
3.  For each mathematical step, generate the single, most appropriate Lean 4 tactic.
4.  Return a JSON object with a single key "steps", which is an array of objects. Each object must have two keys:
    * "reasoning": A very short string (3-5 words) summarizing the user's mathematical step.
    * "tactic": The corresponding Lean 4 tactic as a string.

**Your Turn:** Generate the JSON for the user's strategy now.
"""
        response = call_gemini(strategy_prompt, session["history"], is_json_output=True)
        steps = response.get("steps", []) if isinstance(response, dict) else []
        
        if not steps:
            ai_response_text = "I see you've laid out a strategy, but I'm having trouble breaking it down into concrete Lean steps. Could you please state the very first action you'd like to take?"
        else:
            print(f"[Strategy] Generated steps: {steps}")
            verified_tactics = []
            final_code = current_proof_code
            for step in steps:
                reasoning = step.get("reasoning", "a step")
                tactic = step.get("tactic", "")
                if not tactic: continue

                temp_code = final_code.replace(placeholder, f"  {tactic},\n  {placeholder}")
                is_verified_step, _ = run_lean_verifier(temp_code)
                
                if is_verified_step:
                    final_code = temp_code
                    verified_tactics.append(tactic)
                else:
                    # NEW: Intelligent failure message about the user's reasoning
                    ai_response_text = f"I was following your plan, but I got stuck on the part where you reasoned '{reasoning}'. I tried to translate that, but it didn't seem to be a valid step in Lean. Could you explain your thinking for that specific part of the proof in a bit more detail?"
                    is_verified = False
                    break # Exit the loop
            else: # If loop completes without break
                session["proof_code"] = final_code
                ai_response_text = f"Excellent strategy! I've translated your reasoning into the following successful steps: `{'`, `'.join(verified_tactics)}`. The proof state is updated."
                # Check if the proof is complete
                _, final_verifier_output = run_lean_verifier(final_code)
                if "goals accomplished" in final_verifier_output:
                    ai_response_text += " The proof is complete!"
                else:
                    ai_response_text += " What's next?"
                is_verified = True

    elif intent == "PROOF_STEP":
        # --- Logic for single steps with self-correction ---
        tactic_prompt = f"Translate this user statement into a single Lean 4 tactic: \"{user_message}\""
        generated_tactic = str(call_gemini(tactic_prompt, session["history"])).strip().replace("`", "")
        print(f"[Step] Generated Tactic: {generated_tactic}")
        
        candidate_code = current_proof_code.replace(placeholder, f"  {generated_tactic},\n  {placeholder}")
        is_verified, verifier_output = run_lean_verifier(candidate_code)

        if is_verified:
            session["proof_code"] = candidate_code
            ai_response_text = f"Correct! The step `{generated_tactic}` is valid. What's next?"
        else:
            correction_prompt = f"My tactic `{generated_tactic}` failed with error: '{verifier_output}'. Based on the user's goal '{user_message}', what is the corrected tactic?"
            corrected_tactic = str(call_gemini(correction_prompt, session["history"])).strip().replace("`", "")
            candidate_code_2 = current_proof_code.replace(placeholder, f"  {corrected_tactic},\n  {placeholder}")
            is_verified, _ = run_lean_verifier(candidate_code_2)

            if is_verified:
                session["proof_code"] = candidate_code_2
                ai_response_text = f"That's the right idea! I've adjusted the step to `{corrected_tactic}` and it is correct. What's next?"
            else:
                hint_prompt = f"My attempts `{generated_tactic}` and `{corrected_tactic}` failed. The user's goal is '{user_message}'. Formulate a Socratic hint to guide them."
                ai_response_text = call_gemini(hint_prompt, session["history"])

    else: # QUESTION or META_COMMENT
        prompt_map = {
            "QUESTION": f"A student asked: '{user_message}'. Answer concisely and ask a Socratic question to guide them back to the proof.",
            "META_COMMENT": f"A student sent a conversational message: '{user_message}'. Acknowledge it and gently guide them back to the proof."
        }
        ai_response_text = call_gemini(prompt_map[intent], session["history"])

    session["history"].append({"role": "user", "parts": [{"text": user_message}]})
    session["history"].append({"role": "model", "parts": [{"text": str(ai_response_text)}]})

    return jsonify({
        "ai_response_text": ai_response_text,
        "proof_code": session["proof_code"],
        "is_verified": is_verified,
    })

if __name__ == '__main__':
    app.run(debug=True, port=5000)
