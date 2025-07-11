# app.py
from __future__ import annotations
import os
import uuid
import subprocess
import json
from flask import Flask, request, jsonify
from flask_cors import CORS
from dotenv import load_dotenv
import requests
from typing import Any, Dict, Union, TypeAlias, List, cast
import fitz
import threading
from functools import lru_cache
from .local_llm_stub import generate_response as local_llm
from requests.adapters import HTTPAdapter, Retry
import json

Json: TypeAlias = Dict[str, Any]          # make it an explicit type alias

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

# ---------- util: coerce str|dict to dict --------------------
def _ensure_dict(val: str | Json) -> Json:
    """
    Guarantees a dict output.
    • If val is already a dict → return as-is.
    • If val is a non-empty string → attempt json.loads().
    • Otherwise → return {}.
    """
    if isinstance(val, dict):
        return val
    try:
        return json.loads(val) if val else {}
    except json.JSONDecodeError:
        return {}
    
# ---------- Lean cache warm-up (CORRECTED LOGIC) --------------------------
def _warm_up_lean_cache() -> None:
    """
    Runs `lake update` to ensure all dependencies are fetched and their
    caches are built. This command is the most robust way to prepare the
    project, as it handles its own cache validation and downloads.
    We are relying on this command's success.
    """
    import subprocess
    import time

    project_root = LEAN_PROJECT_PATH
    print("[LeanWarmUp] Ensuring project is fully updated with `lake update`...")
    try:
        start = time.perf_counter()
        # We are ONLY running the command that we have proven works.
        proc = subprocess.run(
            [LAKE_EXECUTABLE, "update"],
            cwd=str(project_root),
            capture_output=True,
            text=True,
            check=True,
            timeout=600,  # 10 minutes, as this can involve downloads
        )
        dur = time.perf_counter() - start
        # Print the output from the command for inspection
        print("--- `lake update` complete. Log output: ---")
        print(proc.stdout)
        print(f"[LeanWarmUp] `lake update` finished in {dur:0.1f}s.")

    except Exception as e:
        print(f"[LeanWarmUp] ⚠️  The `lake update` command itself failed.")
        if isinstance(e, subprocess.CalledProcessError):
            print(f"    STDOUT:\n{e.stdout}")
            print(f"    STDERR:\n{e.stderr}")
        else:
            print(f"    ERROR: {e}")

# ---------- Serialised, cached Lean builds ----------------------------------
class LeanBuildManager:
    """
    • Serialises calls to `lake build` with a global lock (Lake is not
      thread-safe).
    • Caches *identical* proof states via functools.lru_cache so retries
      or duplicate submissions return in ≈10 ms without touching Lake.
    """
    _lock = threading.Lock()

    # Cache by the *exact* Lean source string; size=128 is plenty for a session
    @staticmethod
    @lru_cache(maxsize=128)
    def _cached_build(lean_code: str) -> tuple[bool, str]:
        return _run_lean_verifier(lean_code)

    @classmethod
    def verify(cls, lean_code: str) -> tuple[bool, str]:
        # One build at a time → avoid Lake race conditions
        with cls._lock:
            return cls._cached_build(lean_code)
        
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

# ---------------------------------------------------------------------------
#  call_gemini  —  robust, version-agnostic wrapper  (type-hint-clean)
# ---------------------------------------------------------------------------



GEMINI_API_KEY     = os.getenv("GEMINI_API_KEY", "")
REQUESTS_CA_BUNDLE = os.getenv("REQUESTS_CA_BUNDLE")

_GEMINI_MODELS: List[str]   = [
    "gemini-1.5-flash-latest",
    "gemini-1.5-pro-latest",
    "gemini-pro",
]
_GEMINI_VERSIONS: List[str] = ["v1", "v1beta"]

_RETRY = Retry(
    total=3,
    backoff_factor=0.8,
    status_forcelist=[429, 500, 502, 503, 504],
)

def call_gemini(prompt: str, history: list, *, is_json_output: bool = False) -> str | Json:
    """
    Dynamically discovers and queries available Gemini models, now with conversation history.
    """
    gemini_api_key = os.getenv("GEMINI_API_KEY", "")
    if not gemini_api_key:
        print("[GeminiFallback] No API key → using local stub.")
        return local_llm(prompt, is_json_output)

    sess = requests.Session()
    sess.mount("https://", HTTPAdapter(max_retries=_RETRY))
    headers = {"Content-Type": "application/json"}
    
    # Model discovery logic remains the same...
    discovered_model_names = []
    try:
        discovery_url = f"https://generativelanguage.googleapis.com/v1beta/models?key={gemini_api_key}"
        resp = sess.get(discovery_url, timeout=10)
        if resp.status_code == 200:
            models = resp.json().get("models", [])
            discovered_model_names = [model["name"] for model in models if "generateContent" in model.get("supportedGenerationMethods", [])]
            print(f"[Gemini Discovery] Found usable models: {discovered_model_names}")
        else:
            print(f"[Gemini Discovery] Failed to list models (HTTP {resp.status_code}), falling back to hardcoded list.")
    except requests.exceptions.RequestException as e:
        print(f"[Gemini Discovery] Request to list models failed ({e}), falling back to hardcoded list.")

    if not discovered_model_names:
        discovered_model_names = [f"models/{m}" for m in _GEMINI_MODELS]
        print(f"[Gemini Discovery] Using hardcoded models: {discovered_model_names}")

    # --- THIS IS THE CRITICAL FIX ---
    # Combine the history with the new user message to form the full conversation.
    contents = history + [{"role": "user", "parts": [{"text": prompt}]}]
    
    gen_cfg = {"responseMimeType": "application/json"} if is_json_output else {}
    for model_name in discovered_model_names:
        url = f"https://generativelanguage.googleapis.com/v1beta/{model_name}:generateContent?key={gemini_api_key}"
        
        # The payload now contains the entire conversation history.
        payload = {"contents": contents}
        if gen_cfg:
            payload["generationConfig"] = gen_cfg

        try:
            resp = sess.post(url, headers=headers, json=payload, timeout=20, verify=REQUESTS_CA_BUNDLE or True)
            if 200 <= resp.status_code < 300:
                print(f"[Gemini] Successfully received response from {model_name}")
                response_data = resp.json()
                try:
                    inner_text = response_data['candidates'][0]['content']['parts'][0]['text']
                    if is_json_output:
                        return json.loads(inner_text)
                    return inner_text
                except (KeyError, IndexError, json.JSONDecodeError) as e:
                    print(f"[Gemini] Error parsing successful response from {model_name}: {e}. Response: {response_data}")
            else:
                print(f"[Gemini] {model_name} failed with HTTP {resp.status_code}")
        except requests.exceptions.RequestException as e:
            print(f"[Gemini] Request to {model_name} failed: {e}")

    print("[GeminiFallback] All models failed → using local stub.")
    return local_llm(prompt, is_json_output)

def _run_lean_verifier(lean_code: str) -> tuple[bool, str]:
    """
    Pure function: write code into LeanVerifier.lean and run incremental
    `lake build`.  No locks here; caller (LeanBuildManager) handles that.
    """
    try:
        with open(LEAN_TARGET_FILE_PATH, "w", encoding="utf-8") as f:
            f.write(lean_code)

        proc = subprocess.run(
            [LAKE_EXECUTABLE, "build", "LeanVerifier"],
            cwd=LEAN_PROJECT_PATH,
            capture_output=True,
            text=True,
            timeout=30,
        )

        stderr = proc.stderr.strip()
        if "error" in stderr.lower():
            return False, stderr or "Lean compilation failed"
        return True, "Proof step verified successfully."

    except subprocess.TimeoutExpired:
        return False, "Lean verification timed out (30 s)."
    except Exception as e:
        return False, f"Unexpected Lean verifier error: {e}"

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
    ai_resp = call_gemini(prompt, is_json_output=True)
    
    concepts = []
    try:
        concepts: list[str] = _ensure_dict(ai_resp).get("concepts", [])
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
    
    # --- This is the key change: We no longer create a giant prompt string. ---
    # We pass the history and the new message directly to the LLM call.
    
    # --- STEP 1: Call the LLM with history and the new message ---
    ai_response_json = call_gemini(
        prompt=user_message, 
        history=session["history"], 
        is_json_output=True
    )
    ai_resp_data = _ensure_dict(ai_response_json)
    print(f"[DEBUG] Parsed AI Response Dict: {ai_resp_data}")

    action = ai_resp_data.get("action", "GIVE_HINT")
    response_content = ai_resp_data.get("tactic_or_response_text", "I'm not sure how to proceed. Could you rephrase your last message?")

    ai_response_text = ""
    is_verified = None

    # --- STEP 2: Route based on the LLM's chosen action (this logic is now sound) ---
    if action == "TRANSLATE_TACTIC":
        generated_tactic = response_content.strip().replace("`", "")
        print(f"Generated Tactic: {generated_tactic}")
        
        placeholder = "-- STUDENT TACTICS WILL BE INSERTED HERE"
        candidate_code = session["proof_code"].replace(placeholder, f"  {generated_tactic},\n  {placeholder}")
        
        is_verified, verifier_output = LeanBuildManager.verify(candidate_code)

        if is_verified:
            session["proof_code"] = candidate_code
            ai_response_text = f"Excellent! The step `{generated_tactic}` is correct. The proof state has been updated. What's next?"
        else:
            hint_generation_prompt = f"""
As a Socratic AI tutor, a student's proof step failed.
- Their goal was: '{user_message}'
- We tried the tactic: `{generated_tactic}`
- The Lean verifier gave this error: '{verifier_output}'
Do not show the raw error. Formulate a gentle Socratic question or hint to guide them toward a valid step."""
            # Use a simple call for the hint, no history needed.
            ai_response_text = cast(str, call_gemini(hint_generation_prompt, history=[]))

    elif action == "ANSWER_QUESTION" or action == "GIVE_HINT":
        ai_response_text = response_content
        is_verified = None

    else:
        ai_response_text = "I'm not sure how to proceed. Let's get back to the proof. What should our next step be?"
        is_verified = None

    # --- STEP 3: Add the user message and the final AI response to the history ---
    session["history"].append({"role": "user", "parts": [{"text": user_message}]})
    session["history"].append({"role": "model", "parts": [{"text": ai_response_text}]})

    return jsonify({
        "ai_response_text": ai_response_text,
        "proof_code": session["proof_code"],
        "is_verified": is_verified,
    })

def main() -> None:
    """Main function to run the setup and start the Flask app."""
    print("--- Preparing to Start Altera Labs Backend ---")
    
    # Run the warm-up synchronously. This will complete entirely
    # before the Flask server and its reloader are even initialized.
    _warm_up_lean_cache()
    
    print("--- Warm-up complete. Starting Flask server. ---")
    # Now, start the Flask app. If it restarts, it will NOT re-run the warm-up.
    app.run(debug=True, port=5000)

if __name__ == '__main__':
    main()