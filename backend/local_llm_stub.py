# backend/local_llm_stub.py

"""
local_llm_stub.py
A zero-dependency fallback when Gemini is unavailable.
Returns short, helpful messages or dummy JSON structures.
"""
from __future__ import annotations
import random
import textwrap
import json  # Import the json library
from typing import Any, Dict

CANNED = [
    "Let's unpack that step. Which lemma could apply next?",
    "Remember: identity means x * e = x for all x. How does that help?",
    "Interesting thought! Can you restate the goal in your own words?",
]

def generate_response(prompt: str, is_json_output: bool = False) -> str:
    """
    Generates a response, ensuring JSON output is a string, just like the real API.
    """
    # For syllabus extraction, return a JSON string
    if "Extract key concepts" in prompt:
        data = {"concepts": [{"id": "group", "label": "group"}, {"id": "identity", "label": "identity element"}, {"id": "homomorphism", "label": "homomorphism"}]}
        return json.dumps(data)

    # For any other JSON request, return a JSON string
    if is_json_output:
        # Check if the prompt is asking for a tactic translation
        if "e f = e and f e = f" in prompt:
            data = {
                "action": "TRANSLATE_TACTIC",
                "tactic_or_response_text": "have h₁ := (he f).left;\\n  have h₂ := (hf e).right"
            }
            return json.dumps(data)
        
        # Default JSON response
        data = {
            "action": "GIVE_HINT",
            "tactic_or_response_text": "Let's focus on the proof. What is the very first logical deduction we can make?"
        }
        return json.dumps(data)
        
    # Default text response
    return textwrap.fill(random.choice(CANNED), width=80)