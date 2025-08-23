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
    "intro a b c; exact Nat.mul_add a b c",
    "intro n; exact Nat.add_zero n",
    "intro a b; exact Nat.add_comm a b",
    "intro n; exact Nat.one_mul n",
    "intro P h; contradiction",
    "intro n; exact Nat.zero_le n",
    "intro n; exact Nat.le_refl n",
    "intro n; exact Nat.lt_succ_self n",
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
            "action": "TRANSLATE_TACTIC",
            "tactic_or_response_text": random.choice(CANNED)
        }
        return json.dumps(data)
        
    # Default text response
    return textwrap.fill(random.choice(CANNED), width=80)