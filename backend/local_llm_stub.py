"""
local_llm_stub.py
A zero-dependency fallback when Gemini is unavailable.
Returns short, helpful messages or dummy JSON structures.
"""
from __future__ import annotations
import random, textwrap
from typing import Any, Dict

CANNED = [
    "Let's unpack that step. Which lemma could apply next?",
    "Remember: identity means x * e = x for all x. How does that help?",
    "Interesting thought! Can you restate the goal in your own words?",
]

def generate_response(prompt: str, is_json_output: bool = False) -> str | Dict[str, Any]:
    if "Extract key concepts" in prompt:
        return {"concepts": ["group", "identity element", "homomorphism"]}

    # CORRECTED: Return the new, expected JSON structure for the main prompt.
    if is_json_output:
        # Check if the prompt is asking for a tactic translation
        if "e f = e and f e = f" in prompt:
            return {
                "action": "TRANSLATE_TACTIC",
                "tactic_or_response_text": "have h₁ := (he f).left;\n  have h₂ := (hf e).right"
            }
        # Default JSON response
        return {
            "action": "GIVE_HINT",
            "tactic_or_response_text": "Let's focus on the proof. What is the very first logical deduction we can make?"
        }
        
    return textwrap.fill(random.choice(CANNED), width=80)