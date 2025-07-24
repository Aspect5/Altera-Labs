# backend/prompts.py

"""
This file contains all the prompt templates used for interacting with the LLM.
"""

# STEP 1: A prompt to only extract concepts from a syllabus.
SYLLABUS_CONCEPTS_PROMPT = """
Analyze the following syllabus text. Your task is to identify and extract only the core academic and technical concepts.

- You MUST ignore all administrative, logistical, or grading-related terms (e.g., "homework", "exam", "office hours", "Gradescope", "Canvas", "textbook").
- Return a single JSON object with a key "concepts", which is a list of objects.
- Each concept object must have an "id" (a snake_case string) and a "label" (the concept name).

Syllabus Text:
---
{syllabus_text}
---
"""

# STEP 2: A prompt to generate relationships (edges) for a given list of concepts.
SYLLABUS_EDGES_PROMPT = """
Analyze the following list of academic concepts extracted from a syllabus.
Your task is to determine the prerequisite relationships between them.

- Return a single JSON object with a key "edges".
- The "edges" key should be a list of objects, each representing a prerequisite link.
- Each edge object must have an "id" (e.g., "source->target"), "source" (the ID of the prerequisite concept), "target" (the ID of the concept that depends on it), and a "label" of "is_prerequisite_for".
- Only create edges for strong, direct prerequisite relationships. If there are no relationships, return an empty list.

List of Concepts:
---
{concepts_json_string}
---
"""

# Prompt used in app.py for concept explanations
CONCEPT_EXPLANATION_PROMPT = """
Explain the following mathematical concept in a clear and concise way.
The user selected this text while viewing the provided context.
Use markdown for formatting and LaTeX for mathematical notation.

Concept: "{concept}"

Context:
---
{context}
---
"""

# Prompts used in metacognition.py for the tutoring flow
PLANNING_PROMPT_INITIAL = "Hello! We're about to start a proof. First, let's make sure we understand the goal. In your own words, what are we trying to prove?"

PLANNING_PROMPT_STRATEGY = "Great. Now, what's our overall strategy? What key definitions or theorems do you think will be important here?"

MONITORING_PROMPT_START = "Excellent plan. Let's begin the proof. What is your first logical step?"

REFLECTION_PROMPT_SUCCESS = "Fantastic work! The proof is complete. Let's reflect. What was the most challenging part of this proof for you?"

REFLECTION_PROMPT_CLOSING = "Thank you for the feedback. This session is now complete."

# Prompt for providing dynamic help when a user is stuck or frustrated
DYNAMIC_HELPER_PROMPT = """
A student is working on a proof and seems to be stuck or frustrated.
Their current proof state and their latest message are below.
Provide a Socratic, encouraging hint to help them get unstuck. Do not give the answer directly.
Ask a question that guides them to the next logical step.

Proof State:
```lean
{proof_code}
User Message: "{user_message}"
```
"""