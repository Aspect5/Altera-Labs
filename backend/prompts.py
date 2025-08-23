# backend/prompts.py

"""
This file contains all the prompt templates used for interacting with the LLM.
"""

# A single, unified prompt to generate a complete knowledge graph from a syllabus.
SYLLABUS_GRAPH_PROMPT = """
You are an expert in educational theory and computer science. Your task is to analyze the provided course syllabus and construct an educational knowledge graph.

1.  **Extract Key Concepts:** Identify the main technical topics or concepts from the syllabus. These will be the **nodes** of your graph. Create a unique, simple `id` (snake_case) and a clean, human-readable `label` for each concept. You MUST ignore administrative terms like "homework," "exam," "office hours," etc.

2.  **Determine Prerequisites:** Analyze the text to find prerequisite relationships. Words like "builds upon," "requires," or sequential ordering (e.g., Week 2 topics are prerequisites for Week 3) indicate a relationship. These will be the **edges** of your graph.

3.  **Assign Weights:** For each prerequisite relationship (edge), assign a numerical **weight** from 0.0 to 1.0.
    * A weight of **0.9-1.0** means it's a **hard prerequisite** (e.g., you cannot understand 'Derivatives' without 'Limits').
    * A weight of **0.4-0.7** means it's a **strong suggestion**.
    * A weight of **0.1-0.3** means it's a **weakly related** concept.

- You MUST return a single JSON object containing two keys: "nodes" and "edges".
- If no concepts or edges are found, return empty lists.

Syllabus Text:
---
{syllabus_text}
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