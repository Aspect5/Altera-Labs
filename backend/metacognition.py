# backend/metacognition.py

"""
This module implements the "Metacognitive Scaffolding" logic for the Altera Labs
AI Cognitive Partner. It has been refactored to act as the central
"Pedagogical Policy Engine."

Its primary responsibility is to orchestrate the AI's response by:
1.  Calling the `state_analyzer` to get a rich understanding of the student's
    current cognitive and affective state.
2.  Using that state to make a dynamic, pedagogically-sound decision about
    how to interact with the user, moving beyond a rigid state machine.
"""

import logging
from enum import Enum, auto
from typing import Dict, Any

# --- Local Application Imports ---
import prompts
import socratic_auditor
import state_analyzer

class MetacognitiveStage(Enum):
    """Defines the high-level stages of the pedagogical loop."""
    PLANNING_GOAL = auto()
    PLANNING_STRATEGY = auto()
    MONITORING = auto()
    REFLECTION = auto()

def initialize_session_stage(session: Dict[str, Any]) -> None:
    """
    Sets the initial stage for a new session. The full session object
    is now created in app.py to act as the Student Model placeholder.
    """
    session['metacognitive_stage'] = MetacognitiveStage.PLANNING_GOAL.name
    logging.info(f"Session {session.get('session_id')} initialized. Stage: {session['metacognitive_stage']}.")

def process_message(session: Dict[str, Any], user_message: str) -> Dict[str, Any]:
    """
    Acts as the Pedagogical Policy Engine.
    """
    session_id = session.get("session_id", "unknown")
    state_analyzer.analyze_user_interaction(session, user_message)
    
    current_stage = session['metacognitive_stage']
    
    # --- Initialize conversation history if not exists ---
    if 'conversation_history' not in session:
        session['conversation_history'] = []
    
    # --- Add current message to conversation history ---
    session['conversation_history'].append({
        'role': 'user',
        'content': user_message,
        'timestamp': session.get('current_time', 'unknown')
    })
    
    # --- Keep only last 10 messages for context (to avoid token limits) ---
    if len(session['conversation_history']) > 10:
        session['conversation_history'] = session['conversation_history'][-10:]
    
    # --- DYNAMIC RESPONSE FOR AFFECTIVE STATES ---
    affective_state = session['student_model']['affective_state']
    if affective_state in ['FRUSTRATED', 'CONFUSED']:
        prompt = prompts.DYNAMIC_HELPER_PROMPT.format(
            proof_code=session['student_model']['current_proof_state'],
            user_message=f"The user seems {affective_state.lower()} and said: '{user_message}'"
        )
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        # Add AI response to conversation history
        session['conversation_history'].append({
            'role': 'assistant',
            'content': ai_response,
            'timestamp': session.get('current_time', 'unknown')
        })
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof_state'],
            "is_verified": None
        }

    # --- Check if user is explicitly asking for proof verification ---
    proof_keywords = [
        'prove', 'proof step', 'lean', 'verify', 'tactic', 'rw', 'simp', 'exact',
        'apply', 'intro', 'cases', 'induction', 'rewrite', 'use', 'exists',
        'rw [', 'simp [', 'exact ', 'apply ', 'intro ', 'cases ', 'induction ',
        'rewrite ', 'use ', 'exists ', 'by ', ':= by'
    ]
    user_wants_verification = any(keyword in user_message.lower() for keyword in proof_keywords)
    
    # Additional check for Lean-specific syntax
    lean_syntax_patterns = [
        r'\brw\s*\[', r'\bsimp\s*\[', r'\bexact\s+', r'\bapply\s+', r'\bintro\s+',
        r'\bcases\s+', r'\binduction\s+', r'\brewrite\s+', r'\buse\s+', r'\bexists\s+',
        r'\bby\s+', r':=\s*by'
    ]
    
    import re
    for pattern in lean_syntax_patterns:
        if re.search(pattern, user_message, re.IGNORECASE):
            user_wants_verification = True
            break
    
    # Only proceed to verification if user explicitly requests it
    if user_wants_verification and current_stage == MetacognitiveStage.MONITORING.name:
        result = handle_monitoring_stage(session, user_message)
        
        # Add AI response to conversation history
        session['conversation_history'].append({
            'role': 'assistant',
            'content': result['ai_response_text'],
            'timestamp': session.get('current_time', 'unknown')
        })
        
        return result

    # --- Build conversation context for better memory ---
    conversation_context = ""
    if len(session['conversation_history']) > 1:
        recent_messages = session['conversation_history'][-6:]  # Last 6 messages for context
        conversation_context = "\n\nRecent conversation context:\n"
        for msg in recent_messages:
            role = "Student" if msg['role'] == 'user' else "Tutor"
            conversation_context += f"{role}: {msg['content']}\n"

    # --- DYNAMIC STAGE-BASED RESPONSES ---
    if current_stage == MetacognitiveStage.PLANNING_GOAL.name:
        session['metacognitive_stage'] = MetacognitiveStage.PLANNING_STRATEGY.name
        # Generate dynamic response based on user's understanding of the goal
        prompt = f"""
You are a helpful math tutor. The student is working on understanding a proof goal.
They just said: "{user_message}"

{conversation_context}

Based on their response and our conversation so far, provide a thoughtful, encouraging response that:
1. Acknowledges their understanding and builds on our previous discussion
2. Gently corrects any misconceptions if needed
3. Guides them to think about the overall strategy for the proof
4. Asks a follow-up question about their approach

Keep your response conversational and supportive. Do NOT mention proof verification or Lean tactics yet.
Make sure to reference and build upon what we've discussed previously.
"""
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        # Add AI response to conversation history
        session['conversation_history'].append({
            'role': 'assistant',
            'content': ai_response,
            'timestamp': session.get('current_time', 'unknown')
        })
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof_state'],
            "is_verified": None
        }

    elif current_stage == MetacognitiveStage.PLANNING_STRATEGY.name:
        session['metacognitive_stage'] = MetacognitiveStage.MONITORING.name
        # Generate dynamic response based on their strategy
        prompt = f"""
You are a helpful math tutor. The student is planning their proof strategy.
They just said: "{user_message}"

{conversation_context}

Based on their strategy and our conversation so far, provide a thoughtful response that:
1. Evaluates their approach positively and references our previous discussion
2. Suggests any missing key concepts or theorems they might need
3. Encourages them to start the first step of their proof
4. Asks what their first logical step will be

Keep your response encouraging and constructive. Do NOT mention proof verification or Lean tactics yet.
Make sure to reference and build upon what we've discussed previously.
"""
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        # Add AI response to conversation history
        session['conversation_history'].append({
            'role': 'assistant',
            'content': ai_response,
            'timestamp': session.get('current_time', 'unknown')
        })
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof_state'],
            "is_verified": None
        }

    elif current_stage == MetacognitiveStage.MONITORING.name:
        # If user doesn't explicitly want verification, continue with tutoring
        if not user_wants_verification:
            prompt = f"""
You are a helpful math tutor in the monitoring stage. The student said: "{user_message}"

{conversation_context}

Provide a helpful response that:
1. Acknowledges their input and references our previous discussion
2. Guides them toward understanding the proof concept
3. Encourages them to think about the next logical step
4. Only mention proof verification if they explicitly ask for it

Keep your response conversational and educational.
Make sure to reference and build upon what we've discussed previously.
"""
            ai_response = socratic_auditor.get_llm_response(prompt)
            
            # Add AI response to conversation history
            session['conversation_history'].append({
                'role': 'assistant',
                'content': ai_response,
                'timestamp': session.get('current_time', 'unknown')
            })
            
            return {
                "ai_response_text": ai_response,
                "proof_code": session['student_model']['current_proof_state'],
                "is_verified": None
            }
        else:
            # User explicitly wants verification
            result = handle_monitoring_stage(session, user_message)
            
            # Add AI response to conversation history
            session['conversation_history'].append({
                'role': 'assistant',
                'content': result['ai_response_text'],
                'timestamp': session.get('current_time', 'unknown')
            })
            
            return result
    
    elif current_stage == MetacognitiveStage.REFLECTION.name:
        # Generate dynamic reflection response
        prompt = f"""
You are a helpful math tutor. The student has completed a proof and is reflecting.
They just said: "{user_message}"

{conversation_context}

Provide a thoughtful response that:
1. Acknowledges their reflection and references our journey together
2. Offers insights about their learning process
3. Encourages them to think about what they learned
4. Thanks them for their work

Keep your response warm and encouraging.
Make sure to reference and build upon what we've discussed previously.
"""
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        # Add AI response to conversation history
        session['conversation_history'].append({
            'role': 'assistant',
            'content': ai_response,
            'timestamp': session.get('current_time', 'unknown')
        })
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof_state'],
            "is_verified": None
        }
    
    # Default fallback for any unexpected stage
    prompt = f"""
You are a helpful math tutor. The student said: "{user_message}"

{conversation_context}

Provide a helpful, encouraging response that guides them in their mathematical thinking.
Make sure to reference and build upon what we've discussed previously.
"""
    ai_response = socratic_auditor.get_llm_response(prompt)
    
    # Add AI response to conversation history
    session['conversation_history'].append({
        'role': 'assistant',
        'content': ai_response,
        'timestamp': session.get('current_time', 'unknown')
    })
    
    return {
        "ai_response_text": ai_response,
        "proof_code": session['student_model']['current_proof_state'],
        "is_verified": None
    }

def handle_monitoring_stage(session: Dict[str, Any], user_message: str) -> Dict[str, Any]:
    """
    Manages the logic for the core problem-solving loop (Monitoring stage).
    """
    session_id = session.get("session_id", "unknown")
    
    result = socratic_auditor.verify_step(
        proof_state=session['student_model']['current_proof_state'],
        user_message=user_message,
        mode='homework'
    )

    # --- DYNAMIC RESPONSE FOR TACTIC FAILURE ---
    if result.get('is_verified') is None and 'sorry' in result.get('new_proof_code', ''):
        logging.warning(f"Tactic generation failed for session {session_id}. Generating dynamic response.")
        
        # Instead of a static prompt, we now call the LLM to generate a response.
        prompt = prompts.DYNAMIC_HELPER_PROMPT.format(
            proof_code=session['student_model']['current_proof_state'],
            user_message=user_message
        )
        ai_response = socratic_auditor.get_llm_response(prompt)
        
        return {
            "ai_response_text": ai_response,
            "proof_code": session['student_model']['current_proof_state'],
            "is_verified": None
        }

    # --- Success Path ---
    session['student_model']['current_proof_state'] = result['new_proof_code']
    if 'sorry' not in session['student_model']['current_proof_state']:
        logging.info(f"Proof completed for session {session_id}. Transitioning to REFLECTION.")
        session['metacognitive_stage'] = MetacognitiveStage.REFLECTION.name
        
        # Generate dynamic success response
        prompt = f"""
You are a helpful math tutor. The student has successfully completed a proof step.
Their step was: "{user_message}"

Provide an encouraging response that:
1. Congratulates them on their success
2. Explains why their step was correct
3. Asks them to reflect on what made this step work
4. Guides them to think about the next step or completion

Keep your response enthusiastic and educational.
"""
        ai_response = socratic_auditor.get_llm_response(prompt)
        result['ai_response_text'] = ai_response
    
    return result