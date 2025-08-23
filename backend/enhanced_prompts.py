# backend/enhanced_prompts.py

"""
Enhanced Prompt Engineering System for AI Prover

This module provides sophisticated prompt generation capabilities that incorporate
knowledge base information, error learning, and multi-strategy approaches.
"""

import logging
from typing import Dict, List, Any, Optional
from lean_knowledge_base import lean_kb
import re

logger = logging.getLogger(__name__)

class EnhancedPromptEngine:
    """
    Advanced prompt engineering system for generating context-aware prompts
    that incorporate available knowledge and learn from errors.
    """
    
    def __init__(self):
        self.error_patterns = self._build_error_patterns()
        self.strategy_templates = self._build_strategy_templates()
        self.lean_syntax_guide = self._build_lean_syntax_guide()
        
    def _build_lean_syntax_guide(self) -> str:
        """Build a comprehensive guide for proper Lean syntax."""
        return """
CRITICAL LEAN SYNTAX RULES:
1. NEVER include import statements in your tactic - imports are handled separately
2. NEVER include 'open' statements in your tactic
3. NEVER include theorem declarations in your tactic
4. Use `intro` to introduce variables: `intro n`
5. Use `exact` with theorem names: `exact Nat.add_zero`
6. Use `simp` with lemma lists: `simp [Nat.add_zero, Nat.mul_add]`
7. Use `rw` for rewriting: `rw [Nat.add_zero]`
8. Use `rfl` for reflexivity: `rfl`
9. Use `constructor` for bidirectional proofs: `constructor`
10. Use `cases` for case analysis: `cases Classical.em P with`
11. NEVER include markdown formatting in Lean code
12. NEVER include explanatory text within Lean code blocks
13. ALWAYS use proper Lean syntax without extra characters
14. ONLY generate the tactic itself, not the surrounding code structure
15. KEEP RESPONSES CONCISE - generate only the tactic, no explanations
16. AVOID VERBOSE EXPLANATIONS - focus on the solution, not the reasoning
17. USE SIMPLE TACTICS FIRST - prefer `rfl`, `intro`, `exact` over complex approaches

COMPOSITIONAL REASONING STRATEGIES (Based on Ineq-Comp Research):
1. DECOMPOSITION: Break complex goals into simpler sub-goals
2. VARIABLE DUPLICATION: When you see repeated patterns, consider variable substitution
3. ALGEBRAIC REWRITING: Use systematic transformations to simplify expressions
4. MULTI-STEP COMPOSITION: Chain simple proofs together for complex results
5. HUMAN-INTUITIVE APPROACHES: Think like a human mathematician, not just syntax

COMMON LEAN TACTICS:
- `intro n` - introduces variable n
- `exact theorem_name` - applies exact theorem
- `simp [lemma1, lemma2]` - simplifies using lemmas
- `rw [lemma]` - rewrites using lemma
- `rfl` - proves reflexivity
- `constructor` - breaks bidirectional proof
- `cases` - performs case analysis
- `induction` - performs induction
- `ring` - proves ring identities
- `norm_num` - proves numeric equalities

EXAMPLES OF CORRECT TACTICS:
- `intro n; exact Nat.add_zero n`
- `intro a b; exact Nat.add_comm a b`
- `intro a b c; exact Nat.mul_add a b c`
- `intro n; rfl`
- `intro P; constructor; intro h; by_contra h1; contradiction`

EXAMPLES OF INCORRECT TACTICS:
- `import Mathlib.Data.Nat.Basic` (don't include imports)
- `theorem test : ...` (don't include theorem declarations)
- `open Classical` (don't include open statements)
- `Here's the tactic: intro n` (don't include explanatory text)

COMPOSITIONAL REASONING EXAMPLES:
- For inequalities: Use transitivity and monotonicity properties
- For equalities: Use symmetry, transitivity, and substitution
- For logical statements: Use contrapositive, contradiction, or direct proof
- For arithmetic: Use associativity, commutativity, and distributivity
"""
        
    def _build_error_patterns(self) -> Dict[str, Dict[str, Any]]:
        """Build patterns for recognizing and handling common Lean errors."""
        return {
            "syntax_error": {
                "pattern": r"unexpected token|syntax error|invalid",
                "solutions": [
                    "Check Lean syntax - ensure proper theorem declaration",
                    "Remove any markdown formatting from Lean code",
                    "Use proper Lean imports and structure",
                    "Ensure tactics are properly formatted"
                ],
                "suggestions": [
                    "Start with: theorem theorem_name : statement := by",
                    "Use proper Lean syntax without extra characters",
                    "Check that all tactics are valid Lean tactics"
                ]
            },
            "unknown_constant": {
                "pattern": r"unknown (?:constant|identifier) '([^']+)'",
                "solutions": [
                    "Try alternative theorem name from the knowledge base",
                    "Use simp with available lemmas instead of exact theorem",
                    "Break the proof into smaller steps",
                    "Use constructor and handle each case separately"
                ],
                "suggestions": [
                    "Check if the theorem exists in Mathlib.Data.Nat.Basic",
                    "Try using simp with available lemmas",
                    "Consider using rw instead of exact"
                ]
            },
            "type_mismatch": {
                "pattern": r"Application type mismatch|unsolved goals",
                "solutions": [
                    "Add proper introductions before applying theorems",
                    "Check variable types and ensure they match",
                    "Use constructor to handle bidirectional proofs",
                    "Break into subgoals and handle each separately"
                ],
                "suggestions": [
                    "Make sure all variables are properly introduced",
                    "Check that theorem arguments match the goal",
                    "Use intro to introduce variables first"
                ]
            },
            "tactic_failed": {
                "pattern": r"tactic '[^']+' failed",
                "solutions": [
                    "Try a simpler tactic first",
                    "Break the goal into subgoals",
                    "Use a different approach entirely",
                    "Apply induction if applicable"
                ],
                "suggestions": [
                    "Start with basic tactics like intro and exact",
                    "Consider using simp with available lemmas",
                    "Try constructor for bidirectional proofs"
                ]
            },
            "definitional_equality": {
                "pattern": r"not definitionally equal",
                "solutions": [
                    "Use simp to simplify expressions",
                    "Apply rewrite rules to transform the goal",
                    "Use rw to rewrite using available lemmas",
                    "Break into smaller steps"
                ],
                "suggestions": [
                    "Use simp with available lemmas",
                    "Try rw with relevant theorems",
                    "Consider using ring or norm_num for arithmetic"
                ]
            }
        }
    
    def _build_strategy_templates(self) -> Dict[str, List[str]]:
        """Build templates for different proof strategies."""
        return {
            "easy": [
                "Use reflexivity (rfl) for definitional equalities",
                "Apply exact theorem if available",
                "Use simp with basic lemmas"
            ],
            "medium": [
                "Use exact theorem with proper introductions",
                "Apply simp with relevant lemmas",
                "Use constructor for bidirectional proofs",
                "Break into subgoals if needed"
            ],
            "hard": [
                "Use induction for recursive properties",
                "Apply case analysis for complex logic",
                "Use specialized tactics like ring or norm_num",
                "Break into multiple subgoals"
            ]
        }

    def create_context_aware_prompt(self, goal: str, available_theorems: List[str] = None, 
                                  error_history: List[str] = None, difficulty: str = "medium") -> str:
        """
        Create a context-aware prompt that incorporates available knowledge and error history.
        """
        if available_theorems is None:
            available_theorems = lean_kb.get_available_theorems()
        
        if error_history is None:
            error_history = []
        
        # Get relevant theorems for this goal
        relevant_theorems = lean_kb.suggest_theorem(goal)
        
        # Build the prompt
        prompt = f"""
You are an expert Lean 4 theorem prover. Your task is to generate a correct Lean 4 tactic to prove the given goal.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

AVAILABLE THEOREMS:
{self._format_available_theorems(available_theorems)}

RELEVANT THEOREMS FOR THIS GOAL:
{relevant_theorems}

DIFFICULTY LEVEL: {difficulty.upper()}

RECOMMENDED STRATEGIES:
{chr(10).join(self.strategy_templates.get(difficulty, self.strategy_templates["medium"]))}

ERROR HISTORY:
{self._format_error_history(error_history)}

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Use proper Lean syntax as specified above
3. Start with the most appropriate strategy for the difficulty level
4. If the goal involves universal quantifiers, use 'intro' to introduce variables
5. Use 'exact' with theorem names when applicable
6. Use 'simp' with relevant lemmas for simplification
7. Use 'rfl' for reflexivity proofs
8. Ensure the tactic is complete and will solve the goal

Generate the Lean 4 tactic:
"""
        return prompt

    def create_error_learning_prompt(self, goal: str, error_output: str, 
                                   attempt_count: int, previous_attempts: List[str] = None) -> str:
        """
        Create a prompt that learns from previous errors and attempts.
        """
        if previous_attempts is None:
            previous_attempts = []
        
        # Analyze the error
        error_analysis = self._analyze_error(error_output)
        
        # Get available theorems
        available_theorems = lean_kb.get_available_theorems()
        
        prompt = f"""
You are an expert Lean 4 theorem prover. Previous attempts have failed. Learn from the errors and generate a corrected tactic.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

ATTEMPT NUMBER: {attempt_count}

PREVIOUS ATTEMPTS:
{chr(10).join(f"Attempt {i+1}: {attempt}" for i, attempt in enumerate(previous_attempts))}

ERROR ANALYSIS:
Type: {error_analysis.get('type', 'unknown')}
Message: {error_analysis.get('message', error_output)}
Suggestions: {chr(10).join(error_analysis.get('suggestions', []))}

AVAILABLE THEOREMS:
{self._format_available_theorems(available_theorems)}

LEARNING FROM ERRORS:
1. If there were syntax errors, ensure proper Lean syntax
2. If theorems were not found, use available theorems or simp with lemmas
3. If type mismatches occurred, ensure proper variable introduction
4. If tactics failed, try simpler approaches first
5. Always use the exact syntax shown in the Lean syntax guide

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Address the specific error from the previous attempt
3. Use a different approach if the previous one failed
4. Ensure proper Lean syntax and structure
5. Use available theorems and lemmas

Generate the corrected Lean 4 tactic:
"""
        return prompt

    def create_multi_strategy_prompt(self, goal: str, difficulty: str = "medium") -> str:
        """
        Create a prompt that suggests multiple strategies for proving the goal.
        """
        available_theorems = lean_kb.get_available_theorems()
        relevant_theorems = lean_kb.suggest_theorem(goal)
        
        prompt = f"""
You are an expert Lean 4 theorem prover. Generate a tactic using the most appropriate strategy for this goal.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

DIFFICULTY: {difficulty.upper()}

AVAILABLE THEOREMS:
{self._format_available_theorems(available_theorems)}

RELEVANT THEOREMS:
{relevant_theorems}

STRATEGY OPTIONS:
1. DIRECT APPROACH: Use exact theorem if available
2. SIMPLIFICATION: Use simp with relevant lemmas
3. STEP-BY-STEP: Break into smaller steps with intro, rw, rfl
4. SPECIALIZED: Use ring, norm_num, or other specialized tactics
5. CONSTRUCTOR: Use constructor for bidirectional proofs

RECOMMENDED STRATEGY FOR {difficulty.upper()} DIFFICULTY:
{chr(10).join(self.strategy_templates.get(difficulty, self.strategy_templates["medium"]))}

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Choose the most appropriate strategy for the goal type
3. Use proper Lean syntax as specified above
4. Ensure the tactic is complete and will solve the goal

Generate the Lean 4 tactic:
"""
        return prompt

    def create_fallback_prompt(self, goal: str, failed_attempts: List[str]) -> str:
        """
        Create a fallback prompt when multiple attempts have failed.
        """
        available_theorems = lean_kb.get_available_theorems()
        
        prompt = f"""
You are an expert Lean 4 theorem prover. Multiple attempts have failed. Use the most basic, reliable approach.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

FAILED ATTEMPTS:
{chr(10).join(f"Attempt {i+1}: {attempt}" for i, attempt in enumerate(failed_attempts))}

AVAILABLE THEOREMS:
{self._format_available_theorems(available_theorems)}

FALLBACK STRATEGY:
1. Use the simplest possible approach
2. Start with basic tactics: intro, exact, simp, rfl
3. Use only the most fundamental theorems
4. Avoid complex tactic combinations
5. Focus on step-by-step proof construction

BASIC TACTIC SEQUENCE:
1. Use 'intro' to introduce variables if needed
2. Use 'exact' with a simple theorem if applicable
3. Use 'simp' with basic lemmas if needed
4. Use 'rfl' for reflexivity if applicable

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Use the simplest possible approach
3. Focus on basic, reliable tactics
4. Ensure proper Lean syntax

Generate the basic Lean 4 tactic:
"""
        return prompt

    def create_axiom_driven_prompt(self, goal: str, available_axioms: List[str] = None) -> str:
        """
        Create prompts that encourage diverse proof strategies using available axioms.
        Based on the DREAM approach for axiom-driven strategy diversification.
        """
        if available_axioms is None:
            available_axioms = lean_kb.get_available_theorems()
        
        prompt = f"""
You are an expert Lean 4 theorem prover. Generate multiple diverse proof strategies using available axioms.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

AVAILABLE AXIOMS:
{self._format_available_theorems(available_axioms)}

AXIOM-DRIVEN STRATEGY DIVERSIFICATION (Based on DREAM Research):
1. DIRECT AXIOM APPLICATION: Try applying axioms directly to the goal
2. CONTRAPOSITIVE APPROACH: Consider proving the contrapositive if direct proof fails
3. PROOF BY CONTRADICTION: Assume the negation and derive a contradiction
4. INDUCTION STRATEGY: Use mathematical induction if the goal involves natural numbers
5. DECOMPOSITION: Break the goal into simpler sub-goals and solve each separately
6. ALGEBRAIC MANIPULATION: Use systematic transformations to simplify expressions

COMPOSITIONAL REASONING APPROACH:
- Identify the core mathematical structure of the goal
- Look for patterns that can be decomposed into simpler parts
- Use human-intuitive reasoning rather than brute force
- Consider multiple proof strategies before choosing the best one

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Choose the most appropriate strategy from the diversification options
3. Use available axioms effectively
4. Focus on human-intuitive reasoning patterns
5. Ensure proper Lean syntax

Generate the Lean 4 tactic:
"""
        return prompt

    def create_sub_proposition_feedback_prompt(self, goal: str, failed_attempt: str, sub_goals: List[str] = None) -> str:
        """
        Create prompts that help LLMs reflect on and correct sub-proposition errors.
        Based on the DREAM approach for sub-proposition error feedback.
        """
        if sub_goals is None:
            sub_goals = self._extract_sub_goals(goal)
        
        prompt = f"""
You are an expert Lean 4 theorem prover. Previous attempt failed. Analyze the sub-propositions and identify where the reasoning went wrong.

{self.lean_syntax_guide}

GOAL TO PROVE:
{goal}

FAILED ATTEMPT:
{failed_attempt}

IDENTIFIED SUB-GOALS:
{chr(10).join(f"- {sub_goal}" for sub_goal in sub_goals)}

SUB-PROPOSITION ERROR ANALYSIS (Based on DREAM Research):
1. WHICH SUB-PROPOSITION FAILED? Identify the specific part that caused the failure
2. WHAT WAS THE REASONING ERROR? Analyze the logical flaw in the approach
3. HOW CAN THIS BE CORRECTED? Suggest specific fixes for the identified error
4. WHAT ALTERNATIVE APPROACH SHOULD BE TRIED? Propose a different proof strategy

ERROR CORRECTION STRATEGIES:
- If a sub-goal is too complex, break it down further
- If an axiom application failed, try a different axiom or approach
- If the reasoning was circular, find a more direct path
- If the proof was too long, look for shortcuts or simplifications

INSTRUCTIONS:
1. Generate ONLY the Lean 4 tactic code - no explanations, no markdown
2. Address the specific error identified in the analysis
3. Use a different approach than the failed attempt
4. Focus on correcting the sub-proposition that failed
5. Ensure proper Lean syntax

Generate the corrected Lean 4 tactic:
"""
        return prompt

    def _format_available_theorems(self, theorems: List[str]) -> str:
        """Format the list of available theorems for the prompt."""
        if not theorems:
            return "No specific theorems provided. Use basic Lean tactics."
        
        formatted = []
        for theorem in theorems[:10]:  # Limit to first 10 to avoid overwhelming
            formatted.append(f"- {theorem}")
        
        if len(theorems) > 10:
            formatted.append(f"... and {len(theorems) - 10} more theorems")
        
        return chr(10).join(formatted)

    def _format_error_history(self, error_history: List[str]) -> str:
        """Format the error history for the prompt."""
        if not error_history:
            return "No previous errors."
        
        formatted = []
        for i, error in enumerate(error_history[-3:]):  # Show last 3 errors
            formatted.append(f"Error {i+1}: {error[:100]}...")
        
        return chr(10).join(formatted)

    def _analyze_error(self, error_output: str) -> Dict[str, Any]:
        """Analyze error output to determine type and suggestions."""
        for error_type, pattern_info in self.error_patterns.items():
            if re.search(pattern_info["pattern"], error_output, re.IGNORECASE):
                return {
                    "type": error_type,
                    "message": error_output,
                    "suggestions": pattern_info["suggestions"],
                    "solutions": pattern_info["solutions"]
                }
        
        return {
            "type": "unknown",
            "message": error_output,
            "suggestions": ["Try a different approach", "Use simpler tactics"],
            "solutions": ["Break into steps", "Use basic tactics"]
        }

    def _extract_sub_goals(self, goal: str) -> List[str]:
        """
        Extract potential sub-goals from a complex goal.
        """
        sub_goals = []
        
        # For bidirectional proofs
        if "↔" in goal or "iff" in goal.lower():
            parts = goal.split("↔") if "↔" in goal else goal.split("iff")
            if len(parts) == 2:
                sub_goals.extend([f"Prove: {parts[0].strip()}", f"Prove: {parts[1].strip()}"])
        
        # For universal quantifiers with multiple variables
        if goal.count("∀") > 1:
            # Extract individual universal statements
            import re
            matches = re.findall(r'∀\s*([^,]+),\s*([^∀]+)', goal)
            for var, prop in matches:
                sub_goals.append(f"∀ {var}, {prop.strip()}")
        
        # For complex equalities, suggest breaking into parts
        if "=" in goal and ("+" in goal or "*" in goal):
            sub_goals.append("Simplify left side")
            sub_goals.append("Simplify right side")
            sub_goals.append("Show equality")
        
        # Default sub-goal if none identified
        if not sub_goals:
            sub_goals.append(f"Prove: {goal}")
        
        return sub_goals

# Global instance
enhanced_prompts = EnhancedPromptEngine() 