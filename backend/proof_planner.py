# backend/proof_planner.py

"""
Intelligent Proof Planning System for AI Prover

This module provides advanced proof planning capabilities including proof decomposition,
tactic composition, and adaptive strategy selection.
"""

import logging
from typing import Dict, List, Any, Optional, Tuple
from lean_knowledge_base import lean_kb
from enhanced_prompts import enhanced_prompts

logger = logging.getLogger(__name__)

class ProofPlanner:
    """
    Intelligent proof planning system that can decompose complex proofs,
    compose tactics, and select optimal strategies.
    """
    
    def __init__(self):
        self.decomposition_strategies = self._build_decomposition_strategies()
        self.composition_rules = self._build_composition_rules()
        self.strategy_weights = self._build_strategy_weights()
        
    def _build_decomposition_strategies(self) -> Dict[str, List[str]]:
        """Build strategies for decomposing complex proofs."""
        return {
            "binomial_theorem": [
                "Expand (a + b)^2 using definition of power",
                "Apply distributive law to expand the expression",
                "Simplify using arithmetic properties (commutativity, associativity)",
                "Combine like terms to reach the final form"
            ],
            "de_morgan": [
                "Prove forward direction: ¬(P ∧ Q) → (¬P ∨ ¬Q)",
                "Prove backward direction: (¬P ∨ ¬Q) → ¬(P ∧ Q)",
                "Combine both directions using constructor"
            ],
            "exponential_properties": [
                "Use definition of power to expand (a^b)^c",
                "Apply associativity of multiplication",
                "Use power laws to simplify the expression",
                "Reach the final form a^(b*c)"
            ],
            "group_identity": [
                "Use the definition of identity element",
                "Apply the identity property to both elements",
                "Use transitivity of equality",
                "Conclude that the elements are equal"
            ],
            "double_negation": [
                "Prove ¬¬P → P using classical logic",
                "Prove P → ¬¬P using basic logic",
                "Combine using constructor for bidirectional proof"
            ]
        }
    
    def _build_composition_rules(self) -> Dict[str, List[str]]:
        """Build rules for composing tactics intelligently."""
        return {
            "unknown_constant": [
                "Try alternative theorem names from knowledge base",
                "Use simp with available lemmas instead",
                "Break into smaller steps with intro and exact",
                "Use constructor and handle each case"
            ],
            "type_mismatch": [
                "Add proper introductions before applying theorems",
                "Check variable types and ensure they match",
                "Use constructor to handle bidirectional proofs",
                "Break into subgoals and handle each separately"
            ],
            "tactic_failed": [
                "Try simpler tactics first",
                "Break the goal into subgoals",
                "Use a different approach entirely",
                "Apply induction if applicable"
            ],
            "definitional_equality": [
                "Use simp to simplify expressions",
                "Apply rewrite rules to transform the goal",
                "Use rw to rewrite using available lemmas",
                "Break into smaller steps"
            ]
        }
    
    def _build_strategy_weights(self) -> Dict[str, float]:
        """Build weights for different proof strategies."""
        return {
            "direct": 0.4,      # Use exact theorem if available
            "compositional": 0.3,  # Combine multiple tactics
            "structural": 0.2,   # Use constructor and cases
            "simplification": 0.1  # Use simp with available lemmas
        }
    
    def decompose_complex_proof(self, goal: str) -> List[str]:
        """Break complex proofs into manageable subgoals."""
        goal_type = self._classify_goal_type(goal)
        
        if goal_type in self.decomposition_strategies:
            return self.decomposition_strategies[goal_type]
        else:
            # Generic decomposition strategy
            return [
                "Introduce variables using intro",
                "Apply relevant theorems or lemmas",
                "Simplify using available tactics",
                "Complete the proof with exact or simp"
            ]
    
    def compose_tactics(self, base_tactic: str, error_output: str) -> List[str]:
        """Intelligently compose multiple tactics based on errors."""
        error_type = self._classify_error_type(error_output)
        
        if error_type in self.composition_rules:
            rules = self.composition_rules[error_type]
            composed_tactics = []
            
            for rule in rules:
                if "simp" in rule and "simp" not in base_tactic:
                    composed_tactics.append("simp [Nat.add_zero, Nat.add_comm, Nat.mul_add]")
                elif "intro" in rule and "intro" not in base_tactic:
                    composed_tactics.append("intro n; " + base_tactic)
                elif "constructor" in rule:
                    composed_tactics.append("constructor; " + base_tactic)
                else:
                    composed_tactics.append(base_tactic)
            
            return composed_tactics
        else:
            return [base_tactic]
    
    def select_proof_strategy(self, goal: str, available_theorems: List[str], 
                            difficulty: str = "medium") -> str:
        """Select the best proof strategy based on context."""
        
        # Analyze goal characteristics
        goal_features = self._analyze_goal_features(goal)
        
        # Calculate strategy scores
        strategy_scores = {}
        
        # Direct strategy score
        if self._has_exact_theorem(goal, available_theorems):
            strategy_scores["direct"] = self.strategy_weights["direct"] * 1.5
        else:
            strategy_scores["direct"] = self.strategy_weights["direct"] * 0.5
        
        # Compositional strategy score
        if goal_features["complexity"] > 0.7:
            strategy_scores["compositional"] = self.strategy_weights["compositional"] * 1.3
        else:
            strategy_scores["compositional"] = self.strategy_weights["compositional"]
        
        # Structural strategy score
        if goal_features["bidirectional"]:
            strategy_scores["structural"] = self.strategy_weights["structural"] * 1.4
        else:
            strategy_scores["structural"] = self.strategy_weights["structural"]
        
        # Simplification strategy score
        if goal_features["arithmetic"]:
            strategy_scores["simplification"] = self.strategy_weights["simplification"] * 1.2
        else:
            strategy_scores["simplification"] = self.strategy_weights["simplification"]
        
        # Select best strategy
        best_strategy = max(strategy_scores, key=strategy_scores.get)
        
        logger.info(f"Selected strategy '{best_strategy}' for goal: {goal[:50]}...")
        
        return best_strategy
    
    def generate_strategy_specific_tactic(self, goal: str, strategy: str, 
                                        available_theorems: List[str]) -> str:
        """Generate a tactic based on the selected strategy."""
        
        if strategy == "direct":
            return self._generate_direct_tactic(goal, available_theorems)
        elif strategy == "compositional":
            return self._generate_compositional_tactic(goal, available_theorems)
        elif strategy == "structural":
            return self._generate_structural_tactic(goal, available_theorems)
        elif strategy == "simplification":
            return self._generate_simplification_tactic(goal, available_theorems)
        else:
            return self._generate_fallback_tactic(goal, available_theorems)
    
    def _generate_direct_tactic(self, goal: str, available_theorems: List[str]) -> str:
        """Generate a direct tactic using exact theorem."""
        suggested_theorem = lean_kb.suggest_theorem(goal)
        
        if suggested_theorem and suggested_theorem in available_theorems:
            # Get usage pattern from knowledge base
            info = lean_kb.get_theorem_info(suggested_theorem)
            if info:
                return info.get("usage", f"exact {suggested_theorem}")
        
        # Fallback to pattern matching
        if "n + 0 = n" in goal:
            return "intro n; exact Nat.add_zero n"
        elif "a + b = b + a" in goal:
            return "intro a b; exact Nat.add_comm a b"
        elif "a * (b + c) = a * b + a * c" in goal:
            return "intro a b c; exact Nat.mul_add a b c"
        else:
            return "intro n; exact Nat.add_zero n"  # Safe fallback
    
    def _generate_compositional_tactic(self, goal: str, available_theorems: List[str]) -> str:
        """Generate a compositional tactic combining multiple approaches."""
        goal_type = self._classify_goal_type(goal)
        
        if goal_type == "binomial":
            return "intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]"
        elif goal_type == "double_negation":
            return "intro P; constructor; intro h; by_contra h1; contradiction"
        elif goal_type == "de_morgan":
            return "intro P Q; constructor; intro h; cases h; left; exact h; right; exact h"
        else:
            # Generic compositional approach
            return "intro n; simp [Nat.add_zero, Nat.add_comm, Nat.mul_add]"
    
    def _generate_structural_tactic(self, goal: str, available_theorems: List[str]) -> str:
        """Generate a structural tactic using constructor and cases."""
        if "↔" in goal or "iff" in goal.lower():
            return "constructor; intro h; exact h; intro h; exact h"
        elif "∧" in goal or "and" in goal.lower():
            return "constructor; exact h1; exact h2"
        elif "∨" in goal or "or" in goal.lower():
            return "cases h; left; exact h; right; exact h"
        else:
            return "constructor; intro h; exact h"
    
    def _generate_simplification_tactic(self, goal: str, available_theorems: List[str]) -> str:
        """Generate a simplification tactic using simp."""
        # Select relevant lemmas for simp
        lemmas = []
        
        if "add" in goal:
            lemmas.extend(["Nat.add_zero", "Nat.add_comm", "Nat.add_assoc"])
        if "mul" in goal:
            lemmas.extend(["Nat.mul_zero", "Nat.mul_comm", "Nat.mul_assoc", "Nat.mul_add"])
        if "pow" in goal or "^" in goal:
            lemmas.extend(["Nat.pow_zero", "Nat.pow_one"])
        
        if lemmas:
            return f"simp [{', '.join(lemmas)}]"
        else:
            return "simp [Nat.add_zero, Nat.add_comm, Nat.mul_add]"
    
    def _generate_fallback_tactic(self, goal: str, available_theorems: List[str]) -> str:
        """Generate a fallback tactic when other strategies fail."""
        return "intro n; simp [Nat.add_zero, Nat.add_comm, Nat.mul_add]"
    
    def _classify_goal_type(self, goal: str) -> str:
        """Classify the type of goal for decomposition."""
        goal_lower = goal.lower()
        
        if "binomial" in goal_lower or "(a + b)^2" in goal:
            return "binomial_theorem"
        elif "de morgan" in goal_lower or "¬(p ∧ q)" in goal:
            return "de_morgan"
        elif "exponential" in goal_lower or "(a^b)^c" in goal:
            return "exponential_properties"
        elif "group" in goal_lower and "identity" in goal_lower:
            return "group_identity"
        elif "double negation" in goal_lower or "¬¬p" in goal:
            return "double_negation"
        else:
            return "generic"
    
    def _classify_error_type(self, error_output: str) -> str:
        """Classify the type of error for composition."""
        error_lower = error_output.lower()
        
        if "unknown constant" in error_lower or "unknown identifier" in error_lower:
            return "unknown_constant"
        elif "type mismatch" in error_lower:
            return "type_mismatch"
        elif "tactic" in error_lower and "failed" in error_lower:
            return "tactic_failed"
        elif "definitionally equal" in error_lower:
            return "definitional_equality"
        else:
            return "unknown"
    
    def _analyze_goal_features(self, goal: str) -> Dict[str, Any]:
        """Analyze goal features for strategy selection."""
        return {
            "complexity": self._calculate_complexity(goal),
            "bidirectional": "↔" in goal or "iff" in goal.lower(),
            "arithmetic": any(op in goal for op in ["+", "*", "^", "≤", "<"]),
            "logical": any(op in goal for op in ["¬", "∧", "∨", "→", "↔"]),
            "quantified": "∀" in goal or "∃" in goal
        }
    
    def _calculate_complexity(self, goal: str) -> float:
        """Calculate the complexity of a goal (0.0 to 1.0)."""
        complexity = 0.0
        
        # Add complexity for different features
        if "∀" in goal or "∃" in goal:
            complexity += 0.3
        if "↔" in goal:
            complexity += 0.2
        if "∧" in goal or "∨" in goal:
            complexity += 0.2
        if "^" in goal:
            complexity += 0.2
        if "¬" in goal:
            complexity += 0.1
        
        return min(complexity, 1.0)
    
    def _has_exact_theorem(self, goal: str, available_theorems: List[str]) -> bool:
        """Check if there's an exact theorem for the goal."""
        suggested_theorem = lean_kb.suggest_theorem(goal)
        return suggested_theorem is not None and suggested_theorem in available_theorems

# Global instance
proof_planner = ProofPlanner() 