# backend/lean_knowledge_base.py

"""
Comprehensive Lean 4 Knowledge Base for AI Prover

This module provides a structured knowledge base of available Lean 4 theorems,
tactics, and proof patterns that the AI prover can use to generate correct
mathematical proofs.
"""

import logging
from typing import Dict, List, Any, Optional
from pathlib import Path
import subprocess
import re

logger = logging.getLogger(__name__)

class LeanKnowledgeBase:
    """
    Comprehensive knowledge base for Lean 4 mathematical proofs.
    
    Contains available theorems, tactics, and proof patterns organized by
    mathematical domain and difficulty level.
    """
    
    def __init__(self):
        self.knowledge_base = self._build_knowledge_base()
        self.available_imports = self._detect_available_imports()
        self.theorem_database = self._build_theorem_database()
        
    def _build_knowledge_base(self) -> Dict[str, Any]:
        """Build the comprehensive knowledge base."""
        return {
            "arithmetic": {
                "basic_operations": {
                    "theorems": [
                        "Nat.add_zero", "Nat.zero_add", "Nat.add_comm", "Nat.add_assoc",
                        "Nat.mul_zero", "Nat.zero_mul", "Nat.mul_comm", "Nat.mul_assoc",
                        "Nat.one_mul", "Nat.mul_one", "Nat.mul_add", "Nat.add_mul"
                    ],
                    "tactics": [
                        "intro n; exact Nat.add_zero n",
                        "intro a b; exact Nat.add_comm a b",
                        "intro a b c; exact Nat.add_assoc a b c",
                        "intro n; exact Nat.one_mul n",
                        "intro a b c; exact Nat.mul_add a b c"
                    ],
                    "patterns": [
                        "intro n; exact Nat.add_zero n",
                        "intro a b; exact Nat.add_comm a b",
                        "intro a b c; exact Nat.mul_add a b c"
                    ]
                },
                "exponents": {
                    "theorems": [
                        "Nat.pow_zero", "Nat.pow_one", "Nat.pow_add", "Nat.pow_mul"
                    ],
                    "tactics": [
                        "intro a b c; exact Nat.pow_mul a b c",
                        "intro a b; exact Nat.pow_add a b"
                    ],
                    "patterns": [
                        "intro a b c; exact Nat.pow_mul a b c"
                    ]
                },
                "binomial": {
                    "theorems": [
                        "add_sq", "sub_sq", "Nat.pow_two", "Nat.mul_add", "Nat.add_mul"
                    ],
                    "tactics": [
                        "intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]",
                        "intro a b; rw [Nat.pow_two]; simp [Nat.mul_add, Nat.add_mul]"
                    ],
                    "patterns": [
                        "intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]"
                    ]
                }
            },
            "inequality": {
                "basic_inequalities": {
                    "theorems": [
                        "Nat.zero_le", "Nat.le_refl", "Nat.lt_succ_self", "Nat.le_succ"
                    ],
                    "tactics": [
                        "intro n; exact Nat.zero_le n",
                        "intro n; exact Nat.le_refl n",
                        "intro n; exact Nat.lt_succ_self n"
                    ],
                    "patterns": [
                        "intro n; exact Nat.zero_le n",
                        "intro n; exact Nat.lt_succ_self n"
                    ]
                }
            },
            "logic": {
                "basic_logic": {
                    "theorems": [
                        "Classical.not_not", "Classical.not_not_iff", "False.elim"
                    ],
                    "tactics": [
                        "intro P; intro h_false; exact False.elim h_false",
                        "intro h; exact h"
                    ],
                    "patterns": [
                        "intro P; intro h_false; exact False.elim h_false"
                    ]
                },
                "double_negation": {
                    "theorems": [
                        "Classical.not_not", "Classical.not_not_iff"
                    ],
                    "tactics": [
                        "intro P; constructor; intro h; by_contra h1; contradiction",
                        "intro P; intro h; by_contra h1; contradiction"
                    ],
                    "patterns": [
                        "intro P; constructor; intro h; by_contra h1; contradiction"
                    ]
                },
                "de_morgan": {
                    "theorems": [
                        "not_and_iff_or_not", "not_or_iff_and_not"
                    ],
                    "tactics": [
                        "intro P Q; constructor; intro h; cases h; left; exact h; right; exact h",
                        "intro P Q; constructor; intro h; intro h1; cases h; contradiction; contradiction"
                    ],
                    "patterns": [
                        "intro P Q; constructor; intro h; cases h; left; exact h; right; exact h"
                    ]
                }
            },
            "advanced": {
                "fibonacci": {
                    "theorems": ["fib"],
                    "tactics": [
                        "intro n; rw [fib]; rfl",
                        "intro n; rfl"
                    ],
                    "patterns": [
                        "intro n; rfl"
                    ]
                },
                "group_theory": {
                    "theorems": ["Group.one_mul", "Group.mul_one", "Group.mul_inv_self"],
                    "tactics": [
                        "intro G _inst_1 e1 e2 h1 h2; specialize h1 e2; specialize h2 e1; cases h1; cases h2; rw [←h2, h1]"
                    ],
                    "patterns": [
                        "intro G _inst_1 e1 e2 h1 h2; specialize h1 e2; specialize h2 e1; cases h1; cases h2; rw [←h2, h1]"
                    ]
                }
            }
        }
    
    def _detect_available_imports(self) -> List[str]:
        """Detect available imports in the Lean project."""
        try:
            lean_project_path = Path("backend/lean_verifier")
            lakefile_path = lean_project_path / "lakefile.toml"
            
            if lakefile_path.exists():
                with open(lakefile_path, 'r') as f:
                    content = f.read()
                
                # Extract dependencies from lakefile.toml
                dependencies = re.findall(r'require\s+([^\s]+)', content)
                return dependencies
            else:
                return ["Mathlib.Data.Nat.Basic", "Mathlib.Logic.Basic"]
                
        except Exception as e:
            logger.warning(f"Could not detect available imports: {e}")
            return ["Mathlib.Data.Nat.Basic", "Mathlib.Logic.Basic"]
    
    def _build_theorem_database(self) -> Dict[str, Any]:
        """Build a database of available theorems with usage examples."""
        return {
            "Nat.add_zero": {
                "type": "theorem",
                "signature": "∀ (n : ℕ), n + 0 = n",
                "usage": "intro n; exact Nat.add_zero n",
                "category": "arithmetic"
            },
            "Nat.add_comm": {
                "type": "theorem", 
                "signature": "∀ (a b : ℕ), a + b = b + a",
                "usage": "intro a b; exact Nat.add_comm a b",
                "category": "arithmetic"
            },
            "Nat.mul_add": {
                "type": "theorem",
                "signature": "∀ (a b c : ℕ), a * (b + c) = a * b + a * c", 
                "usage": "intro a b c; exact Nat.mul_add a b c",
                "category": "arithmetic"
            },
            "Nat.zero_le": {
                "type": "theorem",
                "signature": "∀ (n : ℕ), 0 ≤ n",
                "usage": "intro n; exact Nat.zero_le n", 
                "category": "inequality"
            },
            "Nat.lt_succ_self": {
                "type": "theorem",
                "signature": "∀ (n : ℕ), n < n + 1",
                "usage": "intro n; exact Nat.lt_succ_self n",
                "category": "inequality"
            },
            "False.elim": {
                "type": "theorem",
                "signature": "∀ (P : Prop), False → P",
                "usage": "intro P; intro h_false; exact False.elim h_false",
                "category": "logic"
            },
            "Classical.not_not": {
                "type": "theorem", 
                "signature": "∀ (P : Prop), ¬¬P → P",
                "usage": "intro P; intro h; by_contra h1; contradiction",
                "category": "logic"
            }
        }
    
    def get_available_theorems(self, category: str = None) -> List[str]:
        """Get available theorems for a given category."""
        if category:
            return self.theorem_database.get(category, {}).keys()
        else:
            return list(self.theorem_database.keys())
    
    def get_theorem_info(self, theorem_name: str) -> Optional[Dict[str, Any]]:
        """Get detailed information about a specific theorem."""
        return self.theorem_database.get(theorem_name)
    
    def suggest_theorem(self, goal: str) -> Optional[str]:
        """
        Suggest the most appropriate theorem for a given goal.
        Enhanced with compositional reasoning patterns from Ineq-Comp research.
        """
        # Clean the goal
        goal = goal.strip()
        
        # Pattern matching for common goals
        patterns = {
            # Addition properties
            r"∀\s*n\s*,\s*n\s*\+\s*0\s*=\s*n": "Nat.add_zero",
            r"∀\s*a\s*b\s*,\s*a\s*\+\s*b\s*=\s*b\s*\+\s*a": "Nat.add_comm",
            r"∀\s*a\s*b\s*c\s*,\s*a\s*\+\s*\(b\s*\+\s*c\)\s*=\s*\(a\s*\+\s*b\)\s*\+\s*c": "Nat.add_assoc",
            
            # Multiplication properties
            r"∀\s*n\s*,\s*n\s*\*\s*1\s*=\s*n": "Nat.one_mul",
            r"∀\s*n\s*,\s*1\s*\*\s*n\s*=\s*n": "Nat.one_mul",
            r"∀\s*a\s*b\s*,\s*a\s*\*\s*b\s*=\s*b\s*\*\s*a": "Nat.mul_comm",
            r"∀\s*a\s*b\s*c\s*,\s*a\s*\*\s*\(b\s*\+\s*c\)\s*=\s*a\s*\*\s*b\s*\+\s*a\s*\*\s*c": "Nat.mul_add",
            
            # Power properties - Fixed patterns
            r"∀\s*a\s*b\s*c\s*,\s*\(a\^b\)\^c\s*=\s*a\^\(b\s*\*\s*c\)": "Nat.pow_mul",
            r"∀\s*a\s*b\s*,\s*\(a\s*\+\s*b\)\^2\s*=\s*a\^2\s*\+\s*2\s*\*\s*a\s*\*\s*b\s*\+\s*b\^2": "binomial_expansion",
            
            # Inequality properties
            r"∀\s*n\s*,\s*0\s*≤\s*n": "Nat.zero_le",
            r"∀\s*n\s*,\s*n\s*<\s*n\s*\+\s*1": "Nat.lt_succ_self",
            
            # Logic properties
            r"∀\s*P\s*,\s*¬¬P\s*↔\s*P": "Classical.not_not_iff"
        }
        
        # Try exact pattern matching first
        for pattern, theorem in patterns.items():
            if re.match(pattern, goal, re.IGNORECASE):
                return theorem
        
        # Enhanced compositional reasoning patterns (based on Ineq-Comp research)
        compositional_patterns = {
            # Variable duplication patterns
            r".*\(.*\+.*\)\^2.*": "binomial_expansion",
            r".*\(.*\-.*\)\^2.*": "binomial_expansion",
            
            # Algebraic rewriting patterns
            r".*\*\s*\(.*\+.*\).*": "Nat.mul_add",
            r".*\*\s*\(.*\-.*\).*": "Nat.mul_sub",
            
            # Multi-step composition patterns
            r".*≤.*≤.*": "transitivity_inequality",
            r".*<.*<.*": "transitivity_strict_inequality",
            r".*=\s*.*=\s*.*": "transitivity_equality"
        }
        
        for pattern, theorem in compositional_patterns.items():
            if re.search(pattern, goal, re.IGNORECASE):
                return theorem
        
        # Try partial matching for more complex goals
        if "add" in goal.lower() and "comm" in goal.lower():
            return "Nat.add_comm"
        elif "mul" in goal.lower() and "comm" in goal.lower():
            return "Nat.mul_comm"
        elif "add" in goal.lower() and "assoc" in goal.lower():
            return "Nat.add_assoc"
        elif "mul" in goal.lower() and "add" in goal.lower():
            return "Nat.mul_add"
        elif "pow" in goal.lower() or "^" in goal:
            return "Nat.pow_mul"
        elif "≤" in goal or "le" in goal.lower():
            return "Nat.zero_le"
        elif "<" in goal or "lt" in goal.lower():
            return "Nat.lt_succ_self"
        elif "¬" in goal or "not" in goal.lower():
            return "Classical.not_not_iff"
        
        return None

    def get_compositional_strategies(self, goal: str) -> List[str]:
        """
        Get compositional reasoning strategies for complex goals.
        Based on Ineq-Comp research on human-intuitive compositional reasoning.
        """
        strategies = []
        
        # Decomposition strategies
        if "↔" in goal or "iff" in goal.lower():
            strategies.append("DECOMPOSE_BIDIRECTIONAL: Break into two separate implications")
        
        if goal.count("∀") > 1:
            strategies.append("DECOMPOSE_UNIVERSAL: Handle each universal quantifier separately")
        
        # Variable duplication strategies
        if "(" in goal and ")" in goal and ("+" in goal or "-" in goal):
            strategies.append("VARIABLE_DUPLICATION: Use substitution to handle repeated patterns")
        
        # Algebraic rewriting strategies
        if "=" in goal and ("+" in goal or "*" in goal):
            strategies.append("ALGEBRAIC_REWRITING: Use systematic transformations to simplify")
        
        # Multi-step composition strategies
        if "≤" in goal or "<" in goal:
            strategies.append("TRANSITIVITY_CHAIN: Use transitivity properties to chain inequalities")
        
        # Human-intuitive strategies
        strategies.append("HUMAN_INTUITIVE: Think like a human mathematician, not just syntax")
        strategies.append("PATTERN_RECOGNITION: Look for familiar mathematical patterns")
        
        return strategies

    def get_tactics_for_goal(self, goal: str, difficulty: str = "medium") -> List[str]:
        """
        Get appropriate tactics for a given goal and difficulty level.
        Enhanced with compositional reasoning strategies.
        """
        suggested_theorem = self.suggest_theorem(goal)
        compositional_strategies = self.get_compositional_strategies(goal)
        tactics = []
        
        if suggested_theorem:
            # Add direct theorem application
            if suggested_theorem == "Nat.add_zero":
                tactics.append("intro n; exact Nat.add_zero n")
            elif suggested_theorem == "Nat.add_comm":
                tactics.append("intro a b; exact Nat.add_comm a b")
            elif suggested_theorem == "Nat.add_assoc":
                tactics.append("intro a b c; exact Nat.add_assoc a b c")
            elif suggested_theorem == "Nat.one_mul":
                tactics.append("intro n; exact Nat.one_mul n")
            elif suggested_theorem == "Nat.mul_comm":
                tactics.append("intro a b; exact Nat.mul_comm a b")
            elif suggested_theorem == "Nat.mul_add":
                tactics.append("intro a b c; exact Nat.mul_add a b c")
            elif suggested_theorem == "Nat.pow_mul":
                tactics.append("intro a b c; exact Nat.pow_mul a b c")
            elif suggested_theorem == "Nat.zero_le":
                tactics.append("intro n; exact Nat.zero_le n")
            elif suggested_theorem == "Nat.lt_succ_self":
                tactics.append("intro n; exact Nat.lt_succ_self n")
            elif suggested_theorem == "Classical.not_not_iff":
                tactics.append("intro P; constructor; intro h; by_contra h1; contradiction")
            elif suggested_theorem == "binomial_expansion":
                tactics.append("intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]")
            elif suggested_theorem == "transitivity_inequality":
                tactics.append("intro a b c; constructor; intro h; exact Nat.le_trans a b c h")
            elif suggested_theorem == "transitivity_equality":
                tactics.append("intro a b c; constructor; intro h; exact Eq.trans a b c h")
        
        # Add compositional reasoning tactics
        for strategy in compositional_strategies:
            if "DECOMPOSE_BIDIRECTIONAL" in strategy:
                tactics.append("constructor; intro h; exact h")
            elif "DECOMPOSE_UNIVERSAL" in strategy:
                tactics.append("intro a b; exact theorem_name a b")
            elif "ALGEBRAIC_REWRITING" in strategy:
                tactics.append("intro a b; simp [Nat.add_comm, Nat.mul_comm, Nat.add_assoc]")
            elif "TRANSITIVITY_CHAIN" in strategy:
                tactics.append("intro a b c; constructor; intro h; exact Nat.le_trans a b c h")
        
        # Add fallback tactics based on difficulty
        if difficulty == "easy":
            tactics.extend([
                "intro n; rfl",
                "intro n; exact Nat.add_zero n",
                "intro a b; exact Nat.add_comm a b"
            ])
        elif difficulty == "medium":
            tactics.extend([
                "intro a b c; exact Nat.mul_add a b c",
                "intro a b; simp [Nat.add_comm, Nat.mul_comm]",
                "intro n; constructor; intro h; exact h"
            ])
        else:  # hard
            tactics.extend([
                "intro a b c; exact Nat.pow_mul a b c",
                "intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]",
                "intro P; constructor; intro h; by_contra h1; contradiction"
            ])
        
        return tactics[:5]  # Return top 5 tactics

    def get_proof_patterns(self, goal_type: str) -> List[str]:
        """
        Get proof patterns for different types of goals.
        """
        patterns = {
            "equality": [
                "intro n; exact theorem_name n",
                "intro a b; exact theorem_name a b",
                "intro a b c; exact theorem_name a b c"
            ],
            "inequality": [
                "intro n; exact Nat.zero_le n",
                "intro n; exact Nat.lt_succ_self n",
                "intro n; rfl"
            ],
            "bidirectional": [
                "constructor; intro h; exact h",
                "constructor; intro h; by_contra h1; contradiction"
            ],
            "arithmetic": [
                "intro a b; simp [Nat.add_comm, Nat.mul_comm]",
                "intro a b c; simp [Nat.mul_add, Nat.add_mul]",
                "intro a b; ring"
            ],
            "logic": [
                "intro P; constructor; intro h; by_contra h1; contradiction",
                "intro P; exact Classical.not_not_iff P"
            ]
        }
        
        return patterns.get(goal_type, patterns["equality"])
        """Get proof patterns for a given goal type."""
        patterns = []
        
        # Map goal types to categories
        goal_mapping = {
            "addition_identity": "arithmetic.basic_operations",
            "multiplication_identity": "arithmetic.basic_operations", 
            "commutativity": "arithmetic.basic_operations",
            "associativity": "arithmetic.basic_operations",
            "distributivity": "arithmetic.basic_operations",
            "exponential": "arithmetic.exponents",
            "binomial": "arithmetic.binomial",
            "inequality": "inequality.basic_inequalities",
            "double_negation": "logic.double_negation",
            "de_morgan": "logic.de_morgan",
            "false_elimination": "logic.basic_logic",
            "fibonacci": "advanced.fibonacci",
            "group_theory": "advanced.group_theory"
        }
        
        if goal_type in goal_mapping:
            category, subcategory = goal_mapping[goal_type].split(".")
            if category in self.knowledge_base and subcategory in self.knowledge_base[category]:
                patterns = self.knowledge_base[category][subcategory].get("patterns", [])
        
        return patterns
    
    def suggest_theorem(self, goal: str) -> Optional[str]:
        """Suggest a theorem based on the goal."""
        # Simple pattern matching for theorem suggestion
        if "n + 0 = n" in goal or "0 + n = n" in goal:
            return "Nat.add_zero"
        elif "a + b = b + a" in goal:
            return "Nat.add_comm"
        elif "a * (b + c) = a * b + a * c" in goal:
            return "Nat.mul_add"
        elif "0 ≤ n" in goal:
            return "Nat.zero_le"
        elif "n < n + 1" in goal:
            return "Nat.lt_succ_self"
        elif "False → P" in goal:
            return "False.elim"
        elif "¬¬P → P" in goal:
            return "Classical.not_not"
        
        return None

# Global instance
lean_kb = LeanKnowledgeBase() 