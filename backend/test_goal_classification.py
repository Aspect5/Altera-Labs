#!/usr/bin/env python3
"""
Test script to verify goal classification fixes.
"""

from lean_verifier import LeanVerifier

def test_goal_classification():
    """Test the goal classification logic."""
    verifier = LeanVerifier()
    
    test_cases = [
        ("theorem test : 1 + 1 = 2 := by sorry", "simple_arithmetic"),
        ("theorem test : ∀ a b : ℕ, a + b = b + a := by sorry", "commutativity"),
        ("theorem test : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := by sorry", "associativity"),
        ("theorem test : ∀ n : ℕ, n + 0 = n := by sorry", "identity"),
        ("theorem test : ∀ x : ℕ, x > 0 := by sorry", "universal"),
    ]
    
    print("Testing goal classification:")
    print("=" * 50)
    
    for goal, expected in test_cases:
        actual = verifier._fast_goal_classification(goal)
        status = "✅" if actual == expected else "❌"
        print(f"{status} Goal: {goal}")
        print(f"   Expected: {expected}, Got: {actual}")
        print()
    
    # Test tactic generation
    print("Testing tactic generation:")
    print("=" * 50)
    
    simple_goal = "theorem test : 1 + 1 = 2 := by sorry"
    goal_type = verifier._fast_goal_classification(simple_goal)
    tactics = verifier._generate_optimized_tactics(simple_goal, goal_type)
    
    print(f"Goal: {simple_goal}")
    print(f"Classified as: {goal_type}")
    print(f"Generated tactics: {tactics}")
    print()
    
    # Test a simple verification
    print("Testing simple verification:")
    print("=" * 50)
    
    # Create a proper Lean file for testing
    lean_content = """
import Mathlib.Data.Nat.Basic

theorem test : 1 + 1 = 2 := by
  rfl
"""
    
    result = verifier.run_lean_verification("rfl", lean_content)
    print(f"Verification result: {result['success']}")
    if not result['success']:
        print(f"Error: {result.get('error', 'Unknown error')}")

if __name__ == "__main__":
    test_goal_classification() 