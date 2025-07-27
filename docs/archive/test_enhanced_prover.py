# backend/test_enhanced_prover.py

"""
Enhanced AI Prover Test Suite

This script tests the improved AI prover with the new knowledge base,
enhanced prompt engineering, and intelligent proof planning systems.
"""

import logging
import time
from datetime import datetime
from typing import Dict, List, Any
from lean_verifier import LeanVerifier
from lean_knowledge_base import lean_kb
from enhanced_prompts import enhanced_prompts
from proof_planner import proof_planner

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class EnhancedProverTester:
    """Test suite for the enhanced AI prover."""
    
    def __init__(self):
        self.verifier = LeanVerifier(developer_mode=True, max_auto_solve_attempts=8)
        self.test_results = []
        
    def run_comprehensive_test_suite(self):
        """Run the comprehensive test suite."""
        logger.info("🚀 Starting Enhanced AI Prover Test Suite")
        logger.info("=" * 60)
        
        # Test the knowledge base
        self.test_knowledge_base()
        
        # Test the enhanced prompts
        self.test_enhanced_prompts()
        
        # Test the proof planner
        self.test_proof_planner()
        
        # Test the enhanced verifier
        self.test_enhanced_verifier()
        
        # Run performance tests
        self.run_performance_tests()
        
        # Generate report
        self.generate_test_report()
    
    def test_knowledge_base(self):
        """Test the Lean knowledge base functionality."""
        logger.info("📚 Testing Knowledge Base...")
        
        # Test theorem suggestions
        test_goals = [
            "∀ n, n + 0 = n",
            "∀ a b, a + b = b + a", 
            "∀ a b c, a * (b + c) = a * b + a * c",
            "∀ n, 0 ≤ n",
            "∀ n, n < n + 1"
        ]
        
        for goal in test_goals:
            theorem = lean_kb.suggest_theorem(goal)
            logger.info(f"Goal: {goal} -> Suggested: {theorem}")
        
        # Test tactic generation
        tactics = lean_kb.get_tactics_for_goal("∀ n, n + 0 = n", "medium")
        logger.info(f"Generated tactics: {tactics[:3]}")
        
        logger.info("✅ Knowledge Base tests completed")
    
    def test_enhanced_prompts(self):
        """Test the enhanced prompt engineering system."""
        logger.info("🎯 Testing Enhanced Prompts...")
        
        goal = "∀ n, n + 0 = n"
        available_theorems = lean_kb.get_available_theorems()
        
        # Test context-aware prompt
        context_prompt = enhanced_prompts.create_context_aware_prompt(
            goal, available_theorems, [], "medium"
        )
        logger.info(f"Context-aware prompt length: {len(context_prompt)}")
        
        # Test error-learning prompt
        error_prompt = enhanced_prompts.create_error_learning_prompt(
            goal, "unknown constant 'Nat.add_zero'", 2, ["rfl"]
        )
        logger.info(f"Error-learning prompt length: {len(error_prompt)}")
        
        # Test multi-strategy prompt
        strategy_prompt = enhanced_prompts.create_multi_strategy_prompt(goal, "medium")
        logger.info(f"Multi-strategy prompt length: {len(strategy_prompt)}")
        
        logger.info("✅ Enhanced Prompts tests completed")
    
    def test_proof_planner(self):
        """Test the intelligent proof planning system."""
        logger.info("🧠 Testing Proof Planner...")
        
        test_goals = [
            ("∀ n, n + 0 = n", "easy"),
            ("∀ a b, a + b = b + a", "medium"),
            ("∀ a b, (a + b)^2 = a^2 + 2*a*b + b^2", "hard"),
            ("∀ P, ¬¬P ↔ P", "hard")
        ]
        
        available_theorems = lean_kb.get_available_theorems()
        
        for goal, difficulty in test_goals:
            # Test strategy selection
            strategy = proof_planner.select_proof_strategy(goal, available_theorems, difficulty)
            logger.info(f"Goal: {goal[:30]}... -> Strategy: {strategy}")
            
            # Test goal classification
            goal_type = proof_planner._classify_goal_type(goal)
            logger.info(f"Goal type: {goal_type}")
            
            # Test tactic generation
            tactic = proof_planner.generate_strategy_specific_tactic(goal, strategy, available_theorems)
            logger.info(f"Generated tactic: {tactic}")
        
        logger.info("✅ Proof Planner tests completed")
    
    def test_enhanced_verifier(self):
        """Test the enhanced Lean verifier."""
        logger.info("🔍 Testing Enhanced Verifier...")
        
        # Test cases that previously failed
        test_cases = [
            {
                "name": "Double Negation (Previously Failed)",
                "goal": "∀ P, ¬¬P ↔ P",
                "expected": "intro P; constructor; intro h; by_contra h1; contradiction"
            },
            {
                "name": "Binomial Theorem (Previously Failed)", 
                "goal": "∀ a b, (a + b)^2 = a^2 + 2*a*b + b^2",
                "expected": "intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]"
            },
            {
                "name": "Exponential Properties (Previously Failed)",
                "goal": "∀ a b c, (a^b)^c = a^(b*c)",
                "expected": "intro a b c; exact Nat.pow_mul a b c"
            }
        ]
        
        for test_case in test_cases:
            logger.info(f"Testing: {test_case['name']}")
            
            # Create proof state
            proof_state = f"""
import Mathlib.Data.Nat.Basic

theorem test : {test_case['goal']} := by sorry
"""
            
            # Run auto-solve
            start_time = time.time()
            result = self.verifier.auto_solve_proof(proof_state)
            end_time = time.time()
            
            # Record result
            test_result = {
                "name": test_case["name"],
                "goal": test_case["goal"],
                "success": result.get("success", False),
                "attempts": result.get("attempts", 0),
                "time_taken": end_time - start_time,
                "strategy": result.get("strategy", "unknown"),
                "final_tactic": result.get("tactic", ""),
                "expected": test_case["expected"]
            }
            
            self.test_results.append(test_result)
            
            logger.info(f"Result: {'✅ SUCCESS' if test_result['success'] else '❌ FAILED'}")
            logger.info(f"Attempts: {test_result['attempts']}, Time: {test_result['time_taken']:.2f}s")
            logger.info(f"Strategy: {test_result['strategy']}")
            logger.info(f"Generated: {test_result['final_tactic']}")
            logger.info(f"Expected: {test_result['expected']}")
            logger.info("-" * 40)
    
    def run_performance_tests(self):
        """Run performance tests on the enhanced system."""
        logger.info("⚡ Running Performance Tests...")
        
        # Test basic cases that should work quickly
        basic_cases = [
            "∀ n, n + 0 = n",
            "∀ a b, a + b = b + a",
            "∀ a b c, a * (b + c) = a * b + a * c",
            "∀ n, 0 ≤ n",
            "∀ n, n < n + 1"
        ]
        
        performance_results = []
        
        for i, goal in enumerate(basic_cases):
            logger.info(f"Performance test {i+1}/{len(basic_cases)}: {goal}")
            
            proof_state = f"""
import Mathlib.Data.Nat.Basic

theorem test : {goal} := by sorry
"""
            
            start_time = time.time()
            result = self.verifier.auto_solve_proof(proof_state, max_attempts=3)
            end_time = time.time()
            
            performance_results.append({
                "goal": goal,
                "success": result.get("success", False),
                "time": end_time - start_time,
                "attempts": result.get("attempts", 0)
            })
        
        # Calculate performance metrics
        successful_tests = [r for r in performance_results if r["success"]]
        avg_time = sum(r["time"] for r in successful_tests) / len(successful_tests) if successful_tests else 0
        success_rate = len(successful_tests) / len(performance_results) * 100
        
        logger.info(f"Performance Results:")
        logger.info(f"Success Rate: {success_rate:.1f}%")
        logger.info(f"Average Time: {avg_time:.2f}s")
        logger.info(f"Successful Tests: {len(successful_tests)}/{len(performance_results)}")
    
    def generate_test_report(self):
        """Generate a comprehensive test report."""
        logger.info("📊 Generating Test Report...")
        
        # Calculate overall metrics
        total_tests = len(self.test_results)
        successful_tests = len([r for r in self.test_results if r["success"]])
        success_rate = (successful_tests / total_tests * 100) if total_tests > 0 else 0
        
        avg_attempts = sum(r["attempts"] for r in self.test_results) / total_tests if total_tests > 0 else 0
        avg_time = sum(r["time_taken"] for r in self.test_results) / total_tests if total_tests > 0 else 0
        
        # Generate report
        report = f"""
🎯 ENHANCED AI PROVER TEST REPORT
=====================================
Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

📈 OVERALL PERFORMANCE
---------------------
Total Tests: {total_tests}
Successful: {successful_tests}
Failed: {total_tests - successful_tests}
Success Rate: {success_rate:.1f}%

⏱️ TIMING METRICS
-----------------
Average Time: {avg_time:.2f}s
Average Attempts: {avg_attempts:.1f}

🧪 INDIVIDUAL TEST RESULTS
-------------------------
"""
        
        for result in self.test_results:
            status = "✅ PASS" if result["success"] else "❌ FAIL"
            report += f"""
{status} {result['name']}
  Goal: {result['goal']}
  Strategy: {result['strategy']}
  Attempts: {result['attempts']}
  Time: {result['time_taken']:.2f}s
  Generated: {result['final_tactic']}
  Expected: {result['expected']}
"""
        
        # Save report
        with open(f"enhanced_prover_test_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt", "w") as f:
            f.write(report)
        
        logger.info("📄 Test report generated and saved")
        logger.info(f"Overall Success Rate: {success_rate:.1f}%")
        
        return report

def main():
    """Main test execution function."""
    tester = EnhancedProverTester()
    tester.run_comprehensive_test_suite()

if __name__ == "__main__":
    main() 