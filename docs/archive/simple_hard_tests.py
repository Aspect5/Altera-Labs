#!/usr/bin/env python3
"""
Simplified Hard Test Suite for LLM Performance Analysis
Uses only available Lean imports to avoid Mathlib errors
"""

import time
import logging
import json
from datetime import datetime
from llm_performance_tester import LLMPerformanceTester

# Enhanced logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('simple_hard_tests.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

def create_simple_hard_test_cases():
    """Create hard test cases using only available Lean imports."""
    from llm_performance_tester import TestCase
    
    return [
        # **HARD ARITHMETIC TESTS (using only Mathlib.Data.Nat.Basic)**
        TestCase(
            name="Distributive Law",
            description="Prove distributive property: a * (b + c) = a * b + a * c",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (a b c : ℕ), a * (b + c) = a * b + a * c := by sorry""",
            expected_tactic="intro a b c; exact Nat.mul_add a b c",
            difficulty="hard",
            category="arithmetic",
            max_attempts=5
        ),
        
        TestCase(
            name="Multiplication Identity",
            description="Prove that 1 * n = n for all natural numbers",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), 1 * n = n := by sorry""",
            expected_tactic="intro n; exact Nat.one_mul n",
            difficulty="medium",
            category="arithmetic",
            max_attempts=5
        ),
        
        TestCase(
            name="Addition Identity",
            description="Prove that n + 0 = n for all natural numbers",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n + 0 = n := by sorry""",
            expected_tactic="intro n; exact Nat.add_zero n",
            difficulty="medium",
            category="arithmetic",
            max_attempts=5
        ),
        
        # **LOGIC TESTS**
        TestCase(
            name="Double Negation",
            description="Prove double negation elimination: ¬¬P ↔ P",
            proof_state="""import Mathlib.Logic.Basic
theorem test : ∀ (P : Prop), ¬¬P ↔ P := by sorry""",
            expected_tactic="intro P; constructor; intro h; by_contra h1; contradiction; intro h; intro h1; contradiction",
            difficulty="hard",
            category="logic",
            max_attempts=6
        ),
        
        TestCase(
            name="False Elimination",
            description="Prove ex falso: False → P for any P",
            proof_state="""import Mathlib.Logic.Basic
theorem test : ∀ (P : Prop), False → P := by sorry""",
            expected_tactic="intro P h; contradiction",
            difficulty="medium",
            category="logic",
            max_attempts=5
        ),
        
        # **ADVANCED TESTS**
        TestCase(
            name="Successor Greater",
            description="Prove that n + 1 > n for all natural numbers",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n + 1 > n := by sorry""",
            expected_tactic="intro n; exact Nat.lt_succ_self n",
            difficulty="hard",
            category="advanced",
            max_attempts=5
        ),
        
        TestCase(
            name="Zero Less Equal",
            description="Prove that 0 ≤ n for all natural numbers",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), 0 ≤ n := by sorry""",
            expected_tactic="intro n; exact Nat.zero_le n",
            difficulty="medium",
            category="inequality",
            max_attempts=5
        ),
        
        TestCase(
            name="Reflexive Less Equal",
            description="Prove reflexive property: n ≤ n for all n",
            proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n ≤ n := by sorry""",
            expected_tactic="intro n; exact Nat.le_refl n",
            difficulty="medium",
            category="inequality",
            max_attempts=5
        )
    ]

def run_simple_hard_test_suite():
    """Run the simplified hard test suite with detailed performance analysis."""
    print("🚀 Starting SIMPLIFIED HARD Test Suite")
    print("=" * 60)
    
    # Create tester with hard test cases
    tester = LLMPerformanceTester()
    hard_tests = create_simple_hard_test_cases()
    
    # Replace test cases with hard ones
    tester.test_cases = hard_tests
    
    print(f"Running {len(hard_tests)} hard test cases...")
    print()
    
    # Track detailed metrics
    performance_data = []
    total_start = time.time()
    
    for i, test_case in enumerate(hard_tests, 1):
        print(f"Test {i}/{len(hard_tests)}: {test_case.name}")
        print(f"  Difficulty: {test_case.difficulty}")
        print(f"  Category: {test_case.category}")
        print(f"  Description: {test_case.description}")
        print(f"  Expected tactic: {test_case.expected_tactic}")
        print()
        
        test_start = time.time()
        
        try:
            # Run the test
            result = tester.run_single_test(test_case)
            test_time = time.time() - test_start
            
            # Analyze performance
            performance_metrics = {
                "test_name": test_case.name,
                "difficulty": test_case.difficulty,
                "category": test_case.category,
                "success": result.success,
                "attempts_used": result.attempts_used,
                "total_time": test_time,
                "average_time_per_attempt": test_time / result.attempts_used if result.attempts_used > 0 else 0,
                "error_messages": result.error_messages,
                "llm_quality": result.llm_response_quality
            }
            
            performance_data.append(performance_metrics)
            
            print(f"  ✅ Test completed in {test_time:.2f}s")
            print(f"  Success: {result.success}")
            print(f"  Attempts: {result.attempts_used}")
            print(f"  Avg time per attempt: {performance_metrics['average_time_per_attempt']:.2f}s")
            
            if result.error_messages:
                print(f"  Errors: {len(result.error_messages)}")
                for error in result.error_messages[:2]:  # Show first 2 errors
                    print(f"    - {error[:100]}...")
            
        except Exception as e:
            test_time = time.time() - test_start
            print(f"  ❌ Test failed after {test_time:.2f}s")
            print(f"  Error: {str(e)}")
            logger.error(f"Test '{test_case.name}' failed: {e}", exc_info=True)
        
        print("-" * 50)
    
    total_time = time.time() - total_start
    
    # Generate analysis
    analysis = analyze_performance(performance_data, total_time)
    
    # Print summary
    print_summary(analysis)
    
    # Save detailed report
    save_report(analysis)
    
    return analysis

def analyze_performance(performance_data, total_time):
    """Analyze performance data and identify bottlenecks."""
    
    if not performance_data:
        return {"error": "No performance data available"}
    
    # Basic statistics
    total_tests = len(performance_data)
    successful_tests = sum(1 for p in performance_data if p["success"])
    success_rate = (successful_tests / total_tests) * 100
    
    # Time analysis
    times = [p["total_time"] for p in performance_data]
    avg_time = sum(times) / len(times)
    max_time = max(times)
    min_time = min(times)
    
    # Attempt analysis
    attempts = [p["attempts_used"] for p in performance_data]
    avg_attempts = sum(attempts) / len(attempts)
    max_attempts = max(attempts)
    
    # Difficulty breakdown
    difficulty_stats = {}
    for p in performance_data:
        diff = p["difficulty"]
        if diff not in difficulty_stats:
            difficulty_stats[diff] = {"count": 0, "success": 0, "total_time": 0}
        difficulty_stats[diff]["count"] += 1
        difficulty_stats[diff]["total_time"] += p["total_time"]
        if p["success"]:
            difficulty_stats[diff]["success"] += 1
    
    # Calculate success rates by difficulty
    for diff in difficulty_stats:
        count = difficulty_stats[diff]["count"]
        success = difficulty_stats[diff]["success"]
        difficulty_stats[diff]["success_rate"] = (success / count) * 100
        difficulty_stats[diff]["avg_time"] = difficulty_stats[diff]["total_time"] / count
    
    # Bottleneck analysis
    bottlenecks = identify_bottlenecks(performance_data)
    
    # Error analysis
    error_analysis = analyze_errors(performance_data)
    
    return {
        "summary": {
            "total_tests": total_tests,
            "successful_tests": successful_tests,
            "failed_tests": total_tests - successful_tests,
            "success_rate": success_rate,
            "total_time": total_time,
            "average_time_per_test": avg_time,
            "min_time": min_time,
            "max_time": max_time,
            "average_attempts": avg_attempts,
            "max_attempts": max_attempts
        },
        "difficulty_breakdown": difficulty_stats,
        "bottlenecks": bottlenecks,
        "error_analysis": error_analysis,
        "detailed_data": performance_data
    }

def identify_bottlenecks(performance_data):
    """Identify performance bottlenecks."""
    bottlenecks = {
        "primary_bottleneck": None,
        "slow_tests": [],
        "high_attempt_tests": [],
        "optimization_opportunities": []
    }
    
    # Find slow tests (>30 seconds)
    slow_tests = [p for p in performance_data if p["total_time"] > 30]
    bottlenecks["slow_tests"] = [(p["test_name"], p["total_time"]) for p in slow_tests]
    
    # Find tests with many attempts (>5)
    high_attempt_tests = [p for p in performance_data if p["attempts_used"] > 5]
    bottlenecks["high_attempt_tests"] = [(p["test_name"], p["attempts_used"]) for p in high_attempt_tests]
    
    # Identify primary bottleneck
    avg_time = sum(p["total_time"] for p in performance_data) / len(performance_data)
    avg_attempts = sum(p["attempts_used"] for p in performance_data) / len(performance_data)
    
    if avg_time > 25:
        bottlenecks["primary_bottleneck"] = "Slow execution time"
        bottlenecks["optimization_opportunities"].append("Optimize Lean verification process")
        bottlenecks["optimization_opportunities"].append("Implement proof caching")
    elif avg_attempts > 4:
        bottlenecks["primary_bottleneck"] = "High attempt count"
        bottlenecks["optimization_opportunities"].append("Improve LLM prompt engineering")
        bottlenecks["optimization_opportunities"].append("Add more training examples")
    else:
        bottlenecks["primary_bottleneck"] = "Balanced performance"
    
    return bottlenecks

def analyze_errors(performance_data):
    """Analyze error patterns."""
    error_analysis = {
        "total_errors": 0,
        "common_error_patterns": {},
        "error_by_difficulty": {},
        "error_by_category": {}
    }
    
    for p in performance_data:
        if not p["success"]:
            error_analysis["total_errors"] += 1
            
            # Count errors by difficulty
            diff = p["difficulty"]
            if diff not in error_analysis["error_by_difficulty"]:
                error_analysis["error_by_difficulty"][diff] = 0
            error_analysis["error_by_difficulty"][diff] += 1
            
            # Count errors by category
            cat = p["category"]
            if cat not in error_analysis["error_by_category"]:
                error_analysis["error_by_category"][cat] = 0
            error_analysis["error_by_category"][cat] += 1
            
            # Analyze error messages
            for error in p["error_messages"]:
                # Extract common error patterns
                if "unknown tactic" in error.lower():
                    pattern = "Unknown tactic"
                elif "unsolved goals" in error.lower():
                    pattern = "Unsolved goals"
                elif "unexpected identifier" in error.lower():
                    pattern = "Syntax error"
                elif "no such file" in error.lower():
                    pattern = "Missing import"
                else:
                    pattern = "Other error"
                
                if pattern not in error_analysis["common_error_patterns"]:
                    error_analysis["common_error_patterns"][pattern] = 0
                error_analysis["common_error_patterns"][pattern] += 1
    
    return error_analysis

def print_summary(analysis):
    """Print a comprehensive summary of the analysis."""
    print("\n" + "=" * 60)
    print("📊 SIMPLIFIED HARD TEST SUITE SUMMARY")
    print("=" * 60)
    
    summary = analysis["summary"]
    print(f"Total Tests: {summary['total_tests']}")
    print(f"Successful: {summary['successful_tests']}")
    print(f"Failed: {summary['failed_tests']}")
    print(f"Success Rate: {summary['success_rate']:.1f}%")
    print(f"Total Time: {summary['total_time']:.2f}s")
    print(f"Average Time per Test: {summary['average_time_per_test']:.2f}s")
    print(f"Time Range: {summary['min_time']:.2f}s - {summary['max_time']:.2f}s")
    print(f"Average Attempts: {summary['average_attempts']:.1f}")
    print(f"Max Attempts: {summary['max_attempts']}")
    
    # Difficulty breakdown
    print(f"\n📈 BY DIFFICULTY:")
    for diff, stats in analysis["difficulty_breakdown"].items():
        print(f"  {diff.title()}: {stats['success']}/{stats['count']} ({stats['success_rate']:.1f}%) - {stats['avg_time']:.1f}s avg")
    
    # Bottlenecks
    bottlenecks = analysis["bottlenecks"]
    print(f"\n🔍 BOTTLENECK ANALYSIS:")
    print(f"Primary Bottleneck: {bottlenecks['primary_bottleneck']}")
    
    if bottlenecks["slow_tests"]:
        print(f"Slow Tests (>30s):")
        for test_name, time_taken in bottlenecks["slow_tests"]:
            print(f"  - {test_name}: {time_taken:.1f}s")
    
    if bottlenecks["high_attempt_tests"]:
        print(f"High Attempt Tests (>5 attempts):")
        for test_name, attempts in bottlenecks["high_attempt_tests"]:
            print(f"  - {test_name}: {attempts} attempts")
    
    # Error analysis
    error_analysis = analysis["error_analysis"]
    print(f"\n❌ ERROR ANALYSIS:")
    print(f"Total Errors: {error_analysis['total_errors']}")
    
    if error_analysis["common_error_patterns"]:
        print(f"Common Error Patterns:")
        for pattern, count in error_analysis["common_error_patterns"].items():
            print(f"  - {pattern}: {count}")
    
    # Recommendations
    print(f"\n💡 OPTIMIZATION OPPORTUNITIES:")
    for i, rec in enumerate(bottlenecks["optimization_opportunities"], 1):
        print(f"{i}. {rec}")
    
    print("=" * 60)

def save_report(analysis):
    """Save the analysis to a JSON file."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"simple_hard_test_analysis_{timestamp}.json"
    
    # Convert to serializable format
    serializable_analysis = {}
    for key, value in analysis.items():
        if key == "detailed_data":
            # Skip detailed data for file size
            continue
        serializable_analysis[key] = value
    
    with open(filename, 'w') as f:
        json.dump(serializable_analysis, f, indent=2, default=str)
    
    print(f"\n📄 Analysis saved to: {filename}")

if __name__ == "__main__":
    run_simple_hard_test_suite() 