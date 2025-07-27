#!/usr/bin/env python3
"""
Performance Testing Script for Proving Agent Improvements

This script tests the performance improvements implemented in the Proving Agent,
including proof caching and Lean environment optimization.
"""

import time
import json
import logging
from datetime import datetime
from typing import Dict, List, Any
from lean_verifier import LeanVerifier
from proof_cache import proof_cache
from lean_environment_manager import lean_env_manager

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class PerformanceTester:
    """Test suite for measuring Proving Agent performance improvements."""
    
    def __init__(self):
        self.verifier = LeanVerifier(developer_mode=True)
        self.test_cases = self._load_test_cases()
        self.results = []
        
    def _load_test_cases(self) -> List[Dict[str, Any]]:
        """Load test cases for performance testing."""
        return [
            {
                "name": "Simple Addition",
                "proof_state": "theorem test : 1 + 1 = 2 := by sorry",
                "expected_tactic": "rfl",
                "category": "arithmetic",
                "difficulty": "easy"
            },
            {
                "name": "Zero Addition",
                "proof_state": "theorem test : ∀ n : ℕ, n + 0 = n := by sorry",
                "expected_tactic": "intro n; exact Nat.add_zero n",
                "category": "arithmetic",
                "difficulty": "medium"
            },
            {
                "name": "Addition Commutativity",
                "proof_state": "theorem test : ∀ a b : ℕ, a + b = b + a := by sorry",
                "expected_tactic": "intro a b; exact Nat.add_comm a b",
                "category": "arithmetic",
                "difficulty": "medium"
            },
            {
                "name": "Multiplication Commutativity",
                "proof_state": "theorem test : ∀ a b : ℕ, a * b = b * a := by sorry",
                "expected_tactic": "intro a b; exact Nat.mul_comm a b",
                "category": "arithmetic",
                "difficulty": "medium"
            },
            {
                "name": "Addition Associativity",
                "proof_state": "theorem test : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := by sorry",
                "expected_tactic": "intro a b c; exact Nat.add_assoc a b c",
                "category": "arithmetic",
                "difficulty": "medium"
            }
        ]
    
    def run_baseline_test(self) -> Dict[str, Any]:
        """Run baseline test without optimizations."""
        logger.info("Running baseline test (no optimizations)...")
        
        # Disable optimizations
        self.verifier.cache_enabled = False
        self.verifier.environment_optimized = False
        
        return self._run_test_suite("baseline")
    
    def run_optimized_test(self) -> Dict[str, Any]:
        """Run test with all optimizations enabled."""
        logger.info("Running optimized test (with caching and environment optimization)...")
        
        # Enable optimizations
        self.verifier.cache_enabled = True
        self.verifier.environment_optimized = False  # Will be optimized during first test
        
        return self._run_test_suite("optimized")
    
    def run_cache_test(self) -> Dict[str, Any]:
        """Run test to measure cache effectiveness."""
        logger.info("Running cache effectiveness test...")
        
        # Enable caching but disable environment optimization
        self.verifier.cache_enabled = True
        self.verifier.environment_optimized = False
        
        # Clear cache first
        proof_cache.clear_cache()
        
        # Run tests twice to measure cache hits
        first_run = self._run_test_suite("cache_first_run")
        second_run = self._run_test_suite("cache_second_run")
        
        # Get cache statistics
        cache_stats = proof_cache.get_cache_stats()
        
        return {
            "first_run": first_run,
            "second_run": second_run,
            "cache_stats": cache_stats,
            "cache_effectiveness": {
                "hit_rate": cache_stats.get("hit_rate", 0),
                "total_requests": cache_stats.get("total_requests", 0),
                "hits": cache_stats.get("hits", 0),
                "misses": cache_stats.get("misses", 0)
            }
        }
    
    def _run_test_suite(self, test_name: str) -> Dict[str, Any]:
        """Run a complete test suite."""
        results = []
        total_time = 0
        successful_tests = 0
        
        for i, test_case in enumerate(self.test_cases, 1):
            logger.info(f"Running {test_name} test {i}/{len(self.test_cases)}: {test_case['name']}")
            
            start_time = time.time()
            
            try:
                result = self.verifier.auto_solve_proof(
                    test_case["proof_state"], 
                    max_attempts=3
                )
                
                test_time = time.time() - start_time
                total_time += test_time
                
                if result["success"]:
                    successful_tests += 1
                
                test_result = {
                    "test_case": test_case["name"],
                    "success": result["success"],
                    "time": test_time,
                    "attempts": len(result.get("attempts", [])),
                    "tactic": result.get("tactic", ""),
                    "llm_time": result.get("llm_time", 0),
                    "verify_time": result.get("verify_time", 0)
                }
                
                results.append(test_result)
                
                logger.info(f"  ✅ {test_case['name']}: {'SUCCESS' if result['success'] else 'FAILED'} in {test_time:.2f}s")
                
            except Exception as e:
                test_time = time.time() - start_time
                total_time += test_time
                
                test_result = {
                    "test_case": test_case["name"],
                    "success": False,
                    "time": test_time,
                    "attempts": 0,
                    "error": str(e)
                }
                
                results.append(test_result)
                logger.error(f"  ❌ {test_case['name']}: ERROR in {test_time:.2f}s - {e}")
        
        return {
            "test_name": test_name,
            "total_tests": len(self.test_cases),
            "successful_tests": successful_tests,
            "success_rate": (successful_tests / len(self.test_cases)) * 100,
            "total_time": total_time,
            "average_time": total_time / len(self.test_cases),
            "results": results
        }
    
    def run_comprehensive_test(self) -> Dict[str, Any]:
        """Run comprehensive performance test."""
        logger.info("Starting comprehensive performance test...")
        
        start_time = time.time()
        
        # Get initial cache and environment stats
        initial_cache_stats = proof_cache.get_cache_stats()
        initial_env_stats = lean_env_manager.get_environment_status()
        
        # Run baseline test
        baseline_results = self.run_baseline_test()
        
        # Run optimized test
        optimized_results = self.run_optimized_test()
        
        # Run cache effectiveness test
        cache_results = self.run_cache_test()
        
        # Get final stats
        final_cache_stats = proof_cache.get_cache_stats()
        final_env_stats = lean_env_manager.get_environment_status()
        
        total_test_time = time.time() - start_time
        
        # Calculate improvements
        baseline_avg_time = baseline_results["average_time"]
        optimized_avg_time = optimized_results["average_time"]
        
        time_improvement = ((baseline_avg_time - optimized_avg_time) / baseline_avg_time) * 100
        
        # Generate comprehensive report
        report = {
            "timestamp": datetime.now().isoformat(),
            "total_test_time": total_test_time,
            "baseline_results": baseline_results,
            "optimized_results": optimized_results,
            "cache_results": cache_results,
            "performance_improvements": {
                "time_improvement_percent": time_improvement,
                "baseline_avg_time": baseline_avg_time,
                "optimized_avg_time": optimized_avg_time,
                "time_saved_per_test": baseline_avg_time - optimized_avg_time
            },
            "cache_analysis": {
                "initial_stats": initial_cache_stats,
                "final_stats": final_cache_stats,
                "cache_growth": final_cache_stats["total_entries"] - initial_cache_stats["total_entries"]
            },
            "environment_analysis": {
                "initial_stats": initial_env_stats,
                "final_stats": final_env_stats
            }
        }
        
        return report
    
    def save_report(self, report: Dict[str, Any], filename: str = None) -> str:
        """Save test report to file."""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"performance_test_report_{timestamp}.json"
        
        with open(filename, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        logger.info(f"Performance test report saved to {filename}")
        return filename
    
    def print_summary(self, report: Dict[str, Any]):
        """Print a summary of the test results."""
        print("\n" + "="*80)
        print("PROVING AGENT PERFORMANCE TEST RESULTS")
        print("="*80)
        
        # Baseline vs Optimized comparison
        baseline = report["baseline_results"]
        optimized = report["optimized_results"]
        improvements = report["performance_improvements"]
        
        print(f"\n📊 PERFORMANCE COMPARISON:")
        print(f"  Baseline Average Time: {baseline['average_time']:.2f}s")
        print(f"  Optimized Average Time: {optimized['average_time']:.2f}s")
        print(f"  Time Improvement: {improvements['time_improvement_percent']:.1f}%")
        print(f"  Time Saved per Test: {improvements['time_saved_per_test']:.2f}s")
        
        print(f"\n📈 SUCCESS RATES:")
        print(f"  Baseline Success Rate: {baseline['success_rate']:.1f}%")
        print(f"  Optimized Success Rate: {optimized['success_rate']:.1f}%")
        
        # Cache analysis
        cache_results = report["cache_results"]
        cache_stats = cache_results["cache_stats"]
        
        print(f"\n💾 CACHE EFFECTIVENESS:")
        print(f"  Cache Hit Rate: {cache_stats.get('hit_rate', 0):.1f}%")
        print(f"  Total Cache Requests: {cache_stats.get('total_requests', 0)}")
        print(f"  Cache Hits: {cache_stats.get('hits', 0)}")
        print(f"  Cache Misses: {cache_stats.get('misses', 0)}")
        print(f"  Cache Size: {cache_stats.get('cache_size_mb', 0):.2f}MB")
        
        # Environment analysis
        env_stats = report["environment_analysis"]["final_stats"]
        
        print(f"\n🔧 ENVIRONMENT OPTIMIZATION:")
        print(f"  Precompiled: {env_stats.get('precompiled', False)}")
        print(f"  Warmed Up: {env_stats.get('warmed_up', False)}")
        print(f"  Precompilation Time: {env_stats.get('stats', {}).get('precompilation_time', 0):.2f}s")
        print(f"  Warm-up Time: {env_stats.get('stats', {}).get('warmup_time', 0):.2f}s")
        
        print("\n" + "="*80)


def main():
    """Run the performance test suite."""
    print("🚀 Starting Proving Agent Performance Test Suite")
    print("="*80)
    
    tester = PerformanceTester()
    
    try:
        # Run comprehensive test
        report = tester.run_comprehensive_test()
        
        # Print summary
        tester.print_summary(report)
        
        # Save detailed report
        filename = tester.save_report(report)
        print(f"\n📄 Detailed report saved to: {filename}")
        
        # Determine if improvements meet targets
        improvements = report["performance_improvements"]
        time_improvement = improvements["time_improvement_percent"]
        
        if time_improvement >= 50:
            print(f"\n✅ SUCCESS: Achieved {time_improvement:.1f}% time improvement (target: 50%)")
        else:
            print(f"\n⚠️  PARTIAL SUCCESS: Achieved {time_improvement:.1f}% time improvement (target: 50%)")
        
        return report
        
    except Exception as e:
        logger.error(f"Performance test failed: {e}")
        print(f"\n❌ ERROR: Performance test failed - {e}")
        return None


if __name__ == "__main__":
    main() 