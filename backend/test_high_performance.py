#!/usr/bin/env python3
"""
High-Performance Test Script for Proving Agent

This script tests the aggressive performance optimizations implemented in the Proving Agent,
including parallel processing, intelligent caching, and optimized execution patterns.
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

class HighPerformanceTester:
    """Test suite for measuring aggressive performance improvements."""
    
    def __init__(self):
        self.verifier = LeanVerifier(developer_mode=True)
        self.test_cases = self._load_high_performance_test_cases()
        self.results = []
        
    def _load_high_performance_test_cases(self) -> List[Dict[str, Any]]:
        """Load test cases designed for high-performance testing."""
        return [
            {
                "name": "Simple Addition (Optimized)",
                "proof_state": "theorem test : 1 + 1 = 2 := by sorry",
                "expected_tactic": "rfl",
                "category": "arithmetic",
                "difficulty": "easy",
                "optimization_target": "direct_library_call"
            },
            {
                "name": "Zero Addition (Optimized)",
                "proof_state": "theorem test : ∀ n : ℕ, n + 0 = n := by sorry",
                "expected_tactic": "intro n; exact Nat.add_zero n",
                "category": "arithmetic",
                "difficulty": "medium",
                "optimization_target": "identity_optimization"
            },
            {
                "name": "Addition Commutativity (Optimized)",
                "proof_state": "theorem test : ∀ a b : ℕ, a + b = b + a := by sorry",
                "expected_tactic": "intro a b; exact Nat.add_comm a b",
                "category": "arithmetic",
                "difficulty": "medium",
                "optimization_target": "commutativity_optimization"
            },
            {
                "name": "Addition Associativity (Optimized)",
                "proof_state": "theorem test : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := by sorry",
                "expected_tactic": "intro a b c; exact Nat.add_assoc a b c",
                "category": "arithmetic",
                "difficulty": "medium",
                "optimization_target": "associativity_optimization"
            },
            {
                "name": "Multiplication Commutativity (Optimized)",
                "proof_state": "theorem test : ∀ a b : ℕ, a * b = b * a := by sorry",
                "expected_tactic": "intro a b; exact Nat.mul_comm a b",
                "category": "arithmetic",
                "difficulty": "medium",
                "optimization_target": "commutativity_optimization"
            }
        ]
    
    def run_baseline_performance_test(self) -> Dict[str, Any]:
        """Run baseline test without optimizations."""
        logger.info("Running baseline performance test (no optimizations)...")
        
        # Disable all optimizations
        self.verifier.cache_enabled = False
        self.verifier.parallel_processing = False
        self.verifier.aggressive_caching = False
        self.verifier.environment_optimized = False
        
        return self._run_high_performance_test_suite("baseline")
    
    def run_optimized_performance_test(self) -> Dict[str, Any]:
        """Run test with all aggressive optimizations enabled."""
        logger.info("Running optimized performance test (all optimizations)...")
        
        # Enable all optimizations
        self.verifier.cache_enabled = True
        self.verifier.parallel_processing = True
        self.verifier.aggressive_caching = True
        self.verifier.environment_optimized = False  # Will be optimized during first test
        
        return self._run_high_performance_test_suite("optimized")
    
    def run_parallel_performance_test(self) -> Dict[str, Any]:
        """Run test specifically for parallel processing performance."""
        logger.info("Running parallel processing performance test...")
        
        # Enable only parallel processing
        self.verifier.cache_enabled = False
        self.verifier.parallel_processing = True
        self.verifier.aggressive_caching = False
        self.verifier.environment_optimized = False
        
        return self._run_high_performance_test_suite("parallel_only")
    
    def run_cache_performance_test(self) -> Dict[str, Any]:
        """Run test specifically for cache performance."""
        logger.info("Running cache performance test...")
        
        # Enable only caching
        self.verifier.cache_enabled = True
        self.verifier.parallel_processing = False
        self.verifier.aggressive_caching = True
        self.verifier.environment_optimized = False
        
        # Clear cache first
        proof_cache.clear_cache()
        
        # Run tests twice to measure cache effectiveness
        first_run = self._run_high_performance_test_suite("cache_first_run")
        second_run = self._run_high_performance_test_suite("cache_second_run")
        
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
    
    def _run_high_performance_test_suite(self, test_name: str) -> Dict[str, Any]:
        """Run a high-performance test suite."""
        results = []
        total_time = 0
        successful_tests = 0
        parallel_successes = 0
        
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
                    if result.get("parallel_execution", False):
                        parallel_successes += 1
                
                test_result = {
                    "test_case": test_case["name"],
                    "success": result["success"],
                    "time": test_time,
                    "attempts": len(result.get("attempts", [])),
                    "tactic": result.get("tactic", ""),
                    "llm_time": result.get("llm_time", 0),
                    "verify_time": result.get("verify_time", 0),
                    "parallel_execution": result.get("parallel_execution", False),
                    "strategy": result.get("strategy", ""),
                    "optimization_target": test_case.get("optimization_target", "")
                }
                
                results.append(test_result)
                
                logger.info(f"  ✅ {test_case['name']}: {'SUCCESS' if result['success'] else 'FAILED'} in {test_time:.2f}s")
                if result.get("parallel_execution", False):
                    logger.info(f"  🚀 Parallel execution successful!")
                
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
            "parallel_successes": parallel_successes,
            "success_rate": (successful_tests / len(self.test_cases)) * 100,
            "parallel_success_rate": (parallel_successes / len(self.test_cases)) * 100,
            "total_time": total_time,
            "average_time": total_time / len(self.test_cases),
            "results": results,
            "performance_stats": self.verifier.performance_stats.copy()
        }
    
    def run_comprehensive_high_performance_test(self) -> Dict[str, Any]:
        """Run comprehensive high-performance test."""
        logger.info("Starting comprehensive high-performance test...")
        
        start_time = time.time()
        
        # Get initial stats
        initial_cache_stats = proof_cache.get_cache_stats()
        initial_env_stats = lean_env_manager.get_environment_status()
        initial_perf_stats = self.verifier.performance_stats.copy()
        
        # Run baseline test
        baseline_results = self.run_baseline_performance_test()
        
        # Run optimized test
        optimized_results = self.run_optimized_performance_test()
        
        # Run parallel test
        parallel_results = self.run_parallel_performance_test()
        
        # Run cache test
        cache_results = self.run_cache_performance_test()
        
        # Get final stats
        final_cache_stats = proof_cache.get_cache_stats()
        final_env_stats = lean_env_manager.get_environment_status()
        final_perf_stats = self.verifier.performance_stats.copy()
        
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
            "parallel_results": parallel_results,
            "cache_results": cache_results,
            "performance_improvements": {
                "time_improvement_percent": time_improvement,
                "baseline_avg_time": baseline_avg_time,
                "optimized_avg_time": optimized_avg_time,
                "time_saved_per_test": baseline_avg_time - optimized_avg_time,
                "parallel_success_rate": optimized_results["parallel_success_rate"],
                "cache_hit_rate": cache_results["cache_effectiveness"]["hit_rate"]
            },
            "cache_analysis": {
                "initial_stats": initial_cache_stats,
                "final_stats": final_cache_stats,
                "cache_growth": final_cache_stats["total_entries"] - initial_cache_stats["total_entries"]
            },
            "environment_analysis": {
                "initial_stats": initial_env_stats,
                "final_stats": final_env_stats
            },
            "performance_stats_analysis": {
                "initial_stats": initial_perf_stats,
                "final_stats": final_perf_stats,
                "improvements": {
                    "total_verifications": final_perf_stats["total_verifications"] - initial_perf_stats["total_verifications"],
                    "cache_hits": final_perf_stats["cache_hits"] - initial_perf_stats["cache_hits"],
                    "parallel_executions": final_perf_stats["parallel_executions"] - initial_perf_stats["parallel_executions"],
                    "avg_verification_time": final_perf_stats["avg_verification_time"]
                }
            }
        }
        
        return report
    
    def save_report(self, report: Dict[str, Any], filename: str = None) -> str:
        """Save test report to file."""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"high_performance_test_report_{timestamp}.json"
        
        with open(filename, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        logger.info(f"High-performance test report saved to {filename}")
        return filename
    
    def print_summary(self, report: Dict[str, Any]):
        """Print a summary of the high-performance test results."""
        print("\n" + "="*80)
        print("HIGH-PERFORMANCE PROVING AGENT TEST RESULTS")
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
        
        print(f"\n🚀 PARALLEL PROCESSING:")
        print(f"  Parallel Success Rate: {improvements['parallel_success_rate']:.1f}%")
        print(f"  Parallel Executions: {optimized['parallel_successes']}/{optimized['total_tests']}")
        
        print(f"\n💾 CACHE EFFECTIVENESS:")
        print(f"  Cache Hit Rate: {improvements['cache_hit_rate']:.1f}%")
        cache_results = report["cache_results"]
        cache_stats = cache_results["cache_stats"]
        print(f"  Total Cache Requests: {cache_stats.get('total_requests', 0)}")
        print(f"  Cache Hits: {cache_stats.get('hits', 0)}")
        print(f"  Cache Misses: {cache_stats.get('misses', 0)}")
        print(f"  Cache Size: {cache_stats.get('cache_size_mb', 0):.2f}MB")
        
        print(f"\n📈 SUCCESS RATES:")
        print(f"  Baseline Success Rate: {baseline['success_rate']:.1f}%")
        print(f"  Optimized Success Rate: {optimized['success_rate']:.1f}%")
        
        # Performance stats
        perf_stats = report["performance_stats_analysis"]["final_stats"]
        print(f"\n🔧 PERFORMANCE STATISTICS:")
        print(f"  Total Verifications: {perf_stats['total_verifications']}")
        print(f"  Cache Hits: {perf_stats['cache_hits']}")
        print(f"  Parallel Executions: {perf_stats['parallel_executions']}")
        print(f"  Average Verification Time: {perf_stats['avg_verification_time']:.3f}s")
        
        print("\n" + "="*80)


def main():
    """Run the high-performance test suite."""
    print("🚀 Starting High-Performance Proving Agent Test Suite")
    print("="*80)
    
    tester = HighPerformanceTester()
    
    try:
        # Run comprehensive test
        report = tester.run_comprehensive_high_performance_test()
        
        # Print summary
        tester.print_summary(report)
        
        # Save detailed report
        filename = tester.save_report(report)
        print(f"\n📄 Detailed report saved to: {filename}")
        
        # Determine if improvements meet aggressive targets
        improvements = report["performance_improvements"]
        time_improvement = improvements["time_improvement_percent"]
        parallel_success_rate = improvements["parallel_success_rate"]
        cache_hit_rate = improvements["cache_hit_rate"]
        
        print(f"\n🎯 PERFORMANCE TARGETS:")
        print(f"  Time Improvement Target: 70% (Achieved: {time_improvement:.1f}%)")
        print(f"  Parallel Success Target: 60% (Achieved: {parallel_success_rate:.1f}%)")
        print(f"  Cache Hit Rate Target: 80% (Achieved: {cache_hit_rate:.1f}%)")
        
        if time_improvement >= 70 and parallel_success_rate >= 60 and cache_hit_rate >= 80:
            print(f"\n✅ EXCELLENT: All aggressive performance targets achieved!")
        elif time_improvement >= 50:
            print(f"\n✅ GOOD: Significant performance improvement achieved ({time_improvement:.1f}%)")
        else:
            print(f"\n⚠️  NEEDS IMPROVEMENT: Performance improvement below target ({time_improvement:.1f}%)")
        
        return report
        
    except Exception as e:
        logger.error(f"High-performance test failed: {e}")
        print(f"\n❌ ERROR: High-performance test failed - {e}")
        return None


if __name__ == "__main__":
    main() 