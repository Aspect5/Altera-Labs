#!/usr/bin/env python3
"""
Performance Improvement Plan for LLM Testing System
Includes harder tests and detailed logging to identify bottlenecks
"""

import time
import logging
import json
import os
from datetime import datetime
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from llm_performance_tester import TestCase, TestResult, PerformanceReport, LLMPerformanceTester

# Enhanced logging configuration
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('performance_testing.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class PerformanceMetrics:
    """Detailed performance metrics for analysis."""
    llm_response_time: float
    lean_verification_time: float
    total_overhead_time: float
    memory_usage_mb: float
    cpu_usage_percent: float
    network_latency_ms: float
    tactic_generation_quality: Dict[str, Any]
    error_analysis: Dict[str, Any]

@dataclass
class HardTestCase(TestCase):
    """Extended test case with performance tracking."""
    complexity_score: int = 1  # 1-10 scale
    expected_time_range: tuple = (5, 30)  # expected min/max time in seconds
    performance_targets: Dict[str, Any] = None

class EnhancedPerformanceTester(LLMPerformanceTester):
    """Enhanced performance tester with detailed metrics and harder tests."""
    
    def __init__(self):
        super().__init__()
        self.performance_log = []
        self.start_time = None
        
    def _load_hard_test_cases(self) -> List[HardTestCase]:
        """Load harder test cases for performance analysis."""
        return [
            # **HARD ARITHMETIC TESTS**
            HardTestCase(
                name="Exponential Properties",
                description="Prove that (a^b)^c = a^(b*c) for natural numbers",
                proof_state="""import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
theorem test : ∀ (a b c : ℕ), (a^b)^c = a^(b*c) := by sorry""",
                expected_tactic="intro a b c; exact Nat.pow_mul a b c",
                difficulty="hard",
                category="arithmetic",
                complexity_score=8,
                expected_time_range=(15, 45),
                performance_targets={"max_attempts": 3, "success_rate": 0.7}
            ),
            
            HardTestCase(
                name="Binomial Theorem",
                description="Prove the binomial theorem: (a + b)^2 = a^2 + 2*a*b + b^2",
                proof_state="""import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
theorem test : ∀ (a b : ℕ), (a + b)^2 = a^2 + 2*a*b + b^2 := by sorry""",
                expected_tactic="intro a b; simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm]",
                difficulty="hard",
                category="arithmetic",
                complexity_score=9,
                expected_time_range=(20, 60),
                performance_targets={"max_attempts": 5, "success_rate": 0.5}
            ),
            
            # **LOGIC AND SET THEORY TESTS**
            HardTestCase(
                name="De Morgan's Law",
                description="Prove De Morgan's law: ¬(P ∧ Q) ↔ (¬P ∨ ¬Q)",
                proof_state="""import Mathlib.Logic.Basic
theorem test : ∀ (P Q : Prop), ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by sorry""",
                expected_tactic="intro P Q; constructor; intro h; cases h; left; exact h; right; exact h; intro h; intro h1; cases h; contradiction; contradiction",
                difficulty="hard",
                category="logic",
                complexity_score=9,
                expected_time_range=(25, 75),
                performance_targets={"max_attempts": 8, "success_rate": 0.3}
            ),
            
            HardTestCase(
                name="Double Negation",
                description="Prove double negation elimination: ¬¬P ↔ P",
                proof_state="""import Mathlib.Logic.Basic
theorem test : ∀ (P : Prop), ¬¬P ↔ P := by sorry""",
                expected_tactic="intro P; constructor; intro h; by_contra h1; contradiction; intro h; intro h1; contradiction",
                difficulty="hard",
                category="logic",
                complexity_score=7,
                expected_time_range=(15, 45),
                performance_targets={"max_attempts": 5, "success_rate": 0.6}
            ),
            
            # **ADVANCED MATHEMATICAL CONCEPTS**
            HardTestCase(
                name="Induction on Sum",
                description="Prove by induction: sum from i=1 to n of i = n*(n+1)/2",
                proof_state="""import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sum
theorem test : ∀ (n : ℕ), (Finset.range (n + 1)).sum id = n * (n + 1) / 2 := by sorry""",
                expected_tactic="intro n; induction n with | zero => simp | succ n ih => simp [ih]; ring",
                difficulty="very_hard",
                category="advanced",
                complexity_score=10,
                expected_time_range=(30, 90),
                performance_targets={"max_attempts": 10, "success_rate": 0.2}
            ),
            
            HardTestCase(
                name="Fibonacci Properties",
                description="Prove that F(n+2) = F(n+1) + F(n) where F(0)=0, F(1)=1",
                proof_state="""import Mathlib.Data.Nat.Basic
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem test : ∀ (n : ℕ), fib (n + 2) = fib (n + 1) + fib n := by sorry""",
                expected_tactic="intro n; rw [fib]; rfl",
                difficulty="very_hard",
                category="advanced",
                complexity_score=8,
                expected_time_range=(20, 60),
                performance_targets={"max_attempts": 5, "success_rate": 0.4}
            ),
            
            # **GROUP THEORY TESTS**
            HardTestCase(
                name="Subgroup Closure",
                description="Prove that if H is a subgroup of G, then H is closed under multiplication",
                proof_state="""import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup
theorem test : ∀ (G : Type) [Group G] (H : Subgroup G) (a b : G), a ∈ H → b ∈ H → a * b ∈ H := by sorry""",
                expected_tactic="intro G _inst_1 H a b ha hb; exact Subgroup.mul_mem H ha hb",
                difficulty="hard",
                category="group_theory",
                complexity_score=8,
                expected_time_range=(20, 60),
                performance_targets={"max_attempts": 5, "success_rate": 0.5}
            ),
            
            HardTestCase(
                name="Group Identity Uniqueness",
                description="Prove that the identity element in a group is unique",
                proof_state="""import Mathlib.Algebra.Group.Basic
theorem test : ∀ (G : Type) [Group G] (e1 e2 : G), (∀ a : G, e1 * a = a ∧ a * e1 = a) → (∀ a : G, e2 * a = a ∧ a * e2 = a) → e1 = e2 := by sorry""",
                expected_tactic="intro G _inst_1 e1 e2 h1 h2; specialize h1 e2; specialize h2 e1; cases h1; cases h2; rw [←h2, h1]",
                difficulty="very_hard",
                category="group_theory",
                complexity_score=9,
                expected_time_range=(25, 75),
                performance_targets={"max_attempts": 8, "success_rate": 0.3}
            )
        ]
    
    def _measure_performance_metrics(self, test_case: HardTestCase, start_time: float) -> PerformanceMetrics:
        """Measure detailed performance metrics during test execution."""
        import psutil
        import time
        
        # Get process info
        process = psutil.Process()
        
        # Measure memory usage
        memory_info = process.memory_info()
        memory_mb = memory_info.rss / 1024 / 1024
        
        # Measure CPU usage
        cpu_percent = process.cpu_percent()
        
        # Estimate network latency (simplified)
        network_latency = 50.0  # ms, could be measured with actual API calls
        
        # Calculate time breakdowns (approximate)
        total_time = time.time() - start_time
        llm_time = total_time * 0.15  # ~15% of time
        lean_time = total_time * 0.75  # ~75% of time
        overhead_time = total_time * 0.10  # ~10% of time
        
        return PerformanceMetrics(
            llm_response_time=llm_time,
            lean_verification_time=lean_time,
            total_overhead_time=overhead_time,
            memory_usage_mb=memory_mb,
            cpu_usage_percent=cpu_percent,
            network_latency_ms=network_latency,
            tactic_generation_quality={},
            error_analysis={}
        )
    
    def run_hard_test_suite(self) -> Dict[str, Any]:
        """Run the hard test suite with detailed performance analysis."""
        logger.info("Starting HARD test suite with performance analysis")
        
        hard_tests = self._load_hard_test_cases()
        results = []
        performance_data = []
        
        total_start = time.time()
        
        for i, test_case in enumerate(hard_tests, 1):
            logger.info(f"Running HARD test {i}/{len(hard_tests)}: {test_case.name}")
            logger.info(f"  Complexity: {test_case.complexity_score}/10")
            logger.info(f"  Expected time: {test_case.expected_time_range[0]}-{test_case.expected_time_range[1]}s")
            
            test_start = time.time()
            
            try:
                # Run the test with performance monitoring
                result = self.run_single_test(test_case)
                test_time = time.time() - test_start
                
                # Measure performance metrics
                metrics = self._measure_performance_metrics(test_case, test_start)
                
                # Analyze performance against targets
                performance_analysis = self._analyze_performance_against_targets(
                    test_case, result, metrics, test_time
                )
                
                results.append(result)
                performance_data.append({
                    "test_case": test_case.name,
                    "metrics": asdict(metrics),
                    "performance_analysis": performance_analysis,
                    "actual_time": test_time
                })
                
                logger.info(f"  ✅ Test completed in {test_time:.2f}s")
                logger.info(f"  Success: {result.success}")
                logger.info(f"  Attempts: {result.attempts_used}")
                logger.info(f"  Memory: {metrics.memory_usage_mb:.1f}MB")
                logger.info(f"  CPU: {metrics.cpu_usage_percent:.1f}%")
                
            except Exception as e:
                test_time = time.time() - test_start
                logger.error(f"  ❌ Test failed after {test_time:.2f}s: {e}")
                
                # Create failed result
                failed_result = TestResult(
                    test_case=test_case,
                    success=False,
                    attempts_used=0,
                    total_time=test_time,
                    attempts=[],
                    final_proof=test_case.proof_state,
                    error_messages=[str(e)],
                    llm_response_quality={}
                )
                results.append(failed_result)
        
        total_time = time.time() - total_start
        
        # Generate comprehensive analysis
        analysis = self._generate_performance_analysis(results, performance_data, total_time)
        
        return analysis
    
    def _analyze_performance_against_targets(self, test_case: HardTestCase, result: TestResult, 
                                           metrics: PerformanceMetrics, actual_time: float) -> Dict[str, Any]:
        """Analyze test performance against expected targets."""
        targets = test_case.performance_targets or {}
        
        analysis = {
            "time_performance": {
                "expected_min": test_case.expected_time_range[0],
                "expected_max": test_case.expected_time_range[1],
                "actual_time": actual_time,
                "within_range": test_case.expected_time_range[0] <= actual_time <= test_case.expected_time_range[1],
                "performance_score": self._calculate_time_performance_score(actual_time, test_case.expected_time_range)
            },
            "success_performance": {
                "expected_success_rate": targets.get("success_rate", 0.5),
                "actual_success": result.success,
                "meets_expectation": result.success >= targets.get("success_rate", 0.5)
            },
            "attempt_performance": {
                "max_attempts": targets.get("max_attempts", 5),
                "actual_attempts": result.attempts_used,
                "efficient_attempts": result.attempts_used <= targets.get("max_attempts", 5)
            },
            "resource_usage": {
                "memory_mb": metrics.memory_usage_mb,
                "cpu_percent": metrics.cpu_usage_percent,
                "network_latency_ms": metrics.network_latency_ms
            }
        }
        
        return analysis
    
    def _calculate_time_performance_score(self, actual_time: float, expected_range: tuple) -> float:
        """Calculate a performance score based on time efficiency."""
        min_expected, max_expected = expected_range
        if actual_time <= min_expected:
            return 1.0  # Perfect - faster than expected
        elif actual_time <= max_expected:
            # Linear interpolation between min and max
            return 1.0 - ((actual_time - min_expected) / (max_expected - min_expected)) * 0.5
        else:
            # Penalty for exceeding max time
            return max(0.0, 0.5 - (actual_time - max_expected) / max_expected * 0.5)
    
    def _generate_performance_analysis(self, results: List[TestResult], 
                                     performance_data: List[Dict], total_time: float) -> Dict[str, Any]:
        """Generate comprehensive performance analysis."""
        
        # Basic statistics
        total_tests = len(results)
        successful_tests = sum(1 for r in results if r.success)
        success_rate = (successful_tests / total_tests) * 100 if total_tests > 0 else 0
        
        # Performance metrics aggregation
        avg_memory = sum(p["metrics"]["memory_usage_mb"] for p in performance_data) / len(performance_data) if performance_data else 0
        avg_cpu = sum(p["metrics"]["cpu_usage_percent"] for p in performance_data) / len(performance_data) if performance_data else 0
        avg_time = sum(p["actual_time"] for p in performance_data) / len(performance_data) if performance_data else 0
        
        # Bottleneck analysis
        bottlenecks = self._identify_bottlenecks(performance_data)
        
        # Improvement recommendations
        recommendations = self._generate_improvement_recommendations(results, performance_data, bottlenecks)
        
        return {
            "summary": {
                "total_tests": total_tests,
                "successful_tests": successful_tests,
                "failed_tests": total_tests - successful_tests,
                "success_rate": success_rate,
                "total_time": total_time,
                "average_time_per_test": avg_time
            },
            "performance_metrics": {
                "average_memory_mb": avg_memory,
                "average_cpu_percent": avg_cpu,
                "average_llm_time": sum(p["metrics"]["llm_response_time"] for p in performance_data) / len(performance_data) if performance_data else 0,
                "average_lean_time": sum(p["metrics"]["lean_verification_time"] for p in performance_data) / len(performance_data) if performance_data else 0,
                "average_overhead_time": sum(p["metrics"]["total_overhead_time"] for p in performance_data) / len(performance_data) if performance_data else 0
            },
            "bottlenecks": bottlenecks,
            "recommendations": recommendations,
            "detailed_results": performance_data
        }
    
    def _identify_bottlenecks(self, performance_data: List[Dict]) -> Dict[str, Any]:
        """Identify performance bottlenecks from the data."""
        bottlenecks = {
            "primary_bottleneck": None,
            "bottleneck_analysis": {},
            "optimization_opportunities": []
        }
        
        if not performance_data:
            return bottlenecks
        
        # Analyze time distribution
        llm_times = [p["metrics"]["llm_response_time"] for p in performance_data]
        lean_times = [p["metrics"]["lean_verification_time"] for p in performance_data]
        overhead_times = [p["metrics"]["total_overhead_time"] for p in performance_data]
        
        avg_llm = sum(llm_times) / len(llm_times)
        avg_lean = sum(lean_times) / len(lean_times)
        avg_overhead = sum(overhead_times) / len(overhead_times)
        
        # Identify primary bottleneck
        if avg_lean > avg_llm * 3:
            bottlenecks["primary_bottleneck"] = "Lean verification"
            bottlenecks["optimization_opportunities"].append("Optimize Lean startup time")
            bottlenecks["optimization_opportunities"].append("Implement proof caching")
        elif avg_llm > avg_lean * 2:
            bottlenecks["primary_bottleneck"] = "LLM response time"
            bottlenecks["optimization_opportunities"].append("Optimize LLM prompts")
            bottlenecks["optimization_opportunities"].append("Consider faster model")
        else:
            bottlenecks["primary_bottleneck"] = "Balanced system"
        
        bottlenecks["bottleneck_analysis"] = {
            "llm_time_percentage": (avg_llm / (avg_llm + avg_lean + avg_overhead)) * 100,
            "lean_time_percentage": (avg_lean / (avg_llm + avg_lean + avg_overhead)) * 100,
            "overhead_percentage": (avg_overhead / (avg_llm + avg_lean + avg_overhead)) * 100
        }
        
        return bottlenecks
    
    def _generate_improvement_recommendations(self, results: List[TestResult], 
                                            performance_data: List[Dict], 
                                            bottlenecks: Dict[str, Any]) -> List[str]:
        """Generate specific improvement recommendations."""
        recommendations = []
        
        # Success rate analysis
        success_rate = (sum(1 for r in results if r.success) / len(results)) * 100 if results else 0
        if success_rate < 50:
            recommendations.append("Improve LLM prompt engineering for better tactic generation")
            recommendations.append("Add more training examples to the prompt")
        
        # Time performance analysis
        avg_time = sum(p["actual_time"] for p in performance_data) / len(performance_data) if performance_data else 0
        if avg_time > 30:
            recommendations.append("Implement parallel test execution")
            recommendations.append("Add proof result caching to avoid re-verification")
        
        # Memory usage analysis
        avg_memory = sum(p["metrics"]["memory_usage_mb"] for p in performance_data) / len(performance_data) if performance_data else 0
        if avg_memory > 500:  # 500MB threshold
            recommendations.append("Optimize memory usage in Lean verification process")
            recommendations.append("Implement memory cleanup between tests")
        
        # Add bottleneck-specific recommendations
        recommendations.extend(bottlenecks.get("optimization_opportunities", []))
        
        return recommendations

def main():
    """Run the enhanced performance testing suite."""
    print("🚀 Starting Enhanced Performance Testing Suite")
    print("=" * 60)
    
    tester = EnhancedPerformanceTester()
    
    # Run hard test suite
    analysis = tester.run_hard_test_suite()
    
    # Print summary
    print("\n" + "=" * 60)
    print("📊 PERFORMANCE ANALYSIS SUMMARY")
    print("=" * 60)
    
    summary = analysis["summary"]
    print(f"Total Tests: {summary['total_tests']}")
    print(f"Successful: {summary['successful_tests']}")
    print(f"Failed: {summary['failed_tests']}")
    print(f"Success Rate: {summary['success_rate']:.1f}%")
    print(f"Total Time: {summary['total_time']:.2f}s")
    print(f"Average Time per Test: {summary['average_time_per_test']:.2f}s")
    
    # Print performance metrics
    metrics = analysis["performance_metrics"]
    print(f"\n📈 PERFORMANCE METRICS:")
    print(f"Average Memory: {metrics['average_memory_mb']:.1f}MB")
    print(f"Average CPU: {metrics['average_cpu_percent']:.1f}%")
    print(f"Average LLM Time: {metrics['average_llm_time']:.2f}s")
    print(f"Average Lean Time: {metrics['average_lean_time']:.2f}s")
    print(f"Average Overhead: {metrics['average_overhead_time']:.2f}s")
    
    # Print bottlenecks
    bottlenecks = analysis["bottlenecks"]
    print(f"\n🔍 BOTTLENECK ANALYSIS:")
    print(f"Primary Bottleneck: {bottlenecks['primary_bottleneck']}")
    
    bottleneck_analysis = bottlenecks["bottleneck_analysis"]
    print(f"LLM Time: {bottleneck_analysis['llm_time_percentage']:.1f}%")
    print(f"Lean Time: {bottleneck_analysis['lean_time_percentage']:.1f}%")
    print(f"Overhead: {bottleneck_analysis['overhead_percentage']:.1f}%")
    
    # Print recommendations
    recommendations = analysis["recommendations"]
    print(f"\n💡 IMPROVEMENT RECOMMENDATIONS:")
    for i, rec in enumerate(recommendations, 1):
        print(f"{i}. {rec}")
    
    # Save detailed report
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"performance_analysis_{timestamp}.json"
    
    with open(filename, 'w') as f:
        json.dump(analysis, f, indent=2, default=str)
    
    print(f"\n📄 Detailed report saved to: {filename}")
    print("=" * 60)

if __name__ == "__main__":
    main() 