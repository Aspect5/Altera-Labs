import json
import time
import os
from datetime import datetime
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
import logging
from lean_verifier import LeanVerifier

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

@dataclass
class TestCase:
    """Represents a single test case for LLM performance evaluation."""
    name: str
    description: str
    proof_state: str
    expected_tactic: Optional[str] = None
    difficulty: str = "easy"  # easy, medium, hard
    category: str = "basic"  # basic, arithmetic, logic, advanced
    max_attempts: int = 5

@dataclass
class TestResult:
    """Represents the result of a single test case."""
    test_case: TestCase
    success: bool
    attempts_used: int
    total_time: float
    attempts: List[Dict[str, Any]]
    final_proof: str
    error_messages: List[str]
    llm_response_quality: Dict[str, Any]

@dataclass
class PerformanceReport:
    """Comprehensive performance report for LLM testing."""
    timestamp: str
    total_tests: int
    successful_tests: int
    failed_tests: int
    success_rate: float
    average_attempts: float
    average_time: float
    results_by_difficulty: Dict[str, Dict[str, Any]]
    results_by_category: Dict[str, Dict[str, Any]]
    common_errors: Dict[str, int]
    llm_quality_metrics: Dict[str, Any]
    test_results: List[TestResult]

class LLMPerformanceTester:
    """Comprehensive testing system for LLM proof-solving performance."""
    
    def __init__(self):
        self.lean_verifier = LeanVerifier(developer_mode=True)
        self.test_cases = self._load_test_cases()
        
    def _load_test_cases(self) -> List[TestCase]:
        """Load predefined test cases covering various proof scenarios."""
        return [
            # Basic arithmetic proofs
            TestCase(
                name="Simple Addition",
                description="Basic arithmetic: 1 + 1 = 2",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : 1 + 1 = 2 := by sorry""",
                expected_tactic="rfl",
                difficulty="easy",
                category="arithmetic"
            ),
            TestCase(
                name="Simple Multiplication",
                description="Basic arithmetic: 2 * 3 = 6",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : 2 * 3 = 6 := by sorry""",
                expected_tactic="rfl",
                difficulty="easy",
                category="arithmetic"
            ),
            TestCase(
                name="Zero Addition",
                description="Identity property: n + 0 = n",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n + 0 = n := by sorry""",
                expected_tactic="intro n; exact Nat.add_zero n",
                difficulty="medium",
                category="arithmetic"
            ),
            
            # Commutativity proofs
            TestCase(
                name="Addition Commutativity",
                description="Commutative property: a + b = b + a",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (a b : ℕ), a + b = b + a := by sorry""",
                expected_tactic="intro a b; exact Nat.add_comm a b",
                difficulty="medium",
                category="arithmetic"
            ),
            TestCase(
                name="Multiplication Commutativity",
                description="Commutative property: a * b = b * a",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (a b : ℕ), a * b = b * a := by sorry""",
                expected_tactic="intro a b; exact Nat.mul_comm a b",
                difficulty="medium",
                category="arithmetic"
            ),
            
            # Associativity proofs
            TestCase(
                name="Addition Associativity",
                description="Associative property: (a + b) + c = a + (b + c)",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (a b c : ℕ), (a + b) + c = a + (b + c) := by sorry""",
                expected_tactic="intro a b c; exact Nat.add_assoc a b c",
                difficulty="medium",
                category="arithmetic"
            ),
            
            # Inequality proofs
            TestCase(
                name="Zero Less Equal",
                description="Basic inequality: 0 ≤ n for all n",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), 0 ≤ n := by sorry""",
                expected_tactic="intro n; exact Nat.zero_le n",
                difficulty="medium",
                category="inequality"
            ),
            TestCase(
                name="Reflexive Less Equal",
                description="Reflexive property: n ≤ n for all n",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n ≤ n := by sorry""",
                expected_tactic="intro n; exact Nat.le_refl n",
                difficulty="medium",
                category="inequality"
            ),
            
            # Logic proofs
            TestCase(
                name="True Implication",
                description="Basic logic: True → True",
                proof_state="""import Mathlib.Logic.Basic
theorem test : True → True := by sorry""",
                expected_tactic="intro h; exact h",
                difficulty="easy",
                category="logic"
            ),
            TestCase(
                name="False Elimination",
                description="Ex falso: False → P for any P",
                proof_state="""import Mathlib.Logic.Basic
theorem test : ∀ (P : Prop), False → P := by sorry""",
                expected_tactic="intro P h; contradiction",
                difficulty="medium",
                category="logic"
            ),
            
            # Advanced proofs
            TestCase(
                name="Successor Greater",
                description="Advanced: n + 1 > n for all n",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (n : ℕ), n + 1 > n := by sorry""",
                expected_tactic="intro n; exact Nat.lt_succ_self n",
                difficulty="hard",
                category="advanced"
            ),
            TestCase(
                name="Distributive Law",
                description="Distributive property: a * (b + c) = a * b + a * c",
                proof_state="""import Mathlib.Data.Nat.Basic
theorem test : ∀ (a b c : ℕ), a * (b + c) = a * b + a * c := by sorry""",
                expected_tactic="intro a b c; exact Nat.mul_add a b c",
                difficulty="hard",
                category="advanced"
            )
        ]
    
    def _analyze_llm_response_quality(self, attempts: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze the quality of LLM responses."""
        quality_metrics = {
            "valid_tactics": 0,
            "invalid_tactics": 0,
            "markdown_formatted": 0,
            "natural_language": 0,
            "empty_responses": 0,
            "average_response_length": 0,
            "common_patterns": {}
        }
        
        total_length = 0
        pattern_counts = {}
        
        for attempt in attempts:
            tactic = attempt.get("tactic", "")
            total_length += len(tactic)
            
            # Check for valid Lean tactics
            if self._is_valid_lean_tactic(tactic):
                quality_metrics["valid_tactics"] += 1
            else:
                quality_metrics["invalid_tactics"] += 1
                
                # Categorize invalid responses
                if tactic.startswith("```lean") or tactic.endswith("```"):
                    quality_metrics["markdown_formatted"] += 1
                elif any(word in tactic.lower() for word in ["interesting", "think", "consider", "remember", "let's"]):
                    quality_metrics["natural_language"] += 1
                elif not tactic.strip():
                    quality_metrics["empty_responses"] += 1
                    
            # Track common patterns
            if tactic in pattern_counts:
                pattern_counts[tactic] += 1
            else:
                pattern_counts[tactic] = 1
        
        quality_metrics["average_response_length"] = total_length / len(attempts) if attempts else 0
        quality_metrics["common_patterns"] = dict(sorted(pattern_counts.items(), key=lambda x: x[1], reverse=True)[:5])
        
        return quality_metrics
    
    def _is_valid_lean_tactic(self, tactic: str) -> bool:
        """Check if a tactic is a valid Lean tactic."""
        # Remove markdown formatting
        clean_tactic = tactic.replace("```lean", "").replace("```", "").strip()
        
        # Basic Lean tactics
        valid_tactics = [
            "rfl", "simp", "intro", "exact", "apply", "rw", "cases", "induction",
            "contradiction", "assumption", "constructor", "split", "left", "right",
            "exists", "use", "revert", "generalize", "clear", "rename", "unfold",
            "fold", "delta", "beta", "zeta", "eta", "iota", "congr", "ext",
            "funext", "propext", "cc", "linarith", "omega", "ring", "norm_num"
        ]
        
        # Check if it starts with a valid tactic
        for valid_tactic in valid_tactics:
            if clean_tactic.startswith(valid_tactic):
                return True
                
        # Check for exact with theorem names
        if clean_tactic.startswith("exact ") and any(name in clean_tactic for name in ["Nat.", "Int.", "Bool."]):
            return True
            
        return False
    
    def run_single_test(self, test_case: TestCase) -> TestResult:
        """Run a single test case and return detailed results."""
        logger.info(f"Running test: {test_case.name}")
        
        start_time = time.time()
        
        # Run auto-solve
        result = self.lean_verifier.auto_solve_proof(
            test_case.proof_state, 
            max_attempts=test_case.max_attempts
        )
        
        total_time = time.time() - start_time
        
        # Analyze LLM response quality
        llm_quality = self._analyze_llm_response_quality(result.get("attempts", []))
        
        # Extract error messages
        error_messages = []
        for attempt in result.get("attempts", []):
            if attempt.get("error"):
                error_messages.append(attempt["error"])
        
        return TestResult(
            test_case=test_case,
            success=result.get("solved", False),
            attempts_used=result.get("attempts_used", 0),
            total_time=total_time,
            attempts=result.get("attempts", []),
            final_proof=result.get("final_proof", ""),
            error_messages=error_messages,
            llm_response_quality=llm_quality
        )
    
    def run_full_test_suite(self) -> PerformanceReport:
        """Run the complete test suite and generate a comprehensive report."""
        logger.info("Starting comprehensive LLM performance test suite")
        
        test_results = []
        total_tests = len(self.test_cases)
        successful_tests = 0
        total_attempts = 0
        total_time = 0
        
        # Run all test cases
        for test_case in self.test_cases:
            try:
                result = self.run_single_test(test_case)
                test_results.append(result)
                
                if result.success:
                    successful_tests += 1
                
                total_attempts += result.attempts_used
                total_time += result.total_time
                
                logger.info(f"Test '{test_case.name}': {'SUCCESS' if result.success else 'FAILED'} "
                          f"({result.attempts_used} attempts, {result.total_time:.2f}s)")
                
            except Exception as e:
                logger.error(f"Error running test '{test_case.name}': {e}")
                # Create a failed result
                failed_result = TestResult(
                    test_case=test_case,
                    success=False,
                    attempts_used=0,
                    total_time=0,
                    attempts=[],
                    final_proof=test_case.proof_state,
                    error_messages=[str(e)],
                    llm_response_quality={}
                )
                test_results.append(failed_result)
        
        # Calculate metrics
        success_rate = (successful_tests / total_tests) * 100 if total_tests > 0 else 0
        average_attempts = total_attempts / total_tests if total_tests > 0 else 0
        average_time = total_time / total_tests if total_tests > 0 else 0
        
        # Group results by difficulty
        results_by_difficulty = self._group_results_by_difficulty(test_results)
        
        # Group results by category
        results_by_category = self._group_results_by_category(test_results)
        
        # Analyze common errors
        common_errors = self._analyze_common_errors(test_results)
        
        # Overall LLM quality metrics
        llm_quality_metrics = self._calculate_overall_llm_quality(test_results)
        
        return PerformanceReport(
            timestamp=datetime.now().isoformat(),
            total_tests=total_tests,
            successful_tests=successful_tests,
            failed_tests=total_tests - successful_tests,
            success_rate=success_rate,
            average_attempts=average_attempts,
            average_time=average_time,
            results_by_difficulty=results_by_difficulty,
            results_by_category=results_by_category,
            common_errors=common_errors,
            llm_quality_metrics=llm_quality_metrics,
            test_results=test_results
        )
    
    def _group_results_by_difficulty(self, results: List[TestResult]) -> Dict[str, Dict[str, Any]]:
        """Group test results by difficulty level."""
        grouped = {"easy": [], "medium": [], "hard": []}
        
        for result in results:
            difficulty = result.test_case.difficulty
            if difficulty in grouped:
                grouped[difficulty].append(result)
        
        # Calculate metrics for each difficulty
        difficulty_metrics = {}
        for difficulty, difficulty_results in grouped.items():
            if difficulty_results:
                success_count = sum(1 for r in difficulty_results if r.success)
                total_attempts = sum(r.attempts_used for r in difficulty_results)
                total_time = sum(r.total_time for r in difficulty_results)
                
                difficulty_metrics[difficulty] = {
                    "count": len(difficulty_results),
                    "success_count": success_count,
                    "success_rate": (success_count / len(difficulty_results)) * 100,
                    "average_attempts": total_attempts / len(difficulty_results),
                    "average_time": total_time / len(difficulty_results)
                }
            else:
                difficulty_metrics[difficulty] = {
                    "count": 0,
                    "success_count": 0,
                    "success_rate": 0,
                    "average_attempts": 0,
                    "average_time": 0
                }
        
        return difficulty_metrics
    
    def _group_results_by_category(self, results: List[TestResult]) -> Dict[str, Dict[str, Any]]:
        """Group test results by category."""
        grouped = {}
        
        for result in results:
            category = result.test_case.category
            if category not in grouped:
                grouped[category] = []
            grouped[category].append(result)
        
        # Calculate metrics for each category
        category_metrics = {}
        for category, category_results in grouped.items():
            success_count = sum(1 for r in category_results if r.success)
            total_attempts = sum(r.attempts_used for r in category_results)
            total_time = sum(r.total_time for r in category_results)
            
            category_metrics[category] = {
                "count": len(category_results),
                "success_count": success_count,
                "success_rate": (success_count / len(category_results)) * 100,
                "average_attempts": total_attempts / len(category_results),
                "average_time": total_time / len(category_results)
            }
        
        return category_metrics
    
    def _analyze_common_errors(self, results: List[TestResult]) -> Dict[str, int]:
        """Analyze common error patterns across all tests."""
        error_counts = {}
        
        for result in results:
            for error in result.error_messages:
                # Simplify error messages for grouping
                simplified_error = error[:100] if len(error) > 100 else error
                if simplified_error in error_counts:
                    error_counts[simplified_error] += 1
                else:
                    error_counts[simplified_error] = 1
        
        return dict(sorted(error_counts.items(), key=lambda x: x[1], reverse=True)[:10])
    
    def _calculate_overall_llm_quality(self, results: List[TestResult]) -> Dict[str, Any]:
        """Calculate overall LLM response quality metrics."""
        total_valid = 0
        total_invalid = 0
        total_markdown = 0
        total_natural_language = 0
        total_empty = 0
        total_responses = 0
        total_length = 0
        
        for result in results:
            quality = result.llm_response_quality
            total_valid += quality.get("valid_tactics", 0)
            total_invalid += quality.get("invalid_tactics", 0)
            total_markdown += quality.get("markdown_formatted", 0)
            total_natural_language += quality.get("natural_language", 0)
            total_empty += quality.get("empty_responses", 0)
            total_responses += quality.get("valid_tactics", 0) + quality.get("invalid_tactics", 0)
            total_length += quality.get("average_response_length", 0) * (quality.get("valid_tactics", 0) + quality.get("invalid_tactics", 0))
        
        return {
            "total_responses": total_responses,
            "valid_tactics": total_valid,
            "invalid_tactics": total_invalid,
            "valid_tactic_rate": (total_valid / total_responses * 100) if total_responses > 0 else 0,
            "markdown_formatted": total_markdown,
            "natural_language_responses": total_natural_language,
            "empty_responses": total_empty,
            "average_response_length": total_length / total_responses if total_responses > 0 else 0
        }
    
    def generate_markdown_report(self, report: PerformanceReport) -> str:
        """Generate a comprehensive markdown report."""
        markdown = f"""# LLM Proof-Solving Performance Report

**Generated:** {report.timestamp}  
**Total Tests:** {report.total_tests}  
**Success Rate:** {report.success_rate:.1f}%  
**Average Attempts:** {report.average_attempts:.1f}  
**Average Time:** {report.average_time:.2f}s

## Executive Summary

- **Successful Tests:** {report.successful_tests}/{report.total_tests}
- **Failed Tests:** {report.failed_tests}/{report.total_tests}
- **Overall Success Rate:** {report.success_rate:.1f}%

## Performance by Difficulty

| Difficulty | Count | Success Rate | Avg Attempts | Avg Time |
|------------|-------|--------------|--------------|----------|
"""
        
        for difficulty, metrics in report.results_by_difficulty.items():
            markdown += f"| {difficulty.title()} | {metrics['count']} | {metrics['success_rate']:.1f}% | {metrics['average_attempts']:.1f} | {metrics['average_time']:.2f}s |\n"
        
        markdown += """
## Performance by Category

| Category | Count | Success Rate | Avg Attempts | Avg Time |
|----------|-------|--------------|--------------|----------|
"""
        
        for category, metrics in report.results_by_category.items():
            markdown += f"| {category.title()} | {metrics['count']} | {metrics['success_rate']:.1f}% | {metrics['average_attempts']:.1f} | {metrics['average_time']:.2f}s |\n"
        
        markdown += f"""
## LLM Response Quality Analysis

- **Total Responses:** {report.llm_quality_metrics['total_responses']}
- **Valid Tactics:** {report.llm_quality_metrics['valid_tactics']} ({report.llm_quality_metrics['valid_tactic_rate']:.1f}%)
- **Invalid Tactics:** {report.llm_quality_metrics['invalid_tactics']}
- **Markdown Formatted:** {report.llm_quality_metrics['markdown_formatted']}
- **Natural Language Responses:** {report.llm_quality_metrics['natural_language_responses']}
- **Empty Responses:** {report.llm_quality_metrics['empty_responses']}
- **Average Response Length:** {report.llm_quality_metrics['average_response_length']:.1f} characters

## Common Errors

"""
        
        for error, count in report.common_errors.items():
            markdown += f"- **{count} occurrences:** {error}\n"
        
        markdown += """
## Detailed Test Results

"""
        
        for result in report.test_results:
            status = "✅ SUCCESS" if result.success else "❌ FAILED"
            markdown += f"""
### {result.test_case.name} - {status}

**Description:** {result.test_case.description}  
**Difficulty:** {result.test_case.difficulty.title()}  
**Category:** {result.test_case.category.title()}  
**Attempts Used:** {result.attempts_used}/{result.test_case.max_attempts}  
**Time:** {result.total_time:.2f}s

**Initial Proof State:**
```lean
{result.test_case.proof_state}
```

**Final Proof State:**
```lean
{result.final_proof}
```

**Attempts:**
"""
            
            for i, attempt in enumerate(result.attempts, 1):
                tactic = attempt.get("tactic", "")
                success = "✅" if attempt.get("success", False) else "❌"
                error = attempt.get("error", "")
                
                markdown += f"{i}. {success} `{tactic}`"
                if error:
                    markdown += f" - Error: {error}"
                markdown += "\n"
            
            markdown += f"""
**LLM Quality Metrics:**
- Valid Tactics: {result.llm_response_quality.get('valid_tactics', 0)}
- Invalid Tactics: {result.llm_response_quality.get('invalid_tactics', 0)}
- Markdown Formatted: {result.llm_response_quality.get('markdown_formatted', 0)}
- Natural Language: {result.llm_response_quality.get('natural_language', 0)}

---
"""
        
        return markdown
    
    def save_report(self, report: PerformanceReport, filename: str = None) -> str:
        """Save the performance report to a file."""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"llm_performance_report_{timestamp}.md"
        
        markdown_content = self.generate_markdown_report(report)
        
        # Save to reports directory
        reports_dir = os.path.join(os.path.dirname(__file__), "reports")
        os.makedirs(reports_dir, exist_ok=True)
        
        filepath = os.path.join(reports_dir, filename)
        with open(filepath, 'w') as f:
            f.write(markdown_content)
        
        logger.info(f"Performance report saved to: {filepath}")
        return filepath

# Global instance for easy access
performance_tester = LLMPerformanceTester() 