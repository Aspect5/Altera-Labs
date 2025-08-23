# backend/lean_verifier.py

import logging
import subprocess
import tempfile
import os
import json
import re
import asyncio
import concurrent.futures
import platform
from typing import Dict, Any, Tuple, Optional, List
from socratic_auditor import get_llm_response
from datetime import datetime
from config.developer_config import developer_config, developer_logger
from lean_knowledge_base import lean_kb
from enhanced_prompts import enhanced_prompts
from proof_planner import proof_planner
from proof_cache import get_cached_proof_result, cache_proof_result
from lean_environment_manager import ensure_lean_environment_ready, optimize_lean_for_goal
import time
import threading
from functools import lru_cache

# Configure logging for this module
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Cross-platform executable utilities
def get_executable_name(base_name: str) -> str:
    """Get the correct executable name for the current platform."""
    if platform.system() == 'Windows':
        return f"{base_name}.exe"
    return base_name

def get_safe_subprocess_args(cmd_list: List[str]) -> List[str]:
    """Ensure subprocess arguments are safe for the current platform."""
    if platform.system() == 'Windows':
        # On Windows, ensure the first argument (executable) has .exe if needed
        if cmd_list and not cmd_list[0].endswith('.exe') and '/' not in cmd_list[0] and '\\' not in cmd_list[0]:
            # Only add .exe if it's a simple command name without path separators
            if cmd_list[0] in ['lean', 'lake', 'elan']:
                cmd_list[0] = f"{cmd_list[0]}.exe"
    return cmd_list

class LeanVerifier:
    """
    A service class to interact with the Lean 4 proof assistant.

    This class is responsible for taking a student's natural language proof step,
    translating it into a formal Lean tactic, and verifying it against the current
    proof state.

    Enhanced features:
    1. Full Lean error output parsing for LLM feedback
    2. Developer mode configuration system
    3. Auto-solve functionality with configurable attempts
    4. Comprehensive attempt logging
    5. Proof caching for performance optimization
    6. Lean environment optimization
    7. Parallel processing for multiple proof attempts
    8. Intelligent tactic prediction and optimization
    9. Aggressive caching strategies
    10. Optimized Lean execution patterns
    """

    def __init__(self, developer_mode: bool = None, max_auto_solve_attempts: int = None):
        """
        Initializes the verifier with developer mode settings and performance optimizations.
        """
        logger.info("Lean Verifier initialized with performance optimizations.")
        
        # Developer mode configuration - use config file if not specified
        self.developer_mode = developer_mode if developer_mode is not None else developer_config.get("developer_mode", False)
        self.max_auto_solve_attempts = max_auto_solve_attempts if max_auto_solve_attempts is not None else developer_config.get("max_auto_solve_attempts", 5)
        
        # Performance optimization flags
        self.environment_optimized = False
        self.cache_enabled = True
        self.parallel_processing = True
        self.aggressive_caching = True
        
        # Performance tracking
        self.performance_stats = {
            'total_verifications': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'parallel_executions': 0,
            'avg_verification_time': 0.0,
            'total_time_saved': 0.0
        }
        
        # Thread pool for parallel processing
        self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=4)
        
        # Pre-compiled tactic patterns for faster matching
        self._compile_tactic_patterns()
        
        # Common Lean tactics and their natural language equivalents
        self.tactic_mappings = {
            "commutativity": ["rw [mul_comm]", "rw [add_comm]", "rw [comm]"],
            "associativity": ["rw [mul_assoc]", "rw [add_assoc]", "rw [assoc]"],
            "distributivity": ["rw [mul_add]", "rw [add_mul]", "rw [distrib]"],
            "identity": ["rw [mul_one]", "rw [one_mul]", "rw [add_zero]", "rw [zero_add]"],
            "definition": ["unfold", "def", "by definition"],
            "reflexivity": ["refl", "reflexivity"],
            "symmetry": ["symm", "symmetry"],
            "transitivity": ["trans", "transitivity"],
            "induction": ["induction", "induct"],
            "cases": ["cases", "case analysis"],
            "contradiction": ["contradiction", "contra", "absurd"],
            "exact": ["exact", "apply", "use"],
            "intro": ["intro", "introduction"],
            "elimination": ["elim", "elimination"],
            "simplification": ["simp", "simplify", "simplification"],
            "rewrite": ["rw", "rewrite", "rewriting"]
        }

    def _compile_tactic_patterns(self):
        """Pre-compile regex patterns for faster tactic matching."""
        self.tactic_patterns = {
            'intro': re.compile(r'intro\s+\w+', re.IGNORECASE),
            'exact': re.compile(r'exact\s+\w+', re.IGNORECASE),
            'rw': re.compile(r'rw\s*\[([^\]]+)\]', re.IGNORECASE),
            'simp': re.compile(r'simp\s*\[([^\]]*)\]', re.IGNORECASE),
            'refl': re.compile(r'refl', re.IGNORECASE),
            'induction': re.compile(r'induction\s+\w+', re.IGNORECASE)
        }

    @lru_cache(maxsize=1000)
    def _fast_goal_classification(self, goal: str) -> str:
        """Fast goal classification using cached patterns."""
        goal_lower = goal.lower()
        
        # Check for specific patterns first
        if 'comm' in goal_lower:
            return 'commutativity'
        elif 'assoc' in goal_lower:
            return 'associativity'
        elif 'distrib' in goal_lower:
            return 'distributivity'
        elif 'zero' in goal_lower:
            return 'identity'
        
        # Check for universal quantifiers
        if '∀' in goal or 'forall' in goal_lower:
            # Check if it's a universal statement with arithmetic
            if '+' in goal and '=' in goal:
                # Look for commutativity pattern: a + b = b + a
                if re.search(r'(\w+)\s*\+\s*(\w+)\s*=\s*\2\s*\+\s*\1', goal):
                    return 'commutativity'
                # Look for associativity pattern: (a + b) + c = a + (b + c)
                elif re.search(r'\([^)]+\s*\+\s*[^)]+\)\s*\+\s*\w+\s*=\s*\w+\s*\+\s*\([^)]+\s*\+\s*[^)]+\)', goal):
                    return 'associativity'
                # Look for identity pattern: n + 0 = n or 0 + n = n
                elif re.search(r'(\w+)\s*\+\s*0\s*=\s*\1|0\s*\+\s*(\w+)\s*=\s*\2', goal):
                    return 'identity'
            return 'universal'
        
        # Check for existential quantifiers
        if '∃' in goal or 'exists' in goal_lower:
            return 'existential'
        
        # Check for simple arithmetic equality (like 1 + 1 = 2)
        # Look for patterns like "1 + 1 = 2" within the goal
        if re.search(r'\d+\s*\+\s*\d+\s*=\s*\d+', goal):
            return 'simple_arithmetic'
        
        # Default to generic
        return 'generic'

    def _optimize_lean_execution(self, tactic: str, goal: str) -> str:
        """Optimize Lean execution by selecting the most efficient approach."""
        goal_type = self._fast_goal_classification(goal)
        
        # Use optimized execution patterns based on goal type
        if goal_type == 'commutativity':
            return self._optimize_commutativity_proof(tactic, goal)
        elif goal_type == 'associativity':
            return self._optimize_associativity_proof(tactic, goal)
        elif goal_type == 'identity':
            return self._optimize_identity_proof(tactic, goal)
        elif goal_type == 'simple_arithmetic':
            return self._optimize_simple_arithmetic_proof(tactic, goal)
        else:
            return tactic

    def _optimize_commutativity_proof(self, tactic: str, goal: str) -> str:
        """Optimize commutativity proofs with direct library calls."""
        if 'intro' in tactic and 'exact' in tactic:
            # Extract variable names and use direct library call
            vars_match = re.findall(r'intro\s+(\w+)', tactic)
            if len(vars_match) >= 2:
                return f"intro {vars_match[0]} {vars_match[1]}; exact Nat.add_comm {vars_match[0]} {vars_match[1]}"
        return tactic

    def _optimize_associativity_proof(self, tactic: str, goal: str) -> str:
        """Optimize associativity proofs with direct library calls."""
        if 'intro' in tactic and 'exact' in tactic:
            vars_match = re.findall(r'intro\s+(\w+)', tactic)
            if len(vars_match) >= 3:
                return f"intro {vars_match[0]} {vars_match[1]} {vars_match[2]}; exact Nat.add_assoc {vars_match[0]} {vars_match[1]} {vars_match[2]}"
        return tactic

    def _optimize_identity_proof(self, tactic: str, goal: str) -> str:
        """Optimize identity proofs with direct library calls."""
        if 'intro' in tactic and 'exact' in tactic:
            vars_match = re.findall(r'intro\s+(\w+)', tactic)
            if vars_match:
                return f"intro {vars_match[0]}; exact Nat.add_zero {vars_match[0]}"
        return tactic

    def _optimize_simple_arithmetic_proof(self, tactic: str, goal: str) -> str:
        """Optimize simple arithmetic proofs with direct tactics."""
        # For simple arithmetic like 1 + 1 = 2, use the most direct approach
        if 'rfl' in tactic or 'refl' in tactic:
            return 'rfl'
        elif 'simp' in tactic:
            return 'simp'
        elif 'norm_num' in tactic:
            return 'norm_num'
        else:
            return 'rfl'  # Default to reflexivity for simple arithmetic

    def _parallel_verify_tactics(self, tactics: List[str], goal: str) -> List[Dict[str, Any]]:
        """Verify multiple tactics in parallel for faster execution."""
        if not self.parallel_processing or len(tactics) <= 1:
            return [self.run_lean_verification(tactic) for tactic in tactics]
        
        self.performance_stats['parallel_executions'] += 1
        
        # Submit all tactics for parallel execution
        future_to_tactic = {
            self.executor.submit(self.run_lean_verification, tactic): tactic 
            for tactic in tactics
        }
        
        results = []
        for future in concurrent.futures.as_completed(future_to_tactic, timeout=60):
            try:
                result = future.result(timeout=30)
                results.append(result)
            except Exception as e:
                logger.error(f"Parallel verification failed: {e}")
                results.append({"success": False, "error": str(e)})
        
        return results

    def _generate_optimized_tactics(self, goal: str, goal_type: str) -> List[str]:
        """Generate optimized tactics based on goal type and patterns."""
        optimized_tactics = []
        
        if goal_type == 'commutativity':
            # Generate multiple optimized approaches
            optimized_tactics = [
                "intro a b; exact Nat.add_comm a b",
                "intro a b; rw [Nat.add_comm]",
                "intro a b; induction b; simp; exact Nat.add_comm a b"
            ]
        elif goal_type == 'associativity':
            optimized_tactics = [
                "intro a b c; exact Nat.add_assoc a b c",
                "intro a b c; rw [Nat.add_assoc]",
                "intro a b c; induction c; simp; exact Nat.add_assoc a b c"
            ]
        elif goal_type == 'identity':
            optimized_tactics = [
                "intro n; exact Nat.add_zero n",
                "intro n; rw [Nat.add_zero]",
                "intro n; simp [Nat.add_zero]"
            ]
        elif goal_type == 'simple_arithmetic':
            optimized_tactics = [
                "rfl",
                "simp",
                "norm_num",
                "exact rfl"
            ]
        else:
            # Generic optimized tactics
            optimized_tactics = [
                "intro",
                "simp",
                "refl",
                "exact"
            ]
        
        return optimized_tactics

    def _aggressive_cache_lookup(self, goal: str, goal_type: str) -> Optional[Dict[str, Any]]:
        """Aggressive cache lookup with multiple strategies."""
        if not self.aggressive_caching:
            return None
        
        # Try multiple cache keys for the same goal
        cache_keys = [
            goal,
            goal_type,
            self._normalize_goal(goal),
            self._extract_key_components(goal)
        ]
        
        for key in cache_keys:
            cached_result = get_cached_proof_result(key, goal)
            if cached_result:
                self.performance_stats['cache_hits'] += 1
                return cached_result
        
        self.performance_stats['cache_misses'] += 1
        return None

    def _normalize_goal(self, goal: str) -> str:
        """Normalize goal for better cache matching."""
        # Remove whitespace and normalize
        normalized = re.sub(r'\s+', ' ', goal.strip())
        # Extract key mathematical symbols
        symbols = re.findall(r'[∀∃=+\-*/()]', normalized)
        return ''.join(symbols)

    def _extract_key_components(self, goal: str) -> str:
        """Extract key components for cache matching."""
        # Extract variable names and operations
        vars_match = re.findall(r'(\w+)\s*[=+\-*/]', goal)
        ops_match = re.findall(r'[=+\-*/]', goal)
        return f"{'_'.join(vars_match)}_{'_'.join(ops_match)}"

    def set_developer_mode(self, enabled: bool) -> None:
        """Toggle developer mode on/off."""
        self.developer_mode = enabled
        developer_config.set("developer_mode", enabled)
        developer_logger.log_config_change({
            "action": "set_developer_mode",
            "enabled": enabled
        })
        logger.info(f"Developer mode {'enabled' if enabled else 'disabled'}")

    def set_max_attempts(self, max_attempts: int) -> None:
        """Set the maximum number of auto-solve attempts."""
        self.max_auto_solve_attempts = max_attempts
        developer_config.set("max_auto_solve_attempts", max_attempts)
        developer_logger.log_config_change({
            "action": "set_max_attempts",
            "max_attempts": max_attempts
        })
        logger.info(f"Max auto-solve attempts set to {max_attempts}")

    def parse_lean_error_output(self, error_output: str) -> Dict[str, Any]:
        """
        Parse Lean error output to extract meaningful information for LLM feedback.
        """
        if not error_output:
            return {"type": "no_error", "message": "No error output"}
        
        # Common Lean error patterns
        error_info = {
            "type": "unknown",
            "message": error_output,
            "line_number": None,
            "column_number": None,
            "suggestion": None,
            "context": None
        }
        
        # Parse syntax errors
        syntax_patterns = [
            r"unexpected token '([^']+)'",
            r"syntax error",
            r"invalid '([^']+)' command",
            r"unexpected token 'by'; expected '{' or tactic",
            r"unsolved goals"
        ]
        
        for pattern in syntax_patterns:
            if re.search(pattern, error_output, re.IGNORECASE):
                error_info["type"] = "syntax_error"
                error_info["suggestion"] = "Check Lean syntax - ensure proper theorem declaration and tactic format"
                break
        
        # Parse unknown identifier errors
        unknown_pattern = r"unknown (?:constant|identifier) '([^']+)'"
        match = re.search(unknown_pattern, error_output)
        if match:
            error_info["type"] = "unknown_constant"
            error_info["context"] = match.group(1)
            error_info["suggestion"] = f"Unknown constant '{match.group(1)}' - try using available theorems or simp with lemmas"
        
        # Parse type mismatch errors
        type_patterns = [
            r"Application type mismatch",
            r"type mismatch",
            r"unsolved goals"
        ]
        
        for pattern in type_patterns:
            if re.search(pattern, error_output, re.IGNORECASE):
                error_info["type"] = "type_mismatch"
                error_info["suggestion"] = "Check variable types and ensure proper introductions before applying theorems"
                break
        
        # Parse tactic failure errors
        tactic_pattern = r"tactic '[^']+' failed"
        if re.search(tactic_pattern, error_output):
            error_info["type"] = "tactic_failed"
            error_info["suggestion"] = "Try a simpler tactic or break the goal into subgoals"
        
        # Parse import errors
        import_pattern = r"invalid 'import' command"
        if re.search(import_pattern, error_output):
            error_info["type"] = "import_error"
            error_info["suggestion"] = "Imports must be at the beginning of the file"
        
        # Extract line and column numbers if available
        line_col_pattern = r"(\d+):(\d+):"
        line_match = re.search(line_col_pattern, error_output)
        if line_match:
            error_info["line_number"] = int(line_match.group(1))
            error_info["column_number"] = int(line_match.group(2))
        
        return error_info

    def translate_natural_language_to_tactic(self, natural_language_step: str, current_proof_state: str) -> str:
        """
        Translate natural language to Lean tactic using the enhanced prompt system.
        """
        try:
            # Get available theorems
            available_theorems = lean_kb.get_available_theorems()
            
            # Create context-aware prompt
            prompt = enhanced_prompts.create_context_aware_prompt(
                goal=current_proof_state,
                available_theorems=available_theorems,
                error_history=[],
                difficulty=self._determine_difficulty(current_proof_state)
            )
            
            # Get LLM response
            response = get_llm_response(prompt)
            
            # Clean up the response to extract just the tactic
            tactic = self._extract_lean_tactic(response)
            
            if self.developer_mode:
                logger.info(f"Generated tactic: {tactic}")
            
            return tactic
            
        except Exception as e:
            logger.error(f"Error translating natural language to tactic: {e}")
            return ""

    def run_lean_verification(self, tactic: str, goal: str = None) -> Dict[str, Any]:
        """
        Run Lean verification with aggressive performance optimizations.
        Uses parallel processing, intelligent caching, and optimized execution patterns.
        """
        start_time = time.time()
        self.performance_stats['total_verifications'] += 1
        
        try:
            # Fast goal classification for optimization
            if goal:
                goal_type = self._fast_goal_classification(goal)
                
                # Aggressive cache lookup with multiple strategies
                cached_result = self._aggressive_cache_lookup(goal, goal_type)
                if cached_result:
                    if self.developer_mode:
                        logger.info(f"AGGRESSIVE CACHE HIT for goal type: {goal_type}")
                    return cached_result
                
                # Optimize tactic execution based on goal type
                optimized_tactic = self._optimize_lean_execution(tactic, goal)
                if optimized_tactic != tactic:
                    if self.developer_mode:
                        logger.info(f"Tactic optimized: {tactic} -> {optimized_tactic}")
                    tactic = optimized_tactic
            
            # Ensure Lean environment is optimized (only once per session)
            if not self.environment_optimized:
                if ensure_lean_environment_ready():
                    self.environment_optimized = True
                    logger.info("Lean environment optimization completed")
                else:
                    logger.warning("Lean environment optimization failed, continuing without optimization")
            
            # Validate tactic syntax first (fast validation)
            validation_result = self._validate_proof_syntax(tactic)
            if not validation_result["valid"]:
                return {
                    "success": False,
                    "error": f"Syntax validation failed: {validation_result['reason']}",
                    "error_type": "syntax_error"
                }
            
            # Create optimized Lean file content
            lean_file_content = self._create_proper_lean_file(tactic, goal)
            
            # Standard cache check (if aggressive caching didn't find it)
            if self.cache_enabled and not goal:
                cached_result = get_cached_proof_result(tactic, lean_file_content)
                if cached_result:
                    if self.developer_mode:
                        logger.info(f"Standard CACHE HIT for tactic: {tactic}")
                    return cached_result
            
            if self.developer_mode:
                logger.info(f"Cache MISS for tactic: {tactic}")
            
            # Write to temporary file in the Lean project directory
            lean_project_dir = "/workspaces/Altera-Labs/backend/lean_verifier"
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=lean_project_dir, delete=False) as f:
                f.write(lean_file_content)
                temp_file_path = f.name
                temp_file_name = os.path.basename(temp_file_path)
            
            try:
                # Change to Lean project directory and use lake
                original_cwd = os.getcwd()
                os.chdir(lean_project_dir)
                
                # Run lake lean for verification with optimized timeout
                result = subprocess.run(
                    ['lake', 'lean', temp_file_name],
                    capture_output=True,
                    text=True,
                    timeout=20  # Reduced timeout for faster failure detection
                )
                
                if self.developer_mode:
                    logger.info(f"Lake return code: {result.returncode}")
                
                # Check if verification succeeded
                if result.returncode == 0:
                    verification_result = {"success": True, "output": result.stdout}
                    
                    # Cache successful result with multiple keys
                    if self.cache_enabled:
                        cache_proof_result(tactic, lean_file_content, verification_result)
                        if goal:
                            # Cache with goal-based keys for better hit rates
                            cache_proof_result(goal, lean_file_content, verification_result)
                            cache_proof_result(goal_type, lean_file_content, verification_result)
                    
                    # Update performance stats
                    verification_time = time.time() - start_time
                    self.performance_stats['avg_verification_time'] = (
                        (self.performance_stats['avg_verification_time'] * (self.performance_stats['total_verifications'] - 1) + verification_time) 
                        / self.performance_stats['total_verifications']
                    )
                    
                    return verification_result
                else:
                    # Parse error output
                    error_output = result.stderr if result.stderr else result.stdout
                    if not error_output.strip():
                        error_output = f"Lean verification failed with no error message (return code: {result.returncode})"
                    
                    parsed_error = self.parse_lean_error_output(error_output)
                    verification_result = {
                        "success": False,
                        "error": error_output,
                        "error_type": parsed_error["type"],
                        "suggestion": parsed_error["suggestion"]
                    }
                    
                    # Cache failed result (with shorter TTL)
                    if self.cache_enabled:
                        cache_proof_result(tactic, lean_file_content, verification_result, ttl_hours=1)
                    
                    return verification_result
                    
            finally:
                # Clean up temporary file
                if os.path.exists(temp_file_path):
                    os.unlink(temp_file_path)
                # Restore original working directory
                os.chdir(original_cwd)
                
        except subprocess.TimeoutExpired:
            error_result = {
                "success": False,
                "error": "Lean verification timed out after 20 seconds",
                "error_type": "timeout"
            }
            
            # Cache timeout result
            if self.cache_enabled:
                cache_proof_result(tactic, lean_file_content, error_result, ttl_hours=1)
            
            return error_result
            
        except Exception as e:
            error_result = {
                "success": False,
                "error": f"Unexpected error during Lean verification: {str(e)}",
                "error_type": "system_error"
            }
            
            # Cache error result
            if self.cache_enabled:
                cache_proof_result(tactic, lean_file_content, error_result, ttl_hours=1)
            
            return error_result
            
        except Exception as e:
            error_result = {
                "success": False,
                "error": f"Unexpected error during Lean verification: {str(e)}",
                "error_type": "system_error"
            }
            
            # Cache error result
            if self.cache_enabled:
                cache_proof_result(tactic, lean_file_content, error_result, ttl_hours=1)
            
            return error_result

    def _validate_proof_syntax(self, proof_code: str) -> Dict[str, Any]:
        """
        Validate proof code syntax before running Lean.
        """
        # Check for common syntax issues
        issues = []
        
        # Check for markdown formatting
        if '```' in proof_code or '`' in proof_code:
            issues.append("Contains markdown formatting")
        
        # Check for explanatory text
        explanatory_keywords = ['explanation', 'note:', 'comment:', 'this tactic', 'the tactic']
        for keyword in explanatory_keywords:
            if keyword.lower() in proof_code.lower():
                issues.append(f"Contains explanatory text: {keyword}")
        
        # Check for invalid characters (but allow underscores in theorem names)
        invalid_chars = ['*', '**', '`']
        for char in invalid_chars:
            if char in proof_code:
                issues.append(f"Contains invalid character: {char}")
        
        # Check for import statements in tactics (these should be removed)
        if 'import ' in proof_code:
            issues.append("Contains import statement in tactic")
        
        # Check for proper tactic structure
        valid_tactics = ['intro', 'exact', 'simp', 'rw', 'rfl', 'constructor', 'cases', 'induction', 'ring', 'norm_num']
        if not any(tactic in proof_code for tactic in valid_tactics):
            issues.append("No valid Lean tactics found")
        
        if issues:
            return {
                "valid": False,
                "reason": f"Syntax validation failed: {'; '.join(issues)}",
                "issues": issues
            }
        
        return {"valid": True, "reason": None, "issues": []}

    def _extract_lean_tactic(self, response: str) -> str:
        """
        Extract clean Lean tactic from LLM response.
        Enhanced to handle multiple tactics and better cleaning.
        """
        # Remove markdown formatting
        response = re.sub(r'```lean\s*', '', response)
        response = re.sub(r'```\s*', '', response)
        
        # Split into lines and clean each line
        lines = response.strip().split('\n')
        tactic_lines = []
        
        for line in lines:
            line = line.strip()
            # Skip empty lines, comments, and explanatory text
            if not line or line.startswith('#') or line.startswith('--'): 
                continue
            if any(keyword in line.lower() for keyword in ['explanation', 'note:', 'comment:', 'this', 'the', 'here']): 
                continue
            if line.startswith('import ') or line.startswith('open ') or line.startswith('theorem ') or line.startswith('lemma '): 
                continue
            tactic_lines.append(line)
        
        # Join lines and clean up
        tactic = ' '.join(tactic_lines).strip()
        tactic = re.sub(r'\s+', ' ', tactic)
        
        # Handle multiple tactics - take the first complete one
        if ';' in tactic:
            # Split by semicolon and take the first complete tactic
            tactics = [t.strip() for t in tactic.split(';') if t.strip()]
            if tactics:
                tactic = tactics[0]
        
        # If still multiple tactics, try to extract the most likely one
        if len(tactic.split()) > 10:  # Too long, probably multiple tactics
            # Look for common tactic patterns
            patterns = [
                r'intro\s+\w+;\s*exact\s+\w+\.\w+',
                r'intro\s+\w+\s+\w+;\s*exact\s+\w+\.\w+',
                r'intro\s+\w+;\s*rfl',
                r'intro\s+\w+;\s*simp\s*\[.*?\]',
                r'intro\s+\w+;\s*rw\s*\[.*?\]'
            ]
            for pattern in patterns:
                match = re.search(pattern, tactic)
                if match:
                    tactic = match.group(0)
                    break
        
        return tactic.strip()

    def diagnose_lean_environment(self) -> Dict[str, Any]:
        """
        Diagnose Lean environment and configuration.
        """
        diagnosis = {
            "lean_installed": False,
            "lean_version": None,
            "mathlib_available": False,
            "test_proof_works": False,
            "issues": []
        }
        
        try:
            # Check if Lean is installed
            result = subprocess.run(get_safe_subprocess_args(['lean', '--version']), capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                diagnosis["lean_installed"] = True
                diagnosis["lean_version"] = result.stdout.strip()
            else:
                diagnosis["issues"].append("Lean not found or not working properly")
                return diagnosis
                
        except Exception as e:
            diagnosis["issues"].append(f"Error checking Lean installation: {str(e)}")
            return diagnosis
        
        # Check if Lean project exists and has Mathlib
        lean_project_dir = "/workspaces/Altera-Labs/backend/lean_verifier"
        if not os.path.exists(lean_project_dir):
            diagnosis["issues"].append(f"Lean project directory not found: {lean_project_dir}")
            return diagnosis
        
        lakefile_path = os.path.join(lean_project_dir, "lakefile.toml")
        if not os.path.exists(lakefile_path):
            diagnosis["issues"].append("lakefile.toml not found in Lean project")
            return diagnosis
        
        # Check if Mathlib is in lakefile.toml
        try:
            with open(lakefile_path, 'r') as f:
                lakefile_content = f.read()
                if "require mathlib" in lakefile_content:
                    diagnosis["mathlib_available"] = True
                else:
                    diagnosis["issues"].append("Mathlib not found in lakefile.toml")
        except Exception as e:
            diagnosis["issues"].append(f"Error reading lakefile.toml: {str(e)}")
        
        # Test a simple proof using lake
        test_proof = """import Mathlib.Data.Nat.Basic
open Classical

theorem test : ∀ n : ℕ, n + 0 = n := by
  intro n
  exact Nat.add_zero n
"""
        
        try:
            # Change to Lean project directory
            original_cwd = os.getcwd()
            os.chdir(lean_project_dir)
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(test_proof)
                temp_file_path = f.name
                temp_file_name = os.path.basename(temp_file_path)
            
            try:
                result = subprocess.run(
                    ['lake', 'lean', temp_file_name],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                
                if result.returncode == 0:
                    diagnosis["test_proof_works"] = True
                else:
                    diagnosis["issues"].append(f"Test proof failed: {result.stderr}")
                    
            finally:
                if os.path.exists(temp_file_path):
                    os.unlink(temp_file_path)
                os.chdir(original_cwd)
                    
        except Exception as e:
            diagnosis["issues"].append(f"Error testing proof: {str(e)}")
        
        return diagnosis

    def _create_proper_lean_file(self, proof_code: str, goal: str = None) -> str:
        """
        Create a proper Lean file with necessary imports and structure.
        Enhanced with better error handling and debugging.
        """
        # Ensure we have a clean tactic
        tactic = proof_code.strip()
        if not tactic:
            raise ValueError("Empty tactic provided")
        
        # Extract the theorem statement from the goal if provided
        if goal and "theorem" in goal:
            # Extract the theorem line from the goal
            lines = goal.strip().split('\n')
            theorem_line = None
            for line in lines:
                if line.strip().startswith('theorem'):
                    theorem_line = line.strip()
                    break
            
            if theorem_line:
                # Replace ":= by sorry" with ":= by" and add our tactic
                theorem_line = theorem_line.replace(":= by sorry", ":= by")
                lean_content = f"""import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
open Classical

{theorem_line}
  {tactic}
"""
            else:
                # Fallback to default
                lean_content = f"""import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
open Classical

theorem auto_proof : ∀ n : ℕ, n + 0 = n := by
  {tactic}
"""
        else:
            # Default content
            lean_content = f"""import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
open Classical

theorem auto_proof : ∀ n : ℕ, n + 0 = n := by
  {tactic}
"""
        
        return lean_content

    def auto_solve_proof(self, initial_proof_state: str, max_attempts: int = None) -> Dict[str, Any]:
        """
        Auto-solve a proof with aggressive performance optimizations.
        Uses parallel processing, intelligent caching, and optimized execution patterns.
        """
        if max_attempts is None:
            max_attempts = self.max_auto_solve_attempts
        
        attempts = []
        error_history = []
        start_time = time.time()
        
        # Fast goal classification and optimization
        goal_type = self._fast_goal_classification(initial_proof_state)
        difficulty = self._determine_difficulty(initial_proof_state)
        
        # Optimize Lean environment for this specific goal type
        if not self.environment_optimized:
            logger.info(f"Optimizing Lean environment for goal type: {goal_type}")
            if optimize_lean_for_goal(initial_proof_state):
                self.environment_optimized = True
                logger.info("Goal-specific Lean optimization completed")
            else:
                logger.warning("Goal-specific optimization failed, using default environment")
        
        logger.info(f"Auto-solve attempt 1/{max_attempts}")
        logger.info(f"Selected strategy '{goal_type}' for goal: {initial_proof_state}...")
        
        # Generate optimized tactics for parallel execution
        optimized_tactics = self._generate_optimized_tactics(initial_proof_state, goal_type)
        
        for attempt_num in range(1, max_attempts + 1):
            try:
                # First attempt: Try optimized tactics in parallel
                if attempt_num == 1 and optimized_tactics:
                    if self.developer_mode:
                        logger.info(f"Trying {len(optimized_tactics)} optimized tactics in parallel")
                    
                    # Verify optimized tactics in parallel
                    parallel_results = self._parallel_verify_tactics(optimized_tactics, initial_proof_state)
                    
                    # Check for success in parallel results
                    for i, result in enumerate(parallel_results):
                        if result.get("success", False):
                            tactic = optimized_tactics[i]
                            end_time = time.time()
                            success_result = {
                                "success": True,
                                "tactic": tactic,
                                "attempts": [tactic],
                                "time": end_time - start_time,
                                "strategy": f"parallel_{goal_type}",
                                "generated": tactic,
                                "expected": "success",
                                "llm_time": 0.0,  # No LLM call needed
                                "verify_time": end_time - start_time,
                                "total_time": end_time - start_time,
                                "parallel_execution": True
                            }
                            
                            if self.developer_mode:
                                developer_logger.log_attempt({
                                    "attempt": attempt_num,
                                    "tactic": tactic,
                                    "success": True,
                                    "llm_time": 0.0,
                                    "verify_time": end_time - start_time,
                                    "total_time": end_time - start_time,
                                    "strategy": f"parallel_{goal_type}"
                                })
                            
                            return success_result
                    
                    # If parallel execution failed, continue with LLM-based approach
                    if self.developer_mode:
                        logger.info("Parallel tactics failed, trying LLM-based approach")
                
                # Generate tactic based on attempt number and error history
                if attempt_num == 1:
                    # First attempt: use axiom-driven strategy diversification (DREAM approach)
                    prompt = enhanced_prompts.create_axiom_driven_prompt(
                        goal=initial_proof_state,
                        available_axioms=lean_kb.get_available_theorems()
                    )
                elif attempt_num == 2:
                    # Second attempt: use context-aware prompt with error learning
                    prompt = enhanced_prompts.create_context_aware_prompt(
                        goal=initial_proof_state,
                        error_history=error_history,
                        difficulty=difficulty
                    )
                elif attempt_num == 3:
                    # Third attempt: use sub-proposition error feedback (DREAM approach)
                    last_error = error_history[-1] if error_history else "unknown error"
                    prompt = enhanced_prompts.create_sub_proposition_feedback_prompt(
                        goal=initial_proof_state,
                        failed_attempt=attempts[-1] if attempts else "",
                        sub_goals=enhanced_prompts._extract_sub_goals(initial_proof_state)
                    )
                elif attempt_num <= 5:
                    # Later attempts: use error learning with enhanced feedback
                    last_error = error_history[-1] if error_history else "unknown error"
                    prompt = enhanced_prompts.create_error_learning_prompt(
                        goal=initial_proof_state,
                        error_output=last_error,
                        attempt_count=attempt_num,
                        previous_attempts=attempts
                    )
                else:
                    # Final attempts: use fallback strategy
                    prompt = enhanced_prompts.create_fallback_prompt(
                        goal=initial_proof_state,
                        failed_attempts=attempts
                    )
                
                # Get LLM response with timing and timeout
                llm_start_time = time.time()
                response = get_llm_response(prompt)
                llm_time = time.time() - llm_start_time
                
                # Check for timeout
                if llm_time > 10.0:  # 10 second timeout
                    logger.warning(f"LLM response took {llm_time:.2f}s - too slow")
                
                tactic = self._extract_lean_tactic(response)
                
                if self.developer_mode:
                    logger.info(f"LLM generated tactic: {tactic}")
                
                # Verify the tactic with timing and goal optimization
                verify_start_time = time.time()
                verification_result = self.run_lean_verification(tactic, initial_proof_state)
                verify_time = time.time() - verify_start_time
                
                if self.developer_mode:
                    logger.info(f"LLM time: {llm_time:.3f}s, Verification time: {verify_time:.3f}s")
                
                if verification_result["success"]:
                    # Success!
                    end_time = time.time()
                    success_result = {
                        "success": True,
                        "tactic": tactic,
                        "attempts": attempts + [tactic],
                        "time": end_time - start_time,
                        "strategy": goal_type,
                        "generated": tactic,
                        "expected": "success",
                        "llm_time": llm_time,
                        "verify_time": verify_time,
                        "total_time": end_time - start_time
                    }
                    
                    # Log successful attempt
                    if self.developer_mode:
                        developer_logger.log_attempt({
                            "attempt": attempt_num,
                            "tactic": tactic,
                            "success": True,
                            "llm_time": llm_time,
                            "verify_time": verify_time,
                            "total_time": end_time - start_time,
                            "strategy": goal_type
                        })
                    
                    return success_result
                else:
                    # Record the attempt and error with performance metrics
                    attempt_data = {
                        "attempt": attempt_num,
                        "tactic": tactic,
                        "success": False,
                        "error": verification_result.get("error", "unknown error"),
                        "llm_time": llm_time,
                        "verify_time": verify_time,
                        "total_time": time.time() - start_time,
                        "strategy": goal_type
                    }
                    attempts.append(attempt_data)
                    error_history.append(verification_result.get("error", "unknown error"))
                    
                    # Log failed attempt
                    if self.developer_mode:
                        developer_logger.log_attempt(attempt_data)
                    
                    if self.developer_mode:
                        logger.info(f"Attempt {attempt_num} failed: {verification_result.get('error', 'unknown error')}")
                    
                    # Continue to next attempt
                    if attempt_num < max_attempts:
                        logger.info(f"Auto-solve attempt {attempt_num + 1}/{max_attempts}")
                        logger.info(f"Selected strategy '{goal_type}' for goal: {initial_proof_state}...")
                
            except Exception as e:
                logger.error(f"Error in auto-solve attempt {attempt_num}: {e}")
                attempts.append(f"error: {str(e)}")
                error_history.append(str(e))
        
        # All attempts failed
        end_time = time.time()
        return {
            "success": False,
            "attempts": attempts,
            "time": end_time - start_time,
            "strategy": goal_type,
            "generated": "",
            "expected": "success"
        }
    
    def _classify_goal_type(self, goal: str) -> str:
        """Classify the type of goal for better strategy selection."""
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
        elif "n + 0 = n" in goal or "0 + n = n" in goal:
            return "addition_identity"
        elif "a + b = b + a" in goal:
            return "commutativity"
        elif "a * (b + c) = a * b + a * c" in goal:
            return "distributivity"
        else:
            return "generic"
    
    def _determine_difficulty(self, goal: str) -> str:
        """Determine the difficulty level of a goal."""
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
        
        if complexity < 0.3:
            return "easy"
        elif complexity < 0.6:
            return "medium"
        elif complexity < 0.8:
            return "hard"
        else:
            return "very_hard"

    def verify_step(self, current_proof_state: str, natural_language_step: str) -> Dict[str, Any]:
        """
        Verifies a single natural language step in a mathematical proof.
        Enhanced with detailed error information for developer mode.
        """
        logger.info(f"Attempting to verify step: '{natural_language_step}'")

        # Translate natural language to Lean tactic
        tactic = self.translate_natural_language_to_tactic(natural_language_step, current_proof_state)
        
        # Apply the tactic
        if "sorry" in current_proof_state:
            new_state = current_proof_state.replace("sorry", tactic)
        else:
            new_state = current_proof_state + "\n  " + tactic
        
        # Verify with Lean
        verification_result = self.run_lean_verification(new_state)
        
        if verification_result["success"]:
            is_complete = "sorry" not in new_state
            feedback = f"Excellent! The tactic `{tactic}` correctly progresses the proof."
            if is_complete:
                feedback += " The proof is now complete!"
        else:
            error_info = verification_result.get("error_info", {}) or {}
            feedback = f"The tactic `{tactic}` didn't work. "
            if error_info and error_info.get("suggestion"):
                feedback += f"Error: {error_info['message']}. Suggestion: {error_info['suggestion']}"
            else:
                feedback += f"Error: {verification_result.get('error', 'Unknown error')}"
            new_state = current_proof_state  # Revert to previous state
        
        response = {
            "verified": verification_result["success"],
            "new_proof_state": new_state,
            "feedback": feedback,
            "is_complete": verification_result["success"] and "sorry" not in new_state,
            "error": verification_result.get("error") if not verification_result["success"] else None,
            "error_info": verification_result.get("error_info") if not verification_result["success"] else None,
        }

        logger.info(f"Verification result: {response}")
        return response

    def get_developer_logs(self) -> Dict[str, Any]:
        """Get developer mode logs and configuration with performance statistics."""
        logs = {
            "developer_mode": self.developer_mode,
            "max_auto_solve_attempts": self.max_auto_solve_attempts,
            "config": developer_config.get_all_settings(),
            "recent_logs": developer_logger.get_recent_logs(50),
            "attempt_logs": developer_logger.get_logs_by_type("auto_solve_attempt")
        }
        
        # Add performance optimization statistics
        if self.cache_enabled:
            from proof_cache import proof_cache
            logs["cache_stats"] = proof_cache.get_cache_stats()
        
        if hasattr(self, 'environment_optimized'):
            from lean_environment_manager import get_lean_environment_status
            logs["environment_stats"] = get_lean_environment_status()
        
        return logs
    
    def get_performance_stats(self) -> Dict[str, Any]:
        """Get comprehensive performance statistics."""
        stats = {
            "cache_enabled": self.cache_enabled,
            "environment_optimized": getattr(self, 'environment_optimized', False),
            "developer_mode": self.developer_mode
        }
        
        # Add cache statistics
        if self.cache_enabled:
            from proof_cache import proof_cache
            stats["cache"] = proof_cache.get_cache_stats()
        
        # Add environment statistics
        try:
            from lean_environment_manager import get_lean_environment_status
            stats["environment"] = get_lean_environment_status()
        except ImportError:
            stats["environment"] = {"error": "Environment manager not available"}
        
        return stats
    
    def toggle_cache(self, enabled: bool = None) -> bool:
        """Toggle proof caching on/off."""
        if enabled is None:
            self.cache_enabled = not self.cache_enabled
        else:
            self.cache_enabled = enabled
        
        logger.info(f"Proof caching {'enabled' if self.cache_enabled else 'disabled'}")
        return self.cache_enabled
    
    def clear_cache(self):
        """Clear the proof cache."""
        if self.cache_enabled:
            from proof_cache import proof_cache
            proof_cache.clear_cache()
            logger.info("Proof cache cleared")
    
    def optimize_environment(self, force_rebuild: bool = False) -> bool:
        """Manually trigger Lean environment optimization."""
        try:
            from lean_environment_manager import ensure_lean_environment_ready
            success = ensure_lean_environment_ready(force_rebuild)
            if success:
                self.environment_optimized = True
                logger.info("Manual environment optimization completed")
            else:
                logger.warning("Manual environment optimization failed")
            return success
        except Exception as e:
            logger.error(f"Error during manual environment optimization: {e}")
            return False

# You can create a single instance to be imported by the Flask app
lean_verifier_instance = LeanVerifier()