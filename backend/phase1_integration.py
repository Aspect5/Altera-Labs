# backend/phase1_integration.py

"""
Phase 1 Integration Module

This module integrates all Phase 1 optimization components:
- Specialized Prover Models (Action 1.1)
- Persistent Lean Server (Action 1.2) 
- Advanced Proof Caching (Action 1.3)

It provides a unified interface that can replace the current Vertex AI-based
tactic generation and verification system while maintaining backward compatibility.

This is the main integration point for Phase 1 of the optimization plan.
"""

import os
import logging
import time
from typing import Dict, Any, List, Optional, Tuple
from pathlib import Path

# Import Phase 1 components
from specialized_prover_models import prover_model_manager
from persistent_lean_server import lean_server
from advanced_proof_cache import advanced_proof_cache

# Import existing components for fallback
from socratic_auditor import get_llm_response

logger = logging.getLogger(__name__)

class Phase1OptimizedProver:
    """
    Phase 1 optimized theorem prover.
    
    This class integrates all Phase 1 optimizations to provide a unified
    interface for tactic generation and verification that significantly
    outperforms the current Vertex AI-based system.
    """
    
    def __init__(self, enable_fallback: bool = True):
        """
        Initialize the Phase 1 optimized prover.
        
        Args:
            enable_fallback: Whether to fall back to Vertex AI if specialized models fail
        """
        self.enable_fallback = enable_fallback
        self.initialized = False
        
        # Performance tracking
        self.stats = {
            'total_requests': 0,
            'specialized_model_requests': 0,
            'fallback_requests': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'avg_total_time': 0.0,
            'total_time': 0.0
        }
        
        # Initialize components
        self._initialize_components()
        
        logger.info("Phase 1 optimized prover initialized")
    
    def _initialize_components(self):
        """Initialize all Phase 1 components."""
        try:
            # Check if specialized models are available
            if prover_model_manager.models:
                logger.info("Specialized models available")
            else:
                logger.warning("No specialized models configured, will use fallback")
            
            # Test persistent Lean server
            test_result = lean_server.verify_tactic("refl", "1 = 1")
            if test_result.get('success'):
                logger.info("Persistent Lean server operational")
            else:
                logger.warning("Persistent Lean server test failed")
            
            # Test advanced cache
            cache_stats = advanced_proof_cache.get_stats()
            logger.info(f"Advanced cache operational: {cache_stats['total_cache_size']} entries")
            
            self.initialized = True
            
        except Exception as e:
            logger.error(f"Failed to initialize Phase 1 components: {e}")
            self.initialized = False
    
    def generate_and_verify_tactic(self, goal: str, context: str = "", max_attempts: int = 3) -> Dict[str, Any]:
        """
        Generate and verify a tactic using Phase 1 optimizations.
        
        This is the main method that replaces the current tactic generation
        and verification workflow.
        
        Args:
            goal: The goal to prove
            context: Additional context (imports, premises, etc.)
            max_attempts: Maximum number of generation attempts
            
        Returns:
            Comprehensive result including tactic, verification, and metadata
        """
        start_time = time.time()
        self.stats['total_requests'] += 1
        
        try:
            # Step 1: Check advanced cache first
            cached_result = self._check_cache(goal, context)
            if cached_result:
                self.stats['cache_hits'] += 1
                return self._format_result(cached_result, 'cache_hit', time.time() - start_time)
            
            self.stats['cache_misses'] += 1
            
            # Step 2: Generate tactic using specialized models
            tactic_result = self._generate_tactic_with_specialized_models(goal, context, max_attempts)
            
            if not tactic_result.get('tactic'):
                # Step 3: Fallback to Vertex AI if enabled
                if self.enable_fallback:
                    tactic_result = self._generate_tactic_with_fallback(goal, context)
                else:
                    return self._format_result({
                        'success': False,
                        'error': 'No specialized models available and fallback disabled'
                    }, 'specialized_failure', time.time() - start_time)
            
            # Step 4: Verify tactic using persistent server
            verification_result = self._verify_tactic_with_persistent_server(
                tactic_result['tactic'], goal, context
            )
            
            # Step 5: Cache the result
            self._cache_result(goal, context, verification_result)
            
            # Step 6: Format and return result
            total_time = time.time() - start_time
            self.stats['total_time'] += total_time
            self.stats['avg_total_time'] = self.stats['total_time'] / self.stats['total_requests']
            
            return self._format_result(verification_result, 'success', total_time, tactic_result)
            
        except Exception as e:
            total_time = time.time() - start_time
            logger.error(f"Error in generate_and_verify_tactic: {e}")
            return self._format_result({
                'success': False,
                'error': str(e)
            }, 'error', total_time)
    
    def _check_cache(self, goal: str, context: str) -> Optional[Dict[str, Any]]:
        """Check advanced cache for existing results."""
        try:
            # Extract premises from context for cache lookup
            premises = self._extract_premises_from_context(context)
            
            # Check monotonicity-aware cache
            cached_result = advanced_proof_cache.monotonicity_cache.get_cache_result(premises, goal)
            if cached_result:
                logger.debug("Cache hit for goal")
                return cached_result.get('result')
            
            return None
            
        except Exception as e:
            logger.warning(f"Cache check failed: {e}")
            return None
    
    def _generate_tactic_with_specialized_models(self, goal: str, context: str, max_attempts: int) -> Dict[str, Any]:
        """Generate tactic using specialized models."""
        self.stats['specialized_model_requests'] += 1
        
        try:
            if not prover_model_manager.models:
                return {'tactic': None, 'error': 'No specialized models available'}
            
            # Try multiple attempts with different models
            best_result = None
            best_confidence = 0.0
            
            for attempt in range(max_attempts):
                result = prover_model_manager.generate_tactic(goal, context)
                
                if result.get('tactic') and result.get('confidence', 0) > best_confidence:
                    best_result = result
                    best_confidence = result.get('confidence', 0)
                
                # If we got a high-confidence result, stop early
                if best_confidence > 0.8:
                    break
            
            return best_result or {'tactic': None, 'error': 'All specialized models failed'}
            
        except Exception as e:
            logger.error(f"Specialized model generation failed: {e}")
            return {'tactic': None, 'error': str(e)}
    
    def _generate_tactic_with_fallback(self, goal: str, context: str) -> Dict[str, Any]:
        """Generate tactic using Vertex AI fallback."""
        self.stats['fallback_requests'] += 1
        
        try:
            # Construct prompt for Vertex AI
            prompt = f"""
You are a theorem proving assistant for Lean 4. Generate a single, correct Lean 4 tactic.

Context:
{context}

Goal to prove:
{goal}

Generate a single Lean 4 tactic that will help prove this goal. Return only the tactic, nothing else.

Tactic:"""
            
            # Use existing Vertex AI integration
            response = get_llm_response(prompt)
            
            # Extract tactic from response
            tactic = self._extract_tactic_from_response(response)
            
            return {
                'tactic': tactic,
                'model': 'vertex_ai_fallback',
                'confidence': 0.5,  # Lower confidence for fallback
                'raw_response': response
            }
            
        except Exception as e:
            logger.error(f"Fallback generation failed: {e}")
            return {'tactic': None, 'error': str(e)}
    
    def _verify_tactic_with_persistent_server(self, tactic: str, goal: str, context: str) -> Dict[str, Any]:
        """Verify tactic using persistent Lean server."""
        try:
            # Extract imports from context
            imports = self._extract_imports_from_context(context)
            
            # Use persistent server for verification
            result = lean_server.verify_tactic(tactic, goal, imports)
            
            return result
            
        except Exception as e:
            logger.error(f"Persistent server verification failed: {e}")
            return {
                'success': False,
                'error': str(e),
                'verification_time': 0.0
            }
    
    def _cache_result(self, goal: str, context: str, result: Dict[str, Any]):
        """Cache the verification result."""
        try:
            # Extract premises for caching
            premises = self._extract_premises_from_context(context)
            
            if result.get('success', False):
                advanced_proof_cache.monotonicity_cache.cache_positive_result(
                    premises, goal, result
                )
            else:
                advanced_proof_cache.monotonicity_cache.cache_negative_result(
                    premises, goal, result
                )
                
        except Exception as e:
            logger.warning(f"Failed to cache result: {e}")
    
    def _extract_premises_from_context(self, context: str) -> set:
        """Extract premises from context string."""
        premises = set()
        
        # Simple extraction - could be enhanced
        lines = context.split('\n')
        for line in lines:
            line = line.strip()
            if (line.startswith('import ') or 
                line.startswith('theorem ') or 
                line.startswith('lemma ') or
                line.startswith('def ')):
                premises.add(line)
        
        return premises
    
    def _extract_imports_from_context(self, context: str) -> List[str]:
        """Extract import statements from context."""
        imports = []
        
        lines = context.split('\n')
        for line in lines:
            line = line.strip()
            if line.startswith('import '):
                imports.append(line)
        
        return imports if imports else ["import Mathlib"]
    
    def _extract_tactic_from_response(self, response: str) -> str:
        """Extract tactic from model response."""
        tactic = response.strip()
        
        # Remove common prefixes/suffixes
        tactic = tactic.replace("Tactic:", "").strip()
        tactic = tactic.replace("```lean", "").replace("```", "").strip()
        
        # Ensure it's a valid Lean tactic
        if not tactic or tactic.lower() in ["sorry", "admit"]:
            return "sorry"
        
        return tactic
    
    def _format_result(self, result: Dict[str, Any], result_type: str, 
                      total_time: float, tactic_result: Dict[str, Any] = None) -> Dict[str, Any]:
        """Format the final result with metadata."""
        formatted_result = {
            'success': result.get('success', False),
            'result_type': result_type,
            'total_time': total_time,
            'phase1_optimized': True,
            'timestamp': time.time()
        }
        
        if result.get('success'):
            formatted_result.update({
                'tactic': tactic_result.get('tactic') if tactic_result else None,
                'model_used': tactic_result.get('model') if tactic_result else 'unknown',
                'confidence': tactic_result.get('confidence', 0.0) if tactic_result else 0.0,
                'verification_time': result.get('verification_time', 0.0),
                'stdout': result.get('stdout', ''),
                'stderr': result.get('stderr', '')
            })
        else:
            formatted_result.update({
                'error': result.get('error', 'Unknown error'),
                'tactic': None
            })
        
        return formatted_result
    
    def verify_multiple_tactics(self, tactics: List[str], goal: str, context: str = "") -> List[Dict[str, Any]]:
        """
        Verify multiple tactics in parallel using speculative execution.
        
        Args:
            tactics: List of tactics to verify
            goal: The goal statement
            context: Additional context
            
        Returns:
            List of verification results
        """
        try:
            # Extract imports from context
            imports = self._extract_imports_from_context(context)
            
            # Use persistent server's parallel verification
            results = lean_server.verify_tactics_parallel(tactics, goal, imports)
            
            return results
            
        except Exception as e:
            logger.error(f"Parallel verification failed: {e}")
            return [{'success': False, 'error': str(e)} for _ in tactics]
    
    def get_comprehensive_stats(self) -> Dict[str, Any]:
        """Get comprehensive statistics from all Phase 1 components."""
        stats = {
            'phase1_optimized': True,
            'initialized': self.initialized,
            **self.stats
        }
        
        # Add specialized model stats
        if prover_model_manager.models:
            stats['specialized_models'] = prover_model_manager.get_stats()
        
        # Add persistent server stats
        stats['persistent_server'] = lean_server.get_stats()
        
        # Add advanced cache stats
        stats['advanced_cache'] = advanced_proof_cache.get_stats()
        
        return stats
    
    def cleanup(self):
        """Cleanup resources."""
        try:
            # Cleanup persistent server
            lean_server.shutdown()
            
            # Cleanup cache
            advanced_proof_cache.monotonicity_cache.cleanup_expired_entries()
            
            logger.info("Phase 1 components cleaned up")
            
        except Exception as e:
            logger.error(f"Cleanup failed: {e}")


# Global instance for easy access
phase1_prover = Phase1OptimizedProver()


# Backward compatibility functions
def verify_step_phase1(current_proof_state: str, natural_language_step: str) -> Dict[str, Any]:
    """
    Phase 1 optimized version of verify_step.
    
    This function provides the same interface as the existing verify_step
    but uses all Phase 1 optimizations for significantly better performance.
    """
    try:
        # Extract goal from proof state
        goal = _extract_goal_from_proof_state(current_proof_state)
        
        # Use Phase 1 prover
        result = phase1_prover.generate_and_verify_tactic(goal, current_proof_state)
        
        # Format result to match existing interface
        if result.get('success'):
            return {
                'success': True,
                'tactic': result.get('tactic'),
                'new_proof_state': _apply_tactic_to_proof_state(current_proof_state, result.get('tactic')),
                'explanation': f"Generated tactic '{result.get('tactic')}' using {result.get('model_used', 'specialized model')}",
                'phase1_optimized': True,
                'total_time': result.get('total_time', 0.0)
            }
        else:
            return {
                'success': False,
                'error': result.get('error', 'Unknown error'),
                'phase1_optimized': True,
                'total_time': result.get('total_time', 0.0)
            }
            
    except Exception as e:
        logger.error(f"Phase 1 verify_step failed: {e}")
        return {
            'success': False,
            'error': str(e),
            'phase1_optimized': True
        }


def _extract_goal_from_proof_state(proof_state: str) -> str:
    """Extract the current goal from proof state."""
    # Simple extraction - could be enhanced
    lines = proof_state.split('\n')
    for line in lines:
        if 'sorry' in line:
            # Look for the theorem/lemma statement
            for i in range(len(lines) - 1, -1, -1):
                if lines[i].startswith('theorem ') or lines[i].startswith('lemma '):
                    return lines[i].split(':', 1)[1].strip() if ':' in lines[i] else 'True'
    
    return 'True'  # Default goal


def _apply_tactic_to_proof_state(proof_state: str, tactic: str) -> str:
    """Apply a tactic to the proof state."""
    if not tactic or tactic == 'sorry':
        return proof_state
    
    # Replace the first 'sorry' with the tactic
    return proof_state.replace('sorry', f'by {tactic}\n  sorry', 1) 