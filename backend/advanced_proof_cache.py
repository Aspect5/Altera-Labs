# backend/advanced_proof_cache.py

"""
Advanced Proof Caching System

This module implements advanced caching strategies for formal logic as recommended
in the optimization plan. It includes monotonicity-aware caching for proven and
disproven statements, cache normalization, and sophisticated hit rate optimization.

Key Features:
- Monotonicity-aware proof caching (P-cache and N-cache)
- Cache normalization for logically equivalent states
- Standard caching patterns (Cache-Aside, Write-Through)
- Performance tracking and analytics

This is Action 1.3 of the optimization plan: Deploy Advanced Caching
"""

import hashlib
import pickle
import os
import json
import re
from typing import Dict, Any, Optional, List, Set, Tuple
from datetime import datetime, timedelta
from pathlib import Path
import logging
from collections import defaultdict

logger = logging.getLogger(__name__)

class MonotonicityAwareCache:
    """
    Monotonicity-aware cache for proof outcomes.
    
    This cache exploits the monotonicity property of classical logic:
    - If Γ₁ ⊢ G and Γ₁ ⊆ Γ₂, then Γ₂ ⊢ G (Positive cache)
    - If Γ₁ ⊬ G and Γ₂ ⊆ Γ₁, then Γ₂ ⊬ G (Negative cache)
    """
    
    def __init__(self, cache_dir: str = "cache", max_cache_size: int = 10000):
        """
        Initialize the monotonicity-aware cache.
        
        Args:
            cache_dir: Directory to store cache files
            max_cache_size: Maximum number of cache entries
        """
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)
        
        self.max_cache_size = max_cache_size
        
        # Positive cache: stores proven statements (Γ ⊢ G)
        self.positive_cache_file = self.cache_dir / "positive_cache.pkl"
        self.positive_cache = self._load_cache(self.positive_cache_file)
        
        # Negative cache: stores disproven statements (Γ ⊬ G)
        self.negative_cache_file = self.cache_dir / "negative_cache.pkl"
        self.negative_cache = self._load_cache(self.negative_cache_file)
        
        # Cache statistics
        self.stats = {
            'positive_hits': 0,
            'negative_hits': 0,
            'positive_misses': 0,
            'negative_misses': 0,
            'positive_saves': 0,
            'negative_saves': 0,
            'total_requests': 0,
            'normalization_hits': 0
        }
        
        logger.info(f"Advanced proof cache initialized with {len(self.positive_cache)} positive and {len(self.negative_cache)} negative entries")
    
    def _load_cache(self, cache_file: Path) -> Dict[str, Dict[str, Any]]:
        """Load cache from disk."""
        if cache_file.exists():
            try:
                with open(cache_file, 'rb') as f:
                    cache_data = pickle.load(f)
                    logger.info(f"Loaded {len(cache_data)} entries from {cache_file.name}")
                    return cache_data
            except Exception as e:
                logger.warning(f"Failed to load cache {cache_file.name}: {e}")
                return {}
        return {}
    
    def _save_cache(self, cache_data: Dict[str, Dict[str, Any]], cache_file: Path):
        """Save cache to disk with backup."""
        try:
            # Create backup of existing cache
            if cache_file.exists():
                backup_file = cache_file.with_suffix('.backup')
                cache_file.rename(backup_file)
            
            # Save new cache
            with open(cache_file, 'wb') as f:
                pickle.dump(cache_data, f)
            
            # Remove backup if save was successful
            if backup_file.exists():
                backup_file.unlink()
                
            logger.debug(f"Cache saved to {cache_file.name}")
        except Exception as e:
            logger.error(f"Failed to save cache {cache_file.name}: {e}")
            # Restore backup if save failed
            if backup_file.exists():
                backup_file.rename(cache_file)
    
    def _normalize_premises(self, premises: Set[str]) -> Set[str]:
        """
        Normalize premises for consistent caching.
        
        This function ensures that logically equivalent premise sets
        map to the same cache key.
        """
        normalized = set()
        
        for premise in premises:
            # Remove extra whitespace
            premise = re.sub(r'\s+', ' ', premise.strip())
            
            # Canonicalize variable names (simple approach)
            # This could be enhanced with more sophisticated normalization
            premise = re.sub(r'\b([a-z])\b', lambda m: m.group(1).lower(), premise)
            
            normalized.add(premise)
        
        return normalized
    
    def _generate_cache_key(self, premises: Set[str], goal: str) -> str:
        """
        Generate a cache key for a premise-goal pair.
        
        Args:
            premises: Set of premises (hypotheses)
            goal: Goal statement
            
        Returns:
            Normalized cache key
        """
        # Normalize premises
        normalized_premises = self._normalize_premises(premises)
        
        # Sort premises for consistent ordering
        sorted_premises = sorted(normalized_premises)
        
        # Normalize goal
        normalized_goal = re.sub(r'\s+', ' ', goal.strip())
        
        # Create cache key
        content = f"{'|'.join(sorted_premises)}|{normalized_goal}"
        return hashlib.md5(content.encode('utf-8')).hexdigest()
    
    def _is_superset(self, premises1: Set[str], premises2: Set[str]) -> bool:
        """
        Check if premises1 is a superset of premises2.
        
        Args:
            premises1: First set of premises
            premises2: Second set of premises
            
        Returns:
            True if premises1 ⊇ premises2
        """
        return premises2.issubset(premises1)
    
    def _is_subset(self, premises1: Set[str], premises2: Set[str]) -> bool:
        """
        Check if premises1 is a subset of premises2.
        
        Args:
            premises1: First set of premises
            premises2: Second set of premises
            
        Returns:
            True if premises1 ⊆ premises2
        """
        return premises1.issubset(premises2)
    
    def check_positive_cache(self, premises: Set[str], goal: str) -> Optional[Dict[str, Any]]:
        """
        Check positive cache for proven statements.
        
        Uses monotonicity: if Γ₁ ⊢ G and Γ₁ ⊆ Γ₂, then Γ₂ ⊢ G
        
        Args:
            premises: Current premise set
            goal: Goal to prove
            
        Returns:
            Cached result if found, None otherwise
        """
        self.stats['total_requests'] += 1
        
        # Check exact match first
        cache_key = self._generate_cache_key(premises, goal)
        if cache_key in self.positive_cache:
            self.stats['positive_hits'] += 1
            return self.positive_cache[cache_key]
        
        # Check for superset matches (monotonicity)
        for cached_key, cached_data in self.positive_cache.items():
            cached_premises = cached_data.get('premises', set())
            cached_goal = cached_data.get('goal', '')
            
            if (cached_goal == goal and 
                self._is_superset(premises, cached_premises)):
                
                self.stats['positive_hits'] += 1
                self.stats['normalization_hits'] += 1
                logger.debug(f"Positive cache hit via monotonicity: {len(cached_premises)} → {len(premises)} premises")
                return cached_data
        
        self.stats['positive_misses'] += 1
        return None
    
    def check_negative_cache(self, premises: Set[str], goal: str) -> Optional[Dict[str, Any]]:
        """
        Check negative cache for disproven statements.
        
        Uses monotonicity: if Γ₁ ⊬ G and Γ₂ ⊆ Γ₁, then Γ₂ ⊬ G
        
        Args:
            premises: Current premise set
            goal: Goal to prove
            
        Returns:
            Cached result if found, None otherwise
        """
        # Check exact match first
        cache_key = self._generate_cache_key(premises, goal)
        if cache_key in self.negative_cache:
            self.stats['negative_hits'] += 1
            return self.negative_cache[cache_key]
        
        # Check for subset matches (monotonicity)
        for cached_key, cached_data in self.negative_cache.items():
            cached_premises = cached_data.get('premises', set())
            cached_goal = cached_data.get('goal', '')
            
            if (cached_goal == goal and 
                self._is_subset(premises, cached_premises)):
                
                self.stats['negative_hits'] += 1
                self.stats['normalization_hits'] += 1
                logger.debug(f"Negative cache hit via monotonicity: {len(cached_premises)} → {len(premises)} premises")
                return cached_data
        
        self.stats['negative_misses'] += 1
        return None
    
    def cache_positive_result(self, premises: Set[str], goal: str, result: Dict[str, Any], ttl_hours: int = 24):
        """
        Cache a proven statement.
        
        Args:
            premises: Premise set that proves the goal
            goal: Goal that was proven
            result: Verification result
            ttl_hours: Time to live in hours
        """
        cache_key = self._generate_cache_key(premises, goal)
        
        cache_entry = {
            'premises': premises,
            'goal': goal,
            'result': result,
            'cached_at': datetime.now(),
            'expires_at': datetime.now() + timedelta(hours=ttl_hours),
            'cache_type': 'positive'
        }
        
        self.positive_cache[cache_key] = cache_entry
        self.stats['positive_saves'] += 1
        
        # Implement cache size management
        if len(self.positive_cache) > self.max_cache_size:
            self._evict_old_entries(self.positive_cache, 'positive')
        
        # Save to disk periodically
        if self.stats['positive_saves'] % 100 == 0:
            self._save_cache(self.positive_cache, self.positive_cache_file)
    
    def cache_negative_result(self, premises: Set[str], goal: str, result: Dict[str, Any], ttl_hours: int = 24):
        """
        Cache a disproven statement.
        
        Args:
            premises: Premise set that cannot prove the goal
            goal: Goal that could not be proven
            result: Verification result
            ttl_hours: Time to live in hours
        """
        cache_key = self._generate_cache_key(premises, goal)
        
        cache_entry = {
            'premises': premises,
            'goal': goal,
            'result': result,
            'cached_at': datetime.now(),
            'expires_at': datetime.now() + timedelta(hours=ttl_hours),
            'cache_type': 'negative'
        }
        
        self.negative_cache[cache_key] = cache_entry
        self.stats['negative_saves'] += 1
        
        # Implement cache size management
        if len(self.negative_cache) > self.max_cache_size:
            self._evict_old_entries(self.negative_cache, 'negative')
        
        # Save to disk periodically
        if self.stats['negative_saves'] % 100 == 0:
            self._save_cache(self.negative_cache, self.negative_cache_file)
    
    def _evict_old_entries(self, cache: Dict[str, Dict[str, Any]], cache_type: str):
        """Evict old entries to maintain cache size."""
        if len(cache) <= self.max_cache_size:
            return
        
        # Sort by creation time and remove oldest entries
        entries_by_time = sorted(
            cache.items(),
            key=lambda x: x[1].get('cached_at', datetime.min)
        )
        
        entries_to_remove = len(cache) - self.max_cache_size
        for i in range(entries_to_remove):
            key, _ = entries_by_time[i]
            del cache[key]
        
        logger.info(f"Evicted {entries_to_remove} old entries from {cache_type} cache")
    
    def cleanup_expired_entries(self):
        """Remove expired entries from both caches."""
        now = datetime.now()
        
        # Clean positive cache
        expired_keys = [
            key for key, entry in self.positive_cache.items()
            if entry.get('expires_at', datetime.max) < now
        ]
        for key in expired_keys:
            del self.positive_cache[key]
        
        # Clean negative cache
        expired_keys = [
            key for key, entry in self.negative_cache.items()
            if entry.get('expires_at', datetime.max) < now
        ]
        for key in expired_keys:
            del self.negative_cache[key]
        
        if expired_keys:
            logger.info(f"Cleaned up {len(expired_keys)} expired entries")
    
    def get_cache_result(self, premises: Set[str], goal: str) -> Optional[Dict[str, Any]]:
        """
        Get cached result for a premise-goal pair.
        
        This method checks both positive and negative caches using
        monotonicity properties.
        
        Args:
            premises: Set of premises
            goal: Goal to prove
            
        Returns:
            Cached result if found, None otherwise
        """
        # Check positive cache first
        positive_result = self.check_positive_cache(premises, goal)
        if positive_result:
            return positive_result
        
        # Check negative cache
        negative_result = self.check_negative_cache(premises, goal)
        if negative_result:
            return negative_result
        
        return None
    
    def get_stats(self) -> Dict[str, Any]:
        """Get comprehensive cache statistics."""
        total_hits = self.stats['positive_hits'] + self.stats['negative_hits']
        total_misses = self.stats['positive_misses'] + self.stats['negative_misses']
        total_requests = self.stats['total_requests']
        
        hit_rate = (total_hits / total_requests * 100) if total_requests > 0 else 0
        
        return {
            'positive_cache_size': len(self.positive_cache),
            'negative_cache_size': len(self.negative_cache),
            'total_cache_size': len(self.positive_cache) + len(self.negative_cache),
            'max_cache_size': self.max_cache_size,
            'hit_rate_percent': round(hit_rate, 2),
            'positive_hit_rate': round(self.stats['positive_hits'] / max(total_requests, 1) * 100, 2),
            'negative_hit_rate': round(self.stats['negative_hits'] / max(total_requests, 1) * 100, 2),
            'normalization_hits': self.stats['normalization_hits'],
            'total_requests': total_requests,
            'total_hits': total_hits,
            'total_misses': total_misses,
            **self.stats
        }
    
    def clear_cache(self, cache_type: str = 'all'):
        """Clear cache entries."""
        if cache_type in ['all', 'positive']:
            self.positive_cache.clear()
            if self.positive_cache_file.exists():
                self.positive_cache_file.unlink()
        
        if cache_type in ['all', 'negative']:
            self.negative_cache.clear()
            if self.negative_cache_file.exists():
                self.negative_cache_file.unlink()
        
        logger.info(f"Cleared {cache_type} cache")
    
    def export_cache_stats(self, filename: str = None) -> str:
        """Export cache statistics to a file."""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"cache_stats_{timestamp}.json"
        
        stats = self.get_stats()
        stats['exported_at'] = datetime.now().isoformat()
        
        export_path = self.cache_dir / filename
        with open(export_path, 'w') as f:
            json.dump(stats, f, indent=2, default=str)
        
        logger.info(f"Cache statistics exported to {export_path}")
        return str(export_path)


class AdvancedProofCache:
    """
    High-level interface for advanced proof caching.
    
    This class provides a unified interface for the monotonicity-aware cache
    and integrates with the existing proof verification system.
    """
    
    def __init__(self, cache_dir: str = "cache"):
        """Initialize the advanced proof cache."""
        self.monotonicity_cache = MonotonicityAwareCache(cache_dir)
        
        # Legacy cache for backward compatibility
        self.legacy_cache_file = Path(cache_dir) / "legacy_cache.pkl"
        self.legacy_cache = self._load_legacy_cache()
        
        logger.info("Advanced proof cache initialized")
    
    def _load_legacy_cache(self) -> Dict[str, Dict[str, Any]]:
        """Load legacy cache for backward compatibility."""
        if self.legacy_cache_file.exists():
            try:
                with open(self.legacy_cache_file, 'rb') as f:
                    return pickle.load(f)
            except Exception as e:
                logger.warning(f"Failed to load legacy cache: {e}")
        return {}
    
    def get_cached_result(self, tactic: str, goal: str, context: str = "") -> Optional[Dict[str, Any]]:
        """
        Get cached result for a proof attempt.
        
        This method checks both the advanced monotonicity cache and
        the legacy cache for backward compatibility.
        
        Args:
            tactic: The tactic used
            goal: The goal statement
            context: Additional context
            
        Returns:
            Cached result if found, None otherwise
        """
        # Extract premises from context
        premises = self._extract_premises_from_context(context)
        
        # Check advanced cache first
        advanced_result = self.monotonicity_cache.get_cache_result(premises, goal)
        if advanced_result:
            return advanced_result.get('result')
        
        # Fallback to legacy cache
        legacy_key = self._generate_legacy_key(tactic, goal, context)
        if legacy_key in self.legacy_cache:
            return self.legacy_cache[legacy_key]
        
        return None
    
    def cache_result(self, tactic: str, goal: str, result: Dict[str, Any], 
                    context: str = "", ttl_hours: int = 24) -> None:
        """
        Cache a proof result.
        
        Args:
            tactic: The tactic used
            goal: The goal statement
            result: The verification result
            context: Additional context
            ttl_hours: Time to live in hours
        """
        # Extract premises from context
        premises = self._extract_premises_from_context(context)
        
        # Cache in advanced system
        if result.get('success', False):
            self.monotonicity_cache.cache_positive_result(premises, goal, result, ttl_hours)
        else:
            self.monotonicity_cache.cache_negative_result(premises, goal, result, ttl_hours)
        
        # Also cache in legacy system for backward compatibility
        legacy_key = self._generate_legacy_key(tactic, goal, context)
        self.legacy_cache[legacy_key] = result
    
    def _extract_premises_from_context(self, context: str) -> Set[str]:
        """
        Extract premises from context string.
        
        Args:
            context: Context string containing premises
            
        Returns:
            Set of premises
        """
        premises = set()
        
        # Simple extraction - could be enhanced with more sophisticated parsing
        lines = context.split('\n')
        for line in lines:
            line = line.strip()
            if line.startswith('import ') or line.startswith('theorem ') or line.startswith('lemma '):
                premises.add(line)
        
        return premises
    
    def _generate_legacy_key(self, tactic: str, goal: str, context: str) -> str:
        """Generate legacy cache key for backward compatibility."""
        content = f"{tactic}|{goal}|{context}"
        return hashlib.md5(content.encode('utf-8')).hexdigest()
    
    def get_stats(self) -> Dict[str, Any]:
        """Get comprehensive cache statistics."""
        advanced_stats = self.monotonicity_cache.get_stats()
        legacy_stats = {
            'legacy_cache_size': len(self.legacy_cache),
            'legacy_cache_file': str(self.legacy_cache_file)
        }
        
        return {**advanced_stats, **legacy_stats}
    
    def clear_cache(self, cache_type: str = 'all'):
        """Clear cache entries."""
        self.monotonicity_cache.clear_cache(cache_type)
        
        if cache_type in ['all', 'legacy']:
            self.legacy_cache.clear()
            if self.legacy_cache_file.exists():
                self.legacy_cache_file.unlink()


# Global instance for easy access
advanced_proof_cache = AdvancedProofCache()

# Backward compatibility functions
def get_cached_proof_result(tactic: str, goal: str, context: str = "") -> Optional[Dict[str, Any]]:
    """Get cached proof result (backward compatibility)."""
    return advanced_proof_cache.get_cached_result(tactic, goal, context)

def cache_proof_result(tactic: str, goal: str, result: Dict[str, Any], 
                      context: str = "", ttl_hours: int = 24) -> None:
    """Cache proof result (backward compatibility)."""
    advanced_proof_cache.cache_result(tactic, goal, result, context, ttl_hours) 