# backend/test_phase1.py

"""
Phase 1 Test Script

This script tests the Phase 1 optimizations to ensure they are working correctly
and provides performance benchmarks compared to the current system.

Run this script to validate the Phase 1 implementation.
"""

import os
import sys
import time
import logging
from pathlib import Path

# Add the backend directory to the path
backend_dir = Path(__file__).parent
sys.path.insert(0, str(backend_dir))

# Import Phase 1 components
from phase1_config import setup_phase1_environment, get_phase1_status
from phase1_integration import phase1_prover, verify_step_phase1

# Import existing components for comparison
from socratic_auditor import verify_step as verify_step_original

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def test_phase1_setup():
    """Test Phase 1 setup and configuration."""
    print("=== Testing Phase 1 Setup ===")
    
    try:
        # Setup Phase 1 environment
        success = setup_phase1_environment()
        if success:
            print("✅ Phase 1 environment setup successful")
        else:
            print("❌ Phase 1 environment setup failed")
            return False
        
        # Get status
        status = get_phase1_status()
        print(f"Phase 1 enabled: {status['enabled']}")
        
        return True
        
    except Exception as e:
        print(f"❌ Phase 1 setup test failed: {e}")
        return False

def test_simple_proof():
    """Test a simple proof using Phase 1 optimizations."""
    print("\n=== Testing Simple Proof ===")
    
    # Simple proof state
    proof_state = """
import Mathlib

theorem simple_test : 1 + 1 = 2 := by
  sorry
"""
    
    goal = "1 + 1 = 2"
    
    try:
        # Test Phase 1 prover
        print("Testing Phase 1 prover...")
        start_time = time.time()
        result = phase1_prover.generate_and_verify_tactic(goal, proof_state)
        phase1_time = time.time() - start_time
        
        print(f"Phase 1 result: {result.get('success', False)}")
        print(f"Phase 1 time: {phase1_time:.2f}s")
        print(f"Tactic: {result.get('tactic', 'None')}")
        print(f"Model used: {result.get('model_used', 'None')}")
        
        return result.get('success', False)
        
    except Exception as e:
        print(f"❌ Simple proof test failed: {e}")
        return False

def test_cache_functionality():
    """Test the advanced caching functionality."""
    print("\n=== Testing Cache Functionality ===")
    
    goal = "2 + 2 = 4"
    context = "import Mathlib"
    
    try:
        # First request (cache miss)
        print("First request (should be cache miss)...")
        start_time = time.time()
        result1 = phase1_prover.generate_and_verify_tactic(goal, context)
        time1 = time.time() - start_time
        
        # Second request (should be cache hit)
        print("Second request (should be cache hit)...")
        start_time = time.time()
        result2 = phase1_prover.generate_and_verify_tactic(goal, context)
        time2 = time.time() - start_time
        
        print(f"First request time: {time1:.2f}s")
        print(f"Second request time: {time2:.2f}s")
        print(f"Cache speedup: {time1/time2:.1f}x")
        
        return time2 < time1  # Second request should be faster
        
    except Exception as e:
        print(f"❌ Cache test failed: {e}")
        return False

def test_parallel_verification():
    """Test parallel verification of multiple tactics."""
    print("\n=== Testing Parallel Verification ===")
    
    goal = "3 + 3 = 6"
    context = "import Mathlib"
    tactics = ["refl", "simp", "norm_num"]
    
    try:
        print(f"Testing parallel verification of {len(tactics)} tactics...")
        start_time = time.time()
        results = phase1_prover.verify_multiple_tactics(tactics, goal, context)
        parallel_time = time.time() - start_time
        
        print(f"Parallel verification time: {parallel_time:.2f}s")
        
        # Test sequential verification for comparison
        print("Testing sequential verification...")
        start_time = time.time()
        for tactic in tactics:
            phase1_prover.generate_and_verify_tactic(goal, context)
        sequential_time = time.time() - start_time
        
        print(f"Sequential verification time: {sequential_time:.2f}s")
        print(f"Parallel speedup: {sequential_time/parallel_time:.1f}x")
        
        return parallel_time < sequential_time
        
    except Exception as e:
        print(f"❌ Parallel verification test failed: {e}")
        return False

def test_performance_comparison():
    """Compare Phase 1 performance with original system."""
    print("\n=== Performance Comparison ===")
    
    proof_state = """
import Mathlib

theorem performance_test : 5 + 5 = 10 := by
  sorry
"""
    
    try:
        # Test Phase 1 system
        print("Testing Phase 1 system...")
        start_time = time.time()
        phase1_result = verify_step_phase1(proof_state, "prove this")
        phase1_time = time.time() - start_time
        
        # Test original system (if available)
        print("Testing original system...")
        start_time = time.time()
        original_result = verify_step_original(proof_state, "prove this", "homework")
        original_time = time.time() - start_time
        
        print(f"Phase 1 time: {phase1_time:.2f}s")
        print(f"Original time: {original_time:.2f}s")
        print(f"Performance improvement: {original_time/phase1_time:.1f}x")
        
        return phase1_time < original_time
        
    except Exception as e:
        print(f"❌ Performance comparison failed: {e}")
        return False

def test_comprehensive_stats():
    """Test comprehensive statistics collection."""
    print("\n=== Testing Statistics Collection ===")
    
    try:
        # Generate some activity
        goal = "1 = 1"
        context = "import Mathlib"
        
        for i in range(3):
            phase1_prover.generate_and_verify_tactic(goal, context)
        
        # Get comprehensive stats
        stats = phase1_prover.get_comprehensive_stats()
        
        print("Comprehensive Statistics:")
        print(f"  Total requests: {stats.get('total_requests', 0)}")
        print(f"  Specialized model requests: {stats.get('specialized_model_requests', 0)}")
        print(f"  Fallback requests: {stats.get('fallback_requests', 0)}")
        print(f"  Cache hits: {stats.get('cache_hits', 0)}")
        print(f"  Cache misses: {stats.get('cache_misses', 0)}")
        print(f"  Average total time: {stats.get('avg_total_time', 0):.2f}s")
        
        if 'persistent_server' in stats:
            server_stats = stats['persistent_server']
            print(f"  Active workers: {server_stats.get('active_workers', 0)}")
            print(f"  Idle workers: {server_stats.get('idle_workers', 0)}")
            print(f"  Worker creations: {server_stats.get('worker_creations', 0)}")
            print(f"  Worker reuses: {server_stats.get('worker_reuses', 0)}")
        
        if 'advanced_cache' in stats:
            cache_stats = stats['advanced_cache']
            print(f"  Positive cache size: {cache_stats.get('positive_cache_size', 0)}")
            print(f"  Negative cache size: {cache_stats.get('negative_cache_size', 0)}")
            print(f"  Hit rate: {cache_stats.get('hit_rate_percent', 0):.1f}%")
        
        return True
        
    except Exception as e:
        print(f"❌ Statistics test failed: {e}")
        return False

def run_all_tests():
    """Run all Phase 1 tests."""
    print("🚀 Starting Phase 1 Tests")
    print("=" * 50)
    
    tests = [
        ("Phase 1 Setup", test_phase1_setup),
        ("Simple Proof", test_simple_proof),
        ("Cache Functionality", test_cache_functionality),
        ("Parallel Verification", test_parallel_verification),
        ("Performance Comparison", test_performance_comparison),
        ("Statistics Collection", test_comprehensive_stats),
    ]
    
    results = []
    
    for test_name, test_func in tests:
        print(f"\n🧪 Running {test_name} test...")
        try:
            result = test_func()
            results.append((test_name, result))
            status = "✅ PASS" if result else "❌ FAIL"
            print(f"{status} - {test_name}")
        except Exception as e:
            print(f"❌ ERROR - {test_name}: {e}")
            results.append((test_name, False))
    
    # Summary
    print("\n" + "=" * 50)
    print("📊 Test Summary")
    print("=" * 50)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} - {test_name}")
    
    print(f"\nOverall: {passed}/{total} tests passed")
    
    if passed == total:
        print("🎉 All tests passed! Phase 1 is ready for deployment.")
    else:
        print("⚠️  Some tests failed. Please check the configuration and dependencies.")
    
    return passed == total

if __name__ == "__main__":
    # Check if we're in the right directory
    if not Path("lean_verifier").exists():
        print("❌ Error: lean_verifier directory not found. Please run from the backend directory.")
        sys.exit(1)
    
    # Run tests
    success = run_all_tests()
    
    # Exit with appropriate code
    sys.exit(0 if success else 1) 