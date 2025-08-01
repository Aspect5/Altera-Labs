# backend/persistent_lean_server.py

"""
Persistent Lean Server Implementation

This module implements a persistent, stateful server architecture for Lean 4 interaction
as recommended in the optimization plan. It replaces the current stateless verification
endpoint with a pool of persistent Lean REPL workers that are cached by their import headers.

Key Features:
- Persistent worker pool with LRU caching
- Environment caching by import headers
- Parallel verification capabilities
- Speculative execution support
- Automatic worker management

This is Action 1.2 of the optimization plan: Implement Persistent Lean Server
"""

import os
import logging
import subprocess
import threading
import time
import hashlib
import json
import queue
import tempfile
from typing import Dict, Any, List, Optional, Tuple, Set
from pathlib import Path
from dataclasses import dataclass
from datetime import datetime, timedelta
import asyncio
import concurrent.futures

logger = logging.getLogger(__name__)

@dataclass
class LeanWorker:
    """Represents a single Lean REPL worker process."""
    process: subprocess.Popen
    import_hash: str
    last_used: datetime
    is_busy: bool = False
    worker_id: str = None
    
    def __post_init__(self):
        if self.worker_id is None:
            self.worker_id = f"worker_{id(self)}"

@dataclass
class VerificationRequest:
    """Represents a verification request."""
    request_id: str
    tactic: str
    goal: str
    imports: List[str]
    priority: int = 0
    created_at: datetime = None
    
    def __post_init__(self):
        if self.created_at is None:
            self.created_at = datetime.now()

class PersistentLeanServer:
    """
    Persistent Lean server with worker pool management.
    
    This server maintains a pool of Lean REPL workers that are cached by their
    import headers, dramatically reducing startup time for verification tasks.
    """
    
    def __init__(self, 
                 max_workers: int = 4,
                 max_cache_size: int = 10,
                 worker_timeout: int = 300,
                 lean_project_path: str = None):
        """
        Initialize the persistent Lean server.
        
        Args:
            max_workers: Maximum number of concurrent workers
            max_cache_size: Maximum number of cached environments
            worker_timeout: Timeout for worker processes (seconds)
            lean_project_path: Path to the Lean project
        """
        self.max_workers = max_workers
        self.max_cache_size = max_cache_size
        self.worker_timeout = worker_timeout
        
        # Lean project configuration
        self.lean_project_path = Path(lean_project_path) if lean_project_path else Path(__file__).parent / "lean_verifier"
        self.lake_executable = os.getenv('LAKE_EXECUTABLE_PATH', 'lake')
        
        # Worker management
        self.workers: Dict[str, LeanWorker] = {}
        self.worker_pool: queue.Queue = queue.Queue()
        self.import_cache: Dict[str, List[str]] = {}
        
        # Request management
        self.request_queue: queue.PriorityQueue = queue.PriorityQueue()
        self.active_requests: Dict[str, VerificationRequest] = {}
        self.completed_requests: Dict[str, Dict[str, Any]] = {}
        
        # Performance tracking
        self.stats = {
            'total_requests': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'worker_creations': 0,
            'worker_reuses': 0,
            'avg_verification_time': 0.0,
            'total_verification_time': 0.0
        }
        
        # Threading
        self.lock = threading.RLock()
        self.shutdown_event = threading.Event()
        
        # Start worker management thread
        self.worker_thread = threading.Thread(target=self._worker_manager, daemon=True)
        self.worker_thread.start()
        
        logger.info(f"Persistent Lean server initialized with {max_workers} max workers")
    
    def _calculate_import_hash(self, imports: List[str]) -> str:
        """
        Calculate a hash for the import list.
        
        This hash is used as the key for caching workers with the same imports.
        """
        # Sort imports for consistent hashing
        sorted_imports = sorted(imports)
        import_string = "|".join(sorted_imports)
        return hashlib.md5(import_string.encode('utf-8')).hexdigest()
    
    def _create_lean_worker(self, imports: List[str]) -> LeanWorker:
        """
        Create a new Lean REPL worker with the specified imports.
        
        Args:
            imports: List of import statements
            
        Returns:
            Configured LeanWorker instance
        """
        import_hash = self._calculate_import_hash(imports)
        
        # Create a temporary Lean file with the imports
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False)
        try:
            # Write imports to the file
            for import_stmt in imports:
                temp_file.write(f"{import_stmt}\n")
            temp_file.write("\n-- Worker ready for verification\n")
            temp_file.flush()
            
            # Start Lean REPL process
            cmd = [self.lake_executable, "exec", "lean", "--run", temp_file.name]
            process = subprocess.Popen(
                cmd,
                cwd=self.lean_project_path,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1
            )
            
            # Wait for process to be ready
            time.sleep(2)  # Give Lean time to start
            
            if process.poll() is not None:
                raise RuntimeError("Lean process failed to start")
            
            worker = LeanWorker(
                process=process,
                import_hash=import_hash,
                last_used=datetime.now()
            )
            
            self.stats['worker_creations'] += 1
            logger.info(f"Created new Lean worker {worker.worker_id} with imports: {imports}")
            
            return worker
            
        finally:
            # Clean up temporary file
            try:
                os.unlink(temp_file.name)
            except:
                pass
    
    def _get_or_create_worker(self, imports: List[str]) -> LeanWorker:
        """
        Get an existing worker or create a new one for the given imports.
        
        Args:
            imports: List of import statements
            
        Returns:
            Available LeanWorker instance
        """
        import_hash = self._calculate_import_hash(imports)
        
        with self.lock:
            # Check if we have a cached worker with these imports
            for worker in self.workers.values():
                if (worker.import_hash == import_hash and 
                    not worker.is_busy and 
                    worker.process.poll() is None):
                    
                    worker.last_used = datetime.now()
                    worker.is_busy = True
                    self.stats['worker_reuses'] += 1
                    logger.debug(f"Reusing worker {worker.worker_id} for imports: {imports}")
                    return worker
            
            # Create new worker if we haven't reached the limit
            if len(self.workers) < self.max_workers:
                worker = self._create_lean_worker(imports)
                worker.is_busy = True
                self.workers[worker.worker_id] = worker
                return worker
            
            # Wait for a worker to become available
            logger.warning("All workers busy, waiting for availability")
            return None
    
    def _verify_with_worker(self, worker: LeanWorker, tactic: str, goal: str) -> Dict[str, Any]:
        """
        Verify a tactic using a specific worker.
        
        Args:
            worker: The LeanWorker to use
            tactic: The tactic to verify
            goal: The goal statement
            
        Returns:
            Verification result
        """
        start_time = time.time()
        
        try:
            # Construct the verification command
            verification_code = f"""
theorem test_verification : {goal} := by
  {tactic}
"""
            
            # Send to Lean process
            worker.process.stdin.write(verification_code + "\n")
            worker.process.stdin.flush()
            
            # Read response with timeout
            try:
                stdout, stderr = worker.process.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                worker.process.kill()
                worker.process.communicate()
                raise RuntimeError("Verification timed out")
            
            # Parse the result
            success = worker.process.returncode == 0
            result = {
                'success': success,
                'stdout': stdout,
                'stderr': stderr,
                'verification_time': time.time() - start_time
            }
            
            # Update statistics
            self.stats['total_verification_time'] += result['verification_time']
            self.stats['avg_verification_time'] = (
                self.stats['total_verification_time'] / self.stats['total_requests']
            )
            
            return result
            
        except Exception as e:
            logger.error(f"Verification failed for worker {worker.worker_id}: {e}")
            return {
                'success': False,
                'error': str(e),
                'verification_time': time.time() - start_time
            }
        finally:
            # Mark worker as available
            with self.lock:
                worker.is_busy = False
                worker.last_used = datetime.now()
    
    def verify_tactic(self, tactic: str, goal: str, imports: List[str] = None) -> Dict[str, Any]:
        """
        Verify a tactic against a goal.
        
        Args:
            tactic: The tactic to verify
            goal: The goal statement
            imports: List of import statements (defaults to standard Mathlib)
            
        Returns:
            Verification result
        """
        if imports is None:
            imports = ["import Mathlib"]
        
        self.stats['total_requests'] += 1
        
        # Get or create a worker
        worker = self._get_or_create_worker(imports)
        if worker is None:
            return {
                'success': False,
                'error': 'No available workers',
                'verification_time': 0.0
            }
        
        # Perform verification
        result = self._verify_with_worker(worker, tactic, goal)
        
        # Check if this was a cache hit
        import_hash = self._calculate_import_hash(imports)
        if import_hash in self.import_cache:
            self.stats['cache_hits'] += 1
        else:
            self.stats['cache_misses'] += 1
            self.import_cache[import_hash] = imports
        
        return result
    
    def verify_tactics_parallel(self, tactics: List[str], goal: str, imports: List[str] = None) -> List[Dict[str, Any]]:
        """
        Verify multiple tactics in parallel using speculative execution.
        
        Args:
            tactics: List of tactics to verify
            goal: The goal statement
            imports: List of import statements
            
        Returns:
            List of verification results
        """
        if imports is None:
            imports = ["import Mathlib"]
        
        # Create verification requests
        requests = []
        for i, tactic in enumerate(tactics):
            request = VerificationRequest(
                request_id=f"req_{time.time()}_{i}",
                tactic=tactic,
                goal=goal,
                imports=imports,
                priority=i  # Lower index = higher priority
            )
            requests.append(request)
        
        # Execute in parallel using thread pool
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(tactics), self.max_workers)) as executor:
            future_to_request = {
                executor.submit(self.verify_tactic, req.tactic, req.goal, req.imports): req
                for req in requests
            }
            
            results = []
            for future in concurrent.futures.as_completed(future_to_request):
                request = future_to_request[future]
                try:
                    result = future.result()
                    result['request_id'] = request.request_id
                    result['tactic'] = request.tactic
                    results.append(result)
                except Exception as e:
                    results.append({
                        'request_id': request.request_id,
                        'tactic': request.tactic,
                        'success': False,
                        'error': str(e)
                    })
        
        # Sort results by original order
        results.sort(key=lambda r: requests.index(next(req for req in requests if req.request_id == r['request_id'])))
        return results
    
    def _worker_manager(self):
        """
        Background thread for managing worker lifecycle.
        
        This thread handles:
        - Worker cleanup and recycling
        - Cache size management
        - Health monitoring
        """
        while not self.shutdown_event.is_set():
            try:
                with self.lock:
                    # Clean up dead workers
                    dead_workers = []
                    for worker_id, worker in self.workers.items():
                        if worker.process.poll() is not None:
                            dead_workers.append(worker_id)
                    
                    for worker_id in dead_workers:
                        del self.workers[worker_id]
                        logger.info(f"Removed dead worker {worker_id}")
                    
                    # Manage cache size
                    if len(self.workers) > self.max_cache_size:
                        # Remove least recently used workers
                        workers_by_lru = sorted(
                            self.workers.items(),
                            key=lambda x: x[1].last_used
                        )
                        
                        workers_to_remove = len(self.workers) - self.max_cache_size
                        for i in range(workers_to_remove):
                            worker_id, worker = workers_by_lru[i]
                            if not worker.is_busy:
                                worker.process.terminate()
                                del self.workers[worker_id]
                                logger.info(f"Removed LRU worker {worker_id}")
                
                # Sleep before next check
                time.sleep(10)
                
            except Exception as e:
                logger.error(f"Error in worker manager: {e}")
                time.sleep(5)
    
    def get_stats(self) -> Dict[str, Any]:
        """Get server statistics."""
        with self.lock:
            return {
                'active_workers': len([w for w in self.workers.values() if w.is_busy]),
                'idle_workers': len([w for w in self.workers.values() if not w.is_busy]),
                'total_workers': len(self.workers),
                'cache_size': len(self.import_cache),
                'max_workers': self.max_workers,
                'max_cache_size': self.max_cache_size,
                **self.stats
            }
    
    def shutdown(self):
        """Shutdown the server and clean up workers."""
        logger.info("Shutting down persistent Lean server")
        self.shutdown_event.set()
        
        with self.lock:
            for worker in self.workers.values():
                try:
                    worker.process.terminate()
                    worker.process.wait(timeout=5)
                except:
                    worker.process.kill()
        
        logger.info("Persistent Lean server shutdown complete")


# Global instance for easy access
lean_server = PersistentLeanServer() 