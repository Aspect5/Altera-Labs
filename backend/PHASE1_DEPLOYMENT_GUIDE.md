# Phase 1 Deployment Guide

## Overview

This guide explains how to deploy the Phase 1 optimizations for the Altera Labs theorem proving system. Phase 1 implements the foundational upgrades outlined in the optimization plan:

- **Action 1.1**: Specialized Model Integration (BFS-Prover, Goedel-Prover)
- **Action 1.2**: Persistent Lean Server with LRU caching
- **Action 1.3**: Advanced Proof Caching with monotonicity awareness

## Prerequisites

### System Requirements

- Python 3.10+
- Lean 4 with Mathlib
- At least 8GB RAM (16GB recommended)
- GPU with 8GB+ VRAM (for local model hosting)

### Dependencies

Install the new dependencies:

```bash
cd backend
pip install -r requirements.txt
```

The new dependencies include:
- `torch>=2.0.0` - For local model hosting
- `transformers>=4.30.0` - For Hugging Face model integration
- `accelerate>=0.20.0` - For model optimization
- `sentencepiece>=0.1.99` - For tokenization
- `protobuf>=3.20.0` - For model serialization

## Configuration

### Environment Variables

Create a `.env` file in the backend directory with the following variables:

```bash
# Phase 1 General Configuration
PHASE1_SPECIALIZED_MODELS_ENABLED=true
PHASE1_PERSISTENT_SERVER_ENABLED=true
PHASE1_ADVANCED_CACHE_ENABLED=true
PHASE1_FALLBACK_ENABLED=true

# BFS-Prover Configuration
BFS_PROVER_ENABLED=true
BFS_PROVER_MODEL_PATH=/path/to/bfs-prover-model  # Optional: for local hosting
BFS_PROVER_API_ENDPOINT=https://your-bfs-prover-api.com  # Optional: for API hosting
BFS_PROVER_MAX_TOKENS=512
BFS_PROVER_TEMPERATURE=0.3

# Goedel-Prover Configuration
GOEDEL_PROVER_ENABLED=true
GOEDEL_PROVER_MODEL_PATH=/path/to/goedel-prover-model  # Optional: for local hosting
GOEDEL_PROVER_API_ENDPOINT=https://your-goedel-prover-api.com  # Optional: for API hosting
GOEDEL_PROVER_MAX_TOKENS=512
GOEDEL_PROVER_TEMPERATURE=0.3

# Persistent Server Configuration
PHASE1_MAX_WORKERS=4
PHASE1_MAX_CACHE_SIZE=10
PHASE1_WORKER_TIMEOUT=300
PHASE1_LEAN_PROJECT_PATH=/path/to/lean/project

# Advanced Cache Configuration
PHASE1_CACHE_DIR=cache
PHASE1_CACHE_MAX_SIZE=10000
PHASE1_CACHE_TTL_HOURS=24
PHASE1_CACHE_CLEANUP_INTERVAL=3600

# Performance Configuration
PHASE1_SPECULATIVE_EXECUTION=true
PHASE1_MAX_SPECULATIVE_TACTICS=3
PHASE1_PARALLEL_VERIFICATION=true
PHASE1_MAX_PARALLEL_WORKERS=4

# Monitoring Configuration
PHASE1_MONITORING_ENABLED=true
PHASE1_STATS_INTERVAL=300
PHASE1_DETAILED_LOGGING=false
```

### Model Setup Options

#### Option 1: Local Model Hosting (Recommended for Production)

1. **Download BFS-Prover**:
   ```bash
   # Using Hugging Face CLI
   huggingface-cli download ByteDance-Seed/BFS-Prover --local-dir /path/to/bfs-prover-model
   ```

2. **Download Goedel-Prover**:
   ```bash
   # Using Hugging Face CLI
   huggingface-cli download Goedel-LM/Goedel-Prover-SFT --local-dir /path/to/goedel-prover-model
   ```

3. **Update environment variables**:
   ```bash
   BFS_PROVER_MODEL_PATH=/path/to/bfs-prover-model
   GOEDEL_PROVER_MODEL_PATH=/path/to/goedel-prover-model
   ```

#### Option 2: API Endpoint Hosting

1. **Deploy models to a cloud service** (AWS, GCP, Azure)
2. **Set up API endpoints** for model inference
3. **Update environment variables**:
   ```bash
   BFS_PROVER_API_ENDPOINT=https://your-bfs-prover-api.com
   GOEDEL_PROVER_API_ENDPOINT=https://your-goedel-prover-api.com
   ```

#### Option 3: Fallback Only (Minimal Setup)

If you don't want to set up specialized models immediately:

```bash
PHASE1_SPECIALIZED_MODELS_ENABLED=false
PHASE1_FALLBACK_ENABLED=true
```

This will use the existing Vertex AI system as a fallback while still benefiting from the persistent server and advanced caching.

## Deployment Steps

### Step 1: Validate Configuration

Run the configuration validation:

```bash
cd backend
python -c "from phase1_config import setup_phase1_environment; setup_phase1_environment()"
```

This will:
- Validate all configuration settings
- Print a configuration summary
- Set up environment variables

### Step 2: Test Phase 1 Components

Run the comprehensive test suite:

```bash
cd backend
python test_phase1.py
```

This will test:
- Phase 1 setup and configuration
- Simple proof generation and verification
- Cache functionality
- Parallel verification
- Performance comparison with original system
- Statistics collection

### Step 3: Integration with Existing System

The Phase 1 components are designed to be backward compatible. You can integrate them gradually:

#### Option A: Gradual Integration

1. **Start with caching only**:
   ```python
   from advanced_proof_cache import advanced_proof_cache
   
   # Use advanced cache with existing system
   cached_result = advanced_proof_cache.get_cached_result(tactic, goal, context)
   ```

2. **Add persistent server**:
   ```python
   from persistent_lean_server import lean_server
   
   # Use persistent server for verification
   result = lean_server.verify_tactic(tactic, goal, imports)
   ```

3. **Add specialized models**:
   ```python
   from specialized_prover_models import prover_model_manager
   
   # Use specialized models for tactic generation
   result = prover_model_manager.generate_tactic(goal, context)
   ```

#### Option B: Full Integration

Replace the existing verification system with Phase 1:

```python
from phase1_integration import verify_step_phase1

# Use Phase 1 optimized verification
result = verify_step_phase1(proof_state, natural_language_step)
```

### Step 4: Update Flask App (Optional)

To integrate Phase 1 into the Flask app, add these endpoints:

```python
# Add to app.py
from phase1_integration import phase1_prover
from phase1_config import get_phase1_status

@app.route('/api/phase1/status', methods=['GET'])
def get_phase1_status_endpoint():
    """Get Phase 1 status and statistics."""
    return jsonify(get_phase1_status())

@app.route('/api/phase1/verify', methods=['POST'])
def phase1_verify_endpoint():
    """Phase 1 optimized verification endpoint."""
    data = request.get_json()
    goal = data.get('goal')
    context = data.get('context', '')
    
    result = phase1_prover.generate_and_verify_tactic(goal, context)
    return jsonify(result)

@app.route('/api/phase1/stats', methods=['GET'])
def get_phase1_stats_endpoint():
    """Get comprehensive Phase 1 statistics."""
    return jsonify(phase1_prover.get_comprehensive_stats())
```

## Performance Expectations

Based on the optimization plan, you should expect:

### Proof Success Rate
- **Current**: ~60%
- **Phase 1 Target**: 70-75%
- **Improvement**: +10-15%

### Average Proof Time
- **Current**: ~50-60 seconds
- **Phase 1 Target**: <28 seconds
- **Improvement**: 50-60% reduction

### Cache Hit Rate
- **Current**: 21.2%
- **Phase 1 Target**: 60-70%
- **Improvement**: +40-50%

## Monitoring and Maintenance

### Statistics Monitoring

The Phase 1 system provides comprehensive statistics:

```python
from phase1_integration import phase1_prover

# Get comprehensive stats
stats = phase1_prover.get_comprehensive_stats()

# Key metrics to monitor:
print(f"Total requests: {stats['total_requests']}")
print(f"Cache hit rate: {stats['advanced_cache']['hit_rate_percent']}%")
print(f"Average verification time: {stats['persistent_server']['avg_verification_time']:.2f}s")
print(f"Worker utilization: {stats['persistent_server']['active_workers']}/{stats['persistent_server']['total_workers']}")
```

### Cache Management

The advanced cache automatically manages itself, but you can manually control it:

```python
from advanced_proof_cache import advanced_proof_cache

# Clear cache
advanced_proof_cache.clear_cache()

# Export cache statistics
stats_file = advanced_proof_cache.monotonicity_cache.export_cache_stats()

# Cleanup expired entries
advanced_proof_cache.monotonicity_cache.cleanup_expired_entries()
```

### Worker Management

The persistent server automatically manages workers, but you can monitor them:

```python
from persistent_lean_server import lean_server

# Get server statistics
server_stats = lean_server.get_stats()

# Shutdown server (call during application shutdown)
lean_server.shutdown()
```

## Troubleshooting

### Common Issues

1. **"No specialized models available"**
   - Check that `BFS_PROVER_ENABLED=true` or `GOEDEL_PROVER_ENABLED=true`
   - Verify model paths or API endpoints are correct
   - Check that models are properly downloaded/accessible

2. **"Lean process failed to start"**
   - Verify Lean 4 is installed and accessible
   - Check `LAKE_EXECUTABLE_PATH` environment variable
   - Ensure Lean project path is correct

3. **"Cache not working"**
   - Check that `PHASE1_ADVANCED_CACHE_ENABLED=true`
   - Verify cache directory is writable
   - Check cache statistics for hit rates

4. **"Performance not improved"**
   - Run `test_phase1.py` to identify bottlenecks
   - Check that all components are enabled
   - Monitor statistics for cache hit rates and worker utilization

### Debug Mode

Enable detailed logging for debugging:

```bash
PHASE1_DETAILED_LOGGING=true
```

### Performance Profiling

Use the test script to profile performance:

```bash
python test_phase1.py
```

This will show detailed performance metrics and comparisons.

## Next Steps

After successfully deploying Phase 1:

1. **Monitor performance** for 1-2 weeks
2. **Collect feedback** from users
3. **Plan Phase 2** implementation (LeanDojo integration, Planner agent)
4. **Consider Phase 3** features (Corrector agent, custom fine-tuning)

## Support

For issues or questions:

1. Check the troubleshooting section above
2. Run the test suite to identify problems
3. Review the configuration validation output
4. Check the comprehensive statistics for insights

The Phase 1 implementation provides a solid foundation for the advanced features planned in Phase 2 and Phase 3 of the optimization plan. 