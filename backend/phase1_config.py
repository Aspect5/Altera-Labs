# backend/phase1_config.py

"""
Phase 1 Configuration

This module provides configuration management for Phase 1 optimizations,
including specialized model setup, persistent server configuration, and
advanced caching settings.

This allows easy deployment and management of the Phase 1 components.
"""

import os
import logging
from typing import Dict, Any, Optional
from pathlib import Path

logger = logging.getLogger(__name__)

class Phase1Config:
    """
    Configuration manager for Phase 1 optimizations.
    
    This class manages all configuration settings for the Phase 1 components
    and provides validation and setup utilities.
    """
    
    def __init__(self):
        """Initialize Phase 1 configuration."""
        self.config = self._load_config()
        self._validate_config()
    
    def _load_config(self) -> Dict[str, Any]:
        """Load configuration from environment variables and defaults."""
        config = {
            # Specialized Models Configuration
            'specialized_models': {
                'enabled': self._get_env_bool('PHASE1_SPECIALIZED_MODELS_ENABLED', True),
                'primary_model': os.environ.get('PHASE1_PRIMARY_MODEL', 'bfs'),
                'fallback_enabled': self._get_env_bool('PHASE1_FALLBACK_ENABLED', True),
                
                # BFS-Prover Configuration
                'bfs_prover': {
                    'enabled': self._get_env_bool('BFS_PROVER_ENABLED', False),
                    'model_path': os.environ.get('BFS_PROVER_MODEL_PATH'),
                    'api_endpoint': os.environ.get('BFS_PROVER_API_ENDPOINT'),
                    'max_tokens': int(os.environ.get('BFS_PROVER_MAX_TOKENS', '512')),
                    'temperature': float(os.environ.get('BFS_PROVER_TEMPERATURE', '0.3')),
                },
                
                # Goedel-Prover Configuration
                'goedel_prover': {
                    'enabled': self._get_env_bool('GOEDEL_PROVER_ENABLED', False),
                    'model_path': os.environ.get('GOEDEL_PROVER_MODEL_PATH'),
                    'api_endpoint': os.environ.get('GOEDEL_PROVER_API_ENDPOINT'),
                    'max_tokens': int(os.environ.get('GOEDEL_PROVER_MAX_TOKENS', '512')),
                    'temperature': float(os.environ.get('GOEDEL_PROVER_TEMPERATURE', '0.3')),
                }
            },
            
            # Persistent Server Configuration
            'persistent_server': {
                'enabled': self._get_env_bool('PHASE1_PERSISTENT_SERVER_ENABLED', True),
                'max_workers': int(os.environ.get('PHASE1_MAX_WORKERS', '4')),
                'max_cache_size': int(os.environ.get('PHASE1_MAX_CACHE_SIZE', '10')),
                'worker_timeout': int(os.environ.get('PHASE1_WORKER_TIMEOUT', '300')),
                'lean_project_path': os.environ.get('PHASE1_LEAN_PROJECT_PATH'),
            },
            
            # Advanced Cache Configuration
            'advanced_cache': {
                'enabled': self._get_env_bool('PHASE1_ADVANCED_CACHE_ENABLED', True),
                'cache_dir': os.environ.get('PHASE1_CACHE_DIR', 'cache'),
                'max_cache_size': int(os.environ.get('PHASE1_CACHE_MAX_SIZE', '10000')),
                'ttl_hours': int(os.environ.get('PHASE1_CACHE_TTL_HOURS', '24')),
                'cleanup_interval': int(os.environ.get('PHASE1_CACHE_CLEANUP_INTERVAL', '3600')),
            },
            
            # Performance Configuration
            'performance': {
                'speculative_execution': self._get_env_bool('PHASE1_SPECULATIVE_EXECUTION', True),
                'max_speculative_tactics': int(os.environ.get('PHASE1_MAX_SPECULATIVE_TACTICS', '3')),
                'parallel_verification': self._get_env_bool('PHASE1_PARALLEL_VERIFICATION', True),
                'max_parallel_workers': int(os.environ.get('PHASE1_MAX_PARALLEL_WORKERS', '4')),
            },
            
            # Monitoring and Logging
            'monitoring': {
                'enabled': self._get_env_bool('PHASE1_MONITORING_ENABLED', True),
                'stats_interval': int(os.environ.get('PHASE1_STATS_INTERVAL', '300')),
                'detailed_logging': self._get_env_bool('PHASE1_DETAILED_LOGGING', False),
            }
        }
        
        return config
    
    def _get_env_bool(self, key: str, default: bool) -> bool:
        """Get boolean value from environment variable."""
        value = os.environ.get(key, str(default)).lower()
        return value in ('true', '1', 'yes', 'on')
    
    def _validate_config(self):
        """Validate configuration settings."""
        errors = []
        
        # Validate specialized models
        if self.config['specialized_models']['enabled']:
            bfs_config = self.config['specialized_models']['bfs_prover']
            goedel_config = self.config['specialized_models']['goedel_prover']
            
            if not bfs_config['enabled'] and not goedel_config['enabled']:
                errors.append("At least one specialized model must be enabled")
            
            if bfs_config['enabled']:
                if not bfs_config['model_path'] and not bfs_config['api_endpoint']:
                    errors.append("BFS-Prover requires either model_path or api_endpoint")
            
            if goedel_config['enabled']:
                if not goedel_config['model_path'] and not goedel_config['api_endpoint']:
                    errors.append("Goedel-Prover requires either model_path or api_endpoint")
        
        # Validate persistent server
        if self.config['persistent_server']['enabled']:
            if self.config['persistent_server']['max_workers'] < 1:
                errors.append("max_workers must be at least 1")
            
            if self.config['persistent_server']['max_cache_size'] < 1:
                errors.append("max_cache_size must be at least 1")
        
        # Validate advanced cache
        if self.config['advanced_cache']['enabled']:
            if self.config['advanced_cache']['max_cache_size'] < 1:
                errors.append("cache max_cache_size must be at least 1")
        
        # Validate performance settings
        if self.config['performance']['max_speculative_tactics'] < 1:
            errors.append("max_speculative_tactics must be at least 1")
        
        if self.config['performance']['max_parallel_workers'] < 1:
            errors.append("max_parallel_workers must be at least 1")
        
        if errors:
            error_msg = "Phase 1 configuration errors:\n" + "\n".join(f"- {error}" for error in errors)
            logger.error(error_msg)
            raise ValueError(error_msg)
        
        logger.info("Phase 1 configuration validated successfully")
    
    def get_specialized_models_config(self) -> Dict[str, Any]:
        """Get specialized models configuration."""
        return self.config['specialized_models']
    
    def get_persistent_server_config(self) -> Dict[str, Any]:
        """Get persistent server configuration."""
        return self.config['persistent_server']
    
    def get_advanced_cache_config(self) -> Dict[str, Any]:
        """Get advanced cache configuration."""
        return self.config['advanced_cache']
    
    def get_performance_config(self) -> Dict[str, Any]:
        """Get performance configuration."""
        return self.config['performance']
    
    def get_monitoring_config(self) -> Dict[str, Any]:
        """Get monitoring configuration."""
        return self.config['monitoring']
    
    def is_phase1_enabled(self) -> bool:
        """Check if Phase 1 optimizations are enabled."""
        return (self.config['specialized_models']['enabled'] or 
                self.config['persistent_server']['enabled'] or 
                self.config['advanced_cache']['enabled'])
    
    def get_environment_variables(self) -> Dict[str, str]:
        """Get environment variables needed for Phase 1."""
        env_vars = {}
        
        # Specialized models
        if self.config['specialized_models']['enabled']:
            bfs_config = self.config['specialized_models']['bfs_prover']
            goedel_config = self.config['specialized_models']['goedel_prover']
            
            if bfs_config['enabled']:
                if bfs_config['model_path']:
                    env_vars['BFS_PROVER_MODEL_PATH'] = bfs_config['model_path']
                if bfs_config['api_endpoint']:
                    env_vars['BFS_PROVER_API_ENDPOINT'] = bfs_config['api_endpoint']
            
            if goedel_config['enabled']:
                if goedel_config['model_path']:
                    env_vars['GOEDEL_PROVER_MODEL_PATH'] = goedel_config['model_path']
                if goedel_config['api_endpoint']:
                    env_vars['GOEDEL_PROVER_API_ENDPOINT'] = goedel_config['api_endpoint']
        
        # Persistent server
        if self.config['persistent_server']['enabled']:
            if self.config['persistent_server']['lean_project_path']:
                env_vars['PHASE1_LEAN_PROJECT_PATH'] = self.config['persistent_server']['lean_project_path']
        
        # Advanced cache
        if self.config['advanced_cache']['enabled']:
            env_vars['PHASE1_CACHE_DIR'] = self.config['advanced_cache']['cache_dir']
        
        return env_vars
    
    def print_configuration_summary(self):
        """Print a summary of the current configuration."""
        print("=== Phase 1 Configuration Summary ===")
        
        # Specialized Models
        print(f"Specialized Models: {'Enabled' if self.config['specialized_models']['enabled'] else 'Disabled'}")
        if self.config['specialized_models']['enabled']:
            bfs_enabled = self.config['specialized_models']['bfs_prover']['enabled']
            goedel_enabled = self.config['specialized_models']['goedel_prover']['enabled']
            print(f"  - BFS-Prover: {'Enabled' if bfs_enabled else 'Disabled'}")
            print(f"  - Goedel-Prover: {'Enabled' if goedel_enabled else 'Disabled'}")
            print(f"  - Fallback to Vertex AI: {'Enabled' if self.config['specialized_models']['fallback_enabled'] else 'Disabled'}")
        
        # Persistent Server
        print(f"Persistent Server: {'Enabled' if self.config['persistent_server']['enabled'] else 'Disabled'}")
        if self.config['persistent_server']['enabled']:
            print(f"  - Max Workers: {self.config['persistent_server']['max_workers']}")
            print(f"  - Max Cache Size: {self.config['persistent_server']['max_cache_size']}")
        
        # Advanced Cache
        print(f"Advanced Cache: {'Enabled' if self.config['advanced_cache']['enabled'] else 'Disabled'}")
        if self.config['advanced_cache']['enabled']:
            print(f"  - Cache Directory: {self.config['advanced_cache']['cache_dir']}")
            print(f"  - Max Cache Size: {self.config['advanced_cache']['max_cache_size']}")
            print(f"  - TTL Hours: {self.config['advanced_cache']['ttl_hours']}")
        
        # Performance
        print(f"Performance Optimizations:")
        print(f"  - Speculative Execution: {'Enabled' if self.config['performance']['speculative_execution'] else 'Disabled'}")
        print(f"  - Parallel Verification: {'Enabled' if self.config['performance']['parallel_verification'] else 'Disabled'}")
        print(f"  - Max Speculative Tactics: {self.config['performance']['max_speculative_tactics']}")
        print(f"  - Max Parallel Workers: {self.config['performance']['max_parallel_workers']}")
        
        # Monitoring
        print(f"Monitoring: {'Enabled' if self.config['monitoring']['enabled'] else 'Disabled'}")
        if self.config['monitoring']['enabled']:
            print(f"  - Stats Interval: {self.config['monitoring']['stats_interval']}s")
            print(f"  - Detailed Logging: {'Enabled' if self.config['monitoring']['detailed_logging'] else 'Disabled'}")
        
        print("=====================================")


# Global configuration instance
phase1_config = Phase1Config()


def setup_phase1_environment():
    """
    Setup environment for Phase 1 optimizations.
    
    This function sets up the necessary environment variables and
    validates the configuration for Phase 1 components.
    """
    try:
        # Set environment variables
        env_vars = phase1_config.get_environment_variables()
        for key, value in env_vars.items():
            if key not in os.environ:
                os.environ[key] = value
        
        # Print configuration summary
        phase1_config.print_configuration_summary()
        
        logger.info("Phase 1 environment setup completed")
        return True
        
    except Exception as e:
        logger.error(f"Failed to setup Phase 1 environment: {e}")
        return False


def get_phase1_status() -> Dict[str, Any]:
    """
    Get the current status of Phase 1 optimizations.
    
    Returns:
        Dictionary containing status information
    """
    status = {
        'enabled': phase1_config.is_phase1_enabled(),
        'configuration': {
            'specialized_models': phase1_config.get_specialized_models_config(),
            'persistent_server': phase1_config.get_persistent_server_config(),
            'advanced_cache': phase1_config.get_advanced_cache_config(),
            'performance': phase1_config.get_performance_config(),
            'monitoring': phase1_config.get_monitoring_config(),
        }
    }
    
    return status 