# backend/developer_config.py

import json
import os
from typing import Dict, Any, List
from datetime import datetime
from pathlib import Path

class DeveloperConfig:
    """
    Configuration management for developer mode features.
    Handles settings, logging, and persistence of developer preferences.
    """
    
    def __init__(self, config_file: str = "developer_config.json"):
        self.config_file = Path(config_file)
        self.config = self._load_config()
        
    def _load_config(self) -> Dict[str, Any]:
        """Load configuration from file or create default."""
        default_config = {
            "developer_mode": False,
            "max_auto_solve_attempts": 5,
            "log_level": "INFO",
            "enable_detailed_logging": True,
            "save_attempt_logs": True,
            "auto_save_interval": 30,  # seconds
            "max_log_entries": 1000,
            "lean_timeout": 30,  # seconds
            "enable_error_parsing": True,
            "enable_llm_feedback": True
        }
        
        if self.config_file.exists():
            try:
                with open(self.config_file, 'r') as f:
                    loaded_config = json.load(f)
                    # Merge with defaults to ensure all keys exist
                    default_config.update(loaded_config)
                    return default_config
            except Exception as e:
                print(f"Failed to load developer config: {e}")
                return default_config
        else:
            # Create default config file
            self._save_config(default_config)
            return default_config
    
    def _save_config(self, config: Dict[str, Any]) -> None:
        """Save configuration to file."""
        try:
            with open(self.config_file, 'w') as f:
                json.dump(config, f, indent=2)
        except Exception as e:
            print(f"Failed to save developer config: {e}")
    
    def get(self, key: str, default: Any = None) -> Any:
        """Get a configuration value."""
        return self.config.get(key, default)
    
    def set(self, key: str, value: Any) -> None:
        """Set a configuration value and save to file."""
        self.config[key] = value
        self._save_config(self.config)
    
    def toggle_developer_mode(self) -> bool:
        """Toggle developer mode on/off."""
        current_mode = self.config.get("developer_mode", False)
        new_mode = not current_mode
        self.set("developer_mode", new_mode)
        return new_mode
    
    def set_developer_mode(self, enabled: bool) -> None:
        """Set developer mode explicitly."""
        self.set("developer_mode", enabled)
    
    def set_max_attempts(self, max_attempts: int) -> None:
        """Set maximum auto-solve attempts."""
        self.set("max_auto_solve_attempts", max_attempts)
    
    def get_all_settings(self) -> Dict[str, Any]:
        """Get all current settings."""
        return self.config.copy()
    
    def reset_to_defaults(self) -> None:
        """Reset all settings to defaults."""
        default_config = {
            "developer_mode": False,
            "max_auto_solve_attempts": 5,
            "log_level": "INFO",
            "enable_detailed_logging": True,
            "save_attempt_logs": True,
            "auto_save_interval": 30,
            "max_log_entries": 1000,
            "lean_timeout": 30,
            "enable_error_parsing": True,
            "enable_llm_feedback": True
        }
        self.config = default_config
        self._save_config(self.config)

class DeveloperLogger:
    """
    Enhanced logging for developer mode with attempt tracking and persistence.
    """
    
    def __init__(self, log_file: str = "developer_logs.json"):
        self.log_file = Path(log_file)
        self.logs = self._load_logs()
        self.max_entries = 1000
    
    def _load_logs(self) -> List[Dict[str, Any]]:
        """Load logs from file."""
        if self.log_file.exists():
            try:
                with open(self.log_file, 'r') as f:
                    return json.load(f)
            except Exception as e:
                print(f"Failed to load developer logs: {e}")
                return []
        return []
    
    def _save_logs(self) -> None:
        """Save logs to file."""
        try:
            with open(self.log_file, 'w') as f:
                json.dump(self.logs, f, indent=2)
        except Exception as e:
            print(f"Failed to save developer logs: {e}")
    
    def log_attempt(self, attempt_data: Dict[str, Any]) -> None:
        """Log an auto-solve attempt."""
        log_entry = {
            "timestamp": datetime.now().isoformat(),
            "type": "auto_solve_attempt",
            "data": attempt_data
        }
        
        self.logs.append(log_entry)
        
        # Trim old entries if we exceed max
        if len(self.logs) > self.max_entries:
            self.logs = self.logs[-self.max_entries:]
        
        self._save_logs()
    
    def log_error(self, error_data: Dict[str, Any]) -> None:
        """Log an error."""
        log_entry = {
            "timestamp": datetime.now().isoformat(),
            "type": "error",
            "data": error_data
        }
        
        self.logs.append(log_entry)
        
        if len(self.logs) > self.max_entries:
            self.logs = self.logs[-self.max_entries:]
        
        self._save_logs()
    
    def log_config_change(self, config_data: Dict[str, Any]) -> None:
        """Log a configuration change."""
        log_entry = {
            "timestamp": datetime.now().isoformat(),
            "type": "config_change",
            "data": config_data
        }
        
        self.logs.append(log_entry)
        
        if len(self.logs) > self.max_entries:
            self.logs = self.logs[-self.max_entries:]
        
        self._save_logs()
    
    def get_recent_logs(self, limit: int = 50) -> List[Dict[str, Any]]:
        """Get recent logs."""
        return self.logs[-limit:] if self.logs else []
    
    def get_logs_by_type(self, log_type: str) -> List[Dict[str, Any]]:
        """Get logs filtered by type."""
        return [log for log in self.logs if log.get("type") == log_type]
    
    def clear_logs(self) -> None:
        """Clear all logs."""
        self.logs = []
        self._save_logs()

# Global instances
developer_config = DeveloperConfig()
developer_logger = DeveloperLogger("config/developer_logs.json") 