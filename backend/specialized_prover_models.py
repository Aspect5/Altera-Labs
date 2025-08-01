# backend/specialized_prover_models.py

"""
Specialized Theorem Proving Models Integration

This module implements the integration with state-of-the-art specialized theorem proving
models as recommended in the optimization plan. It replaces the generic Vertex AI LLM
with models specifically trained for Lean 4 theorem proving.

Supported Models:
- BFS-Prover (ByteDance-Seed/BFS-Prover)
- Goedel-Prover (Goedel-LM/Goedel-Prover-SFT)
- DeepSeek-Prover V2 (future integration)

This is Action 1.1 of the optimization plan: Specialized Model Integration
"""

import os
import logging
import json
import requests
from typing import Dict, Any, List, Optional, Tuple
from pathlib import Path
import time
import hashlib

# Try to import Hugging Face transformers for local model hosting
try:
    import torch
    from transformers import AutoTokenizer, AutoModelForCausalLM
    TRANSFORMERS_AVAILABLE = True
except ImportError:
    TRANSFORMERS_AVAILABLE = False
    logging.warning("Transformers not available. Local model hosting disabled.")

logger = logging.getLogger(__name__)

class SpecializedProverModel:
    """
    Base class for specialized theorem proving models.
    
    This class provides a unified interface for different specialized models
    while allowing for model-specific optimizations and configurations.
    """
    
    def __init__(self, model_name: str, model_type: str = "huggingface"):
        """
        Initialize a specialized prover model.
        
        Args:
            model_name: Name/identifier of the model
            model_type: Type of model ("huggingface", "api", "local")
        """
        self.model_name = model_name
        self.model_type = model_type
        self.tokenizer = None
        self.model = None
        self.api_endpoint = None
        
        # Performance tracking
        self.stats = {
            'total_requests': 0,
            'successful_generations': 0,
            'failed_generations': 0,
            'avg_generation_time': 0.0,
            'total_generation_time': 0.0
        }
        
        logger.info(f"Initialized specialized prover model: {model_name} ({model_type})")
    
    def generate_tactic(self, goal: str, context: str = "", max_tokens: int = 512) -> Dict[str, Any]:
        """
        Generate a Lean 4 tactic for the given goal.
        
        Args:
            goal: The goal statement to prove
            context: Additional context (imports, premises, etc.)
            max_tokens: Maximum tokens to generate
            
        Returns:
            Dictionary containing the generated tactic and metadata
        """
        start_time = time.time()
        self.stats['total_requests'] += 1
        
        try:
            # Construct the prompt for the specialized model
            prompt = self._construct_prompt(goal, context)
            
            # Generate tactic based on model type
            if self.model_type == "huggingface":
                result = self._generate_huggingface(prompt, max_tokens)
            elif self.model_type == "api":
                result = self._generate_api(prompt, max_tokens)
            else:
                raise ValueError(f"Unsupported model type: {self.model_type}")
            
            # Extract tactic from result
            tactic = self._extract_tactic(result)
            
            generation_time = time.time() - start_time
            self.stats['successful_generations'] += 1
            self.stats['total_generation_time'] += generation_time
            self.stats['avg_generation_time'] = (
                self.stats['total_generation_time'] / self.stats['successful_generations']
            )
            
            return {
                'tactic': tactic,
                'model': self.model_name,
                'generation_time': generation_time,
                'confidence': self._calculate_confidence(result),
                'raw_response': result
            }
            
        except Exception as e:
            generation_time = time.time() - start_time
            self.stats['failed_generations'] += 1
            logger.error(f"Tactic generation failed: {e}")
            
            return {
                'tactic': None,
                'error': str(e),
                'model': self.model_name,
                'generation_time': generation_time
            }
    
    def _construct_prompt(self, goal: str, context: str = "") -> str:
        """
        Construct a prompt optimized for the specialized model.
        
        This method creates prompts that are specifically designed for
        theorem proving models, focusing on Lean 4 syntax and formal reasoning.
        """
        # Base prompt template for specialized models
        prompt_template = """You are a specialized theorem proving assistant for Lean 4. 
Your task is to generate a single, correct Lean 4 tactic that will help prove the given goal.

Context (imports and available lemmas):
{context}

Goal to prove:
{goal}

Generate a single Lean 4 tactic that will make progress toward proving this goal. 
Return only the tactic, nothing else. The tactic should be syntactically correct Lean 4.

Tactic:"""

        return prompt_template.format(
            context=context if context else "Standard Mathlib imports",
            goal=goal
        )
    
    def _generate_huggingface(self, prompt: str, max_tokens: int) -> str:
        """Generate tactic using local Hugging Face model."""
        if not TRANSFORMERS_AVAILABLE:
            raise RuntimeError("Transformers library not available")
        
        if self.tokenizer is None or self.model is None:
            raise RuntimeError("Model not loaded")
        
        # Tokenize input
        inputs = self.tokenizer(prompt, return_tensors="pt", truncation=True, max_length=2048)
        
        # Generate
        with torch.no_grad():
            outputs = self.model.generate(
                inputs.input_ids,
                max_new_tokens=max_tokens,
                temperature=0.3,
                top_p=0.95,
                do_sample=True,
                pad_token_id=self.tokenizer.eos_token_id
            )
        
        # Decode and extract generated text
        generated_text = self.tokenizer.decode(outputs[0], skip_special_tokens=True)
        return generated_text[len(prompt):].strip()
    
    def _generate_api(self, prompt: str, max_tokens: int) -> str:
        """Generate tactic using API endpoint."""
        if not self.api_endpoint:
            raise RuntimeError("API endpoint not configured")
        
        payload = {
            "prompt": prompt,
            "max_tokens": max_tokens,
            "temperature": 0.3,
            "top_p": 0.95
        }
        
        response = requests.post(
            self.api_endpoint,
            json=payload,
            timeout=30
        )
        response.raise_for_status()
        
        return response.json().get("generated_text", "")
    
    def _extract_tactic(self, response: str) -> str:
        """
        Extract the tactic from the model's response.
        
        This method handles different response formats and extracts
        the actual Lean 4 tactic.
        """
        # Clean up the response
        tactic = response.strip()
        
        # Remove common prefixes/suffixes
        tactic = tactic.replace("Tactic:", "").strip()
        tactic = tactic.replace("```lean", "").replace("```", "").strip()
        
        # Ensure it's a valid Lean tactic
        if not tactic or tactic.lower() in ["sorry", "admit"]:
            return "sorry"
        
        return tactic
    
    def _calculate_confidence(self, response: str) -> float:
        """
        Calculate confidence score for the generated tactic.
        
        This is a simple heuristic based on response characteristics.
        More sophisticated confidence estimation can be added later.
        """
        # Basic confidence calculation
        if not response or response.strip() == "":
            return 0.0
        
        # Check for common error patterns
        error_indicators = ["sorry", "admit", "error", "cannot", "unable"]
        if any(indicator in response.lower() for indicator in error_indicators):
            return 0.3
        
        # Check for valid tactic patterns
        valid_patterns = ["rw", "simp", "exact", "apply", "intro", "cases", "induction"]
        if any(pattern in response.lower() for pattern in valid_patterns):
            return 0.8
        
        return 0.5
    
    def get_stats(self) -> Dict[str, Any]:
        """Get performance statistics."""
        return {
            'model_name': self.model_name,
            'model_type': self.model_type,
            **self.stats
        }


class BFSProver(SpecializedProverModel):
    """
    BFS-Prover model integration.
    
    BFS-Prover is a high-performance model that achieves 72.95% success rate
    on MiniF2F benchmark using a simple Best-First Search algorithm.
    """
    
    def __init__(self, model_path: str = None, api_endpoint: str = None):
        """
        Initialize BFS-Prover.
        
        Args:
            model_path: Local path to the model (for Hugging Face)
            api_endpoint: API endpoint for the model
        """
        super().__init__("BFS-Prover", "huggingface" if model_path else "api")
        
        if model_path and TRANSFORMERS_AVAILABLE:
            self._load_huggingface_model(model_path)
        elif api_endpoint:
            self.api_endpoint = api_endpoint
            self.model_type = "api"
        else:
            # Fallback to API endpoint from environment
            self.api_endpoint = os.environ.get("BFS_PROVER_API_ENDPOINT")
            if not self.api_endpoint:
                raise ValueError("BFS-Prover requires either model_path or api_endpoint")
            self.model_type = "api"
    
    def _load_huggingface_model(self, model_path: str):
        """Load BFS-Prover from Hugging Face."""
        logger.info(f"Loading BFS-Prover from {model_path}")
        
        try:
            self.tokenizer = AutoTokenizer.from_pretrained(model_path)
            self.model = AutoModelForCausalLM.from_pretrained(
                model_path,
                torch_dtype=torch.float16,
                device_map="auto"
            )
            logger.info("BFS-Prover loaded successfully")
        except Exception as e:
            logger.error(f"Failed to load BFS-Prover: {e}")
            raise
    
    def _construct_prompt(self, goal: str, context: str = "") -> str:
        """
        BFS-Prover specific prompt construction.
        
        BFS-Prover is trained on state-tactic pairs and responds well to
        direct goal statements with minimal context.
        """
        return f"""Goal: {goal}

Generate a Lean 4 tactic to prove this goal:"""


class GoedelProver(SpecializedProverModel):
    """
    Goedel-Prover model integration.
    
    Goedel-Prover achieves 57.6% success rate on MiniF2F and ranks first
    on PutnamBench. It's particularly strong at whole-proof generation.
    """
    
    def __init__(self, model_path: str = None, api_endpoint: str = None):
        """
        Initialize Goedel-Prover.
        
        Args:
            model_path: Local path to the model (for Hugging Face)
            api_endpoint: API endpoint for the model
        """
        super().__init__("Goedel-Prover", "huggingface" if model_path else "api")
        
        if model_path and TRANSFORMERS_AVAILABLE:
            self._load_huggingface_model(model_path)
        elif api_endpoint:
            self.api_endpoint = api_endpoint
            self.model_type = "api"
        else:
            # Fallback to API endpoint from environment
            self.api_endpoint = os.environ.get("GOEDEL_PROVER_API_ENDPOINT")
            if not self.api_endpoint:
                raise ValueError("Goedel-Prover requires either model_path or api_endpoint")
            self.model_type = "api"
    
    def _load_huggingface_model(self, model_path: str):
        """Load Goedel-Prover from Hugging Face."""
        logger.info(f"Loading Goedel-Prover from {model_path}")
        
        try:
            self.tokenizer = AutoTokenizer.from_pretrained(model_path)
            self.model = AutoModelForCausalLM.from_pretrained(
                model_path,
                torch_dtype=torch.float16,
                device_map="auto"
            )
            logger.info("Goedel-Prover loaded successfully")
        except Exception as e:
            logger.error(f"Failed to load Goedel-Prover: {e}")
            raise
    
    def _construct_prompt(self, goal: str, context: str = "") -> str:
        """
        Goedel-Prover specific prompt construction.
        
        Goedel-Prover is trained on iterative self-improvement data and
        responds well to structured prompts with context.
        """
        return f"""Context:
{context}

Goal: {goal}

Generate a Lean 4 tactic to make progress on this goal:"""


class ProverModelManager:
    """
    Manager for multiple specialized prover models.
    
    This class handles model selection, fallback strategies, and
    ensemble methods for improved reliability.
    """
    
    def __init__(self):
        """Initialize the prover model manager."""
        self.models = {}
        self.primary_model = None
        self.fallback_models = []
        
        # Load models based on configuration
        self._load_configured_models()
    
    def _load_configured_models(self):
        """Load models based on environment configuration."""
        # Check for BFS-Prover configuration
        bfs_model_path = os.environ.get("BFS_PROVER_MODEL_PATH")
        bfs_api_endpoint = os.environ.get("BFS_PROVER_API_ENDPOINT")
        
        if bfs_model_path or bfs_api_endpoint:
            try:
                self.models["bfs"] = BFSProver(bfs_model_path, bfs_api_endpoint)
                self.primary_model = "bfs"
                logger.info("BFS-Prover loaded as primary model")
            except Exception as e:
                logger.error(f"Failed to load BFS-Prover: {e}")
        
        # Check for Goedel-Prover configuration
        goedel_model_path = os.environ.get("GOEDEL_PROVER_MODEL_PATH")
        goedel_api_endpoint = os.environ.get("GOEDEL_PROVER_API_ENDPOINT")
        
        if goedel_model_path or goedel_api_endpoint:
            try:
                self.models["goedel"] = GoedelProver(goedel_model_path, goedel_api_endpoint)
                if not self.primary_model:
                    self.primary_model = "goedel"
                else:
                    self.fallback_models.append("goedel")
                logger.info("Goedel-Prover loaded")
            except Exception as e:
                logger.error(f"Failed to load Goedel-Prover: {e}")
        
        if not self.models:
            logger.warning("No specialized models configured. Falling back to Vertex AI.")
    
    def generate_tactic(self, goal: str, context: str = "", max_attempts: int = 3) -> Dict[str, Any]:
        """
        Generate tactic using the best available model with fallback.
        
        Args:
            goal: The goal to prove
            context: Additional context
            max_attempts: Maximum number of attempts across models
            
        Returns:
            Best tactic generation result
        """
        if not self.models:
            raise RuntimeError("No specialized models available")
        
        best_result = None
        best_confidence = 0.0
        
        # Try primary model first
        if self.primary_model:
            result = self.models[self.primary_model].generate_tactic(goal, context)
            if result.get('tactic') and result.get('confidence', 0) > best_confidence:
                best_result = result
                best_confidence = result.get('confidence', 0)
        
        # Try fallback models
        for model_name in self.fallback_models:
            if max_attempts <= 1:
                break
            
            result = self.models[model_name].generate_tactic(goal, context)
            if result.get('tactic') and result.get('confidence', 0) > best_confidence:
                best_result = result
                best_confidence = result.get('confidence', 0)
            
            max_attempts -= 1
        
        return best_result or {
            'tactic': None,
            'error': 'All models failed to generate tactic',
            'model': 'ensemble'
        }
    
    def get_stats(self) -> Dict[str, Any]:
        """Get statistics from all models."""
        stats = {
            'total_models': len(self.models),
            'primary_model': self.primary_model,
            'fallback_models': self.fallback_models
        }
        
        for name, model in self.models.items():
            stats[name] = model.get_stats()
        
        return stats


# Global instance for easy access
prover_model_manager = ProverModelManager() 