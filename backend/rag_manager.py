# backend/rag_manager.py

"""
This module handles the storage and retrieval of user-uploaded documents,
acting as the first step in our Retrieval-Augmented Generation (RAG) pipeline.
"""

import os
from pathlib import Path
import logging
from werkzeug.utils import secure_filename
from typing import Tuple # Import Tuple for type hinting

# Use pathlib for robust, cross-platform path management.
BACKEND_DIR = Path(__file__).parent.resolve()
UPLOAD_FOLDER = BACKEND_DIR / 'user_uploads'

try:
    UPLOAD_FOLDER.mkdir(parents=True, exist_ok=True)
except OSError as e:
    logging.critical(f"Could not create upload directory at {UPLOAD_FOLDER}. Check permissions. Error: {e}")

def save_assignment_file(user_id: str, file_storage) -> Tuple[str | None, str | None]:
    """
    Saves an uploaded assignment file securely for a specific user.

    Args:
        user_id (str): The unique identifier for the user.
        file_storage: The file object from the Flask request (e.g., request.files['file']).

    Returns:
        A tuple containing:
        - str | None: The full path to the saved file on success, None on failure.
        - str | None: An error message on failure, None on success.
    """
    if not user_id or not file_storage or not file_storage.filename:
        return None, "Invalid user ID or file provided."
        
    filename = secure_filename(file_storage.filename)
    user_folder = UPLOAD_FOLDER / user_id
    try:
        user_folder.mkdir(exist_ok=True)
    except OSError as e:
        logging.error(f"Could not create user directory {user_folder}. Error: {e}")
        return None, "Server error: Could not create user directory."

    try:
        file_path = user_folder / filename
        file_storage.save(file_path)
        logging.info(f"Successfully saved file for user {user_id} at {file_path}")
        return str(file_path), None
    except Exception as e:
        logging.error(f"Failed to save file for user {user_id}. Error: {e}")
        return None, "Server error: Could not save file."
