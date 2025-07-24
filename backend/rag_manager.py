# backend/rag_manager.py

"""
This module handles the storage and retrieval of user-uploaded documents,
acting as the first step in our Retrieval-Augmented Generation (RAG) pipeline.

In this initial version, it provides a simple file-based storage system.
In a production environment, this would be replaced with a more robust solution
like Google Cloud Storage and a vector database like Pinecone or Vertex AI Vector Search.
"""

import os
from pathlib import Path
import logging
from werkzeug.utils import secure_filename

# Use pathlib for robust, cross-platform path management.
BACKEND_DIR = Path(__file__).parent.resolve()
# Define a dedicated, git-ignored folder for user uploads.
UPLOAD_FOLDER = BACKEND_DIR / 'user_uploads'

# Ensure the upload directory exists.
try:
    UPLOAD_FOLDER.mkdir(parents=True, exist_ok=True)
except OSError as e:
    logging.critical(f"Could not create upload directory at {UPLOAD_FOLDER}. Check permissions. Error: {e}")

def save_assignment_file(user_id: str, file_storage) -> (str | None, str | None):
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
        
    # Sanitize the filename to prevent security issues like directory traversal.
    filename = secure_filename(file_storage.filename)
    
    # Create a dedicated folder for the user to prevent file conflicts.
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
        
        # In a future phase, this is where you would trigger the parsing of the
        # PDF/LaTeX and embed its content into a vector database.
        
        return str(file_path), None
    except Exception as e:
        logging.error(f"Failed to save file for user {user_id}. Error: {e}")
        return None, "Server error: Could not save file."

