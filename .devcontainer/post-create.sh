#!/bin/bash

# Enhanced error handling
set -euo pipefail

# Function to log errors
log_error() {
    echo "❌ ERROR: $1" >&2
    echo "Last command exit code: $?" >&2
}

# Function to log success
log_success() {
    echo "✅ SUCCESS: $1"
}

# Trap errors and provide context
trap 'log_error "Command failed at line $LINENO. Check the output above for details."' ERR

# Determine repository root reliably (postCreate runs from workspace root, but avoid hardcoding)
REPO_ROOT="$(pwd)"
LEAN_PROJECT_DIR="$REPO_ROOT/backend/lean_verifier"

echo "--- Installing elan (Lean's toolchain manager) ---"
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
. /home/vscode/.elan/env

echo "--- Configuring .bashrc to make elan environment permanent ---"
if ! grep -q ". /home/vscode/.elan/env" /home/vscode/.bashrc; then
  echo -e "\n# Add Lean/Elan to the PATH\n. /home/vscode/.elan/env\n" >> /home/vscode/.bashrc
fi

if [ ! -f "$LEAN_PROJECT_DIR/lakefile.toml" ]; then
    echo "--- Lean project not found. Initializing a new one... ---"
    cd "$REPO_ROOT/backend"
    lake new lean_verifier math
else
    echo "--- Lean project found. Using existing setup. ---"
fi

cd "$LEAN_PROJECT_DIR"
echo "--- Building Lean project (will be fast if dependencies are cached)... ---"
lake build

echo "--- Setting up frontend dependencies ---"
cd "$REPO_ROOT/frontend"

# Clean install to avoid platform-specific issues
rm -f package-lock.json
rm -rf node_modules
log_success "Cleaned previous npm installation"

# Install all dependencies with timeout
echo "--- Installing npm dependencies (this may take a while) ---"
if ! timeout 300 npm install; then
    log_error "npm install failed or timed out. Trying with --legacy-peer-deps..."
    if ! timeout 300 npm install --legacy-peer-deps; then
        log_error "npm install failed completely. You may need to install dependencies manually."
        cd "$REPO_ROOT"
        echo "⚠️  Frontend dependencies failed to install. Run 'cd frontend && npm install' manually after container starts."
        # Don't exit, continue with backend setup
    else
        log_success "npm dependencies installed with --legacy-peer-deps"
    fi
else
    log_success "npm dependencies installed successfully"
    
    # Verify critical dependencies are installed, install if missing
    npm list react react-dom react-router-dom d3 > /dev/null 2>&1 || {
        echo "--- Installing missing React dependencies ---"
        npm install react@^19.1.0 react-dom@^19.1.0 react-router-dom@^7.7.1 d3@^7.9.0
        log_success "Missing React dependencies installed"
    }

    # Ensure Tailwind CSS is installed
    npm list tailwindcss postcss autoprefixer > /dev/null 2>&1 || {
        echo "--- Installing Tailwind CSS dependencies ---"
        npm install -D tailwindcss postcss autoprefixer
        log_success "Tailwind CSS dependencies installed"
    }
fi

echo "--- Returning to workspace root ---"
cd "$REPO_ROOT"

# --- Always recreate venv inside the container ---
echo "--- Setting up Python virtual environment ---"
rm -rf .venv
python3 -m venv .venv
. .venv/bin/activate
log_success "Virtual environment created and activated"

echo "--- Upgrading pip ---"
pip install --upgrade pip
log_success "Pip upgraded"

echo "--- Installing Python dependencies (this may take a while) ---"
# Install core requirements first
if ! timeout 300 pip install -r backend/requirements.txt; then
    log_error "Core dependencies installation failed or timed out."
    exit 1
else
    log_success "Core Python dependencies installed successfully"
fi

# Optionally install ML dependencies (commented out by default for faster builds)
if [ -f "backend/requirements-ml.txt" ] && [ "${INSTALL_ML_DEPS:-false}" = "true" ]; then
    echo "--- Installing ML dependencies (this will take several minutes) ---"
    if ! timeout 900 pip install -r backend/requirements-ml.txt; then
        log_error "ML dependencies installation failed or timed out."
        echo "⚠️  WARNING: ML dependencies failed to install. You can install them manually later with:"
        echo "    pip install -r backend/requirements-ml.txt"
    else
        log_success "ML dependencies installed successfully"
    fi
else
    echo "ℹ️  Skipping ML dependencies for faster container build. To install them:"
    echo "   Set INSTALL_ML_DEPS=true environment variable, or run manually:"
    echo "   pip install -r backend/requirements-ml.txt"
fi
# Ensure .venv/bin/python3 exists for compatibility
if [ ! -f ".venv/bin/python3" ]; then
  ln -s python .venv/bin/python3
fi

# --- Auto-activate venv in every new terminal ---
VENV_ACTIVATE=". $REPO_ROOT/.venv/bin/activate"
for PROFILE in /home/vscode/.bashrc /home/vscode/.zshrc /home/vscode/.profile; do
  if ! grep -Fxq "$VENV_ACTIVATE" "$PROFILE" 2>/dev/null; then
    echo "$VENV_ACTIVATE" >> "$PROFILE"
  fi
done

# --- Check Google Cloud credentials setup ---
echo "--- Checking Google Cloud credentials ---"
if [ -f "/home/vscode/.config/gcloud/application_default_credentials.json" ]; then
    log_success "Google Cloud credentials found and mounted successfully"
    echo "ℹ️  Vertex AI integration is ready to use"
elif [ -d "/home/vscode/.config/gcloud" ] && [ "$(ls -A /home/vscode/.config/gcloud 2>/dev/null)" ]; then
    log_success "Google Cloud configuration found"
    echo "ℹ️  You may need to run 'gcloud auth application-default login' on your host if you haven't already"
else
    echo "⚠️  WARNING: Google Cloud credentials not found in container"
    echo "📋 To fix this:"
    echo "   1. On your HOST machine (not in container), install gcloud CLI"
    echo "   2. Run: gcloud auth application-default login"
    echo "   3. Rebuild the dev container"
    echo ""
    echo "   This is REQUIRED for Vertex AI integration to work!"
fi

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"