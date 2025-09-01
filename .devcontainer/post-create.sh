#!/bin/bash

# Robust error handling with automatic recovery
set -uo pipefail

# Function to log errors
log_error() {
    echo "❌ ERROR: $1" >&2
    echo "Last command exit code: $?" >&2
}

# Function to log success
log_success() {
    echo "✅ SUCCESS: $1"
}

# Function to log warnings
log_warning() {
    echo "⚠️  WARNING: $1"
}

# Enhanced error trap that continues execution
handle_error() {
    local exit_code=$?
    local line_number=$1
    log_error "Command failed at line $line_number (exit code: $exit_code). Attempting to continue..."
    return 0  # Continue execution instead of exiting
}

trap 'handle_error $LINENO' ERR

# Determine repository root reliably (postCreate runs from workspace root, but avoid hardcoding)
REPO_ROOT="$(pwd)"
LEAN_PROJECT_DIR="$REPO_ROOT/backend/lean_verifier"

echo "--- Fixing file permissions and cross-platform compatibility ---"
# Configure git for cross-platform development (handle line endings)
git config --global core.autocrlf input || log_warning "Could not configure git autocrlf"
git config --global core.safecrlf false || log_warning "Could not configure git safecrlf"

# Automatically fix common permission issues
chmod +x scripts/manage.sh 2>/dev/null || log_warning "Could not set permissions on scripts/manage.sh"
chmod +x .devcontainer/*.sh 2>/dev/null || log_warning "Could not set permissions on devcontainer scripts"
find scripts/ -name "*.sh" -exec chmod +x {} \; 2>/dev/null || log_warning "Could not set permissions on script files"

log_success "File permissions and git configuration updated"

echo "--- Installing elan (Lean's toolchain manager) ---"
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
. /home/vscode/.elan/env

echo "--- Configuring shell environment to make elan permanent ---"
# Configure for bash
if ! grep -q ". /home/vscode/.elan/env" /home/vscode/.bashrc; then
  echo -e "\n# Add Lean/Elan to the PATH\n. /home/vscode/.elan/env\n" >> /home/vscode/.bashrc
fi

# Also configure for zsh if it exists (common on macOS)
if [ -f "/home/vscode/.zshrc" ]; then
  if ! grep -q ". /home/vscode/.elan/env" /home/vscode/.zshrc; then
    echo -e "\n# Add Lean/Elan to the PATH\n. /home/vscode/.elan/env\n" >> /home/vscode/.zshrc
  fi
fi

# Ensure PATH is set for current session
export PATH="/home/vscode/.elan/bin:$PATH"

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

echo "--- Installing Rust toolchain and jixia (Lean static analyzer) ---"
# Ensure required build tools are present
if command -v apt-get >/dev/null 2>&1; then
  sudo apt-get update -y || log_warning "apt-get update failed"
  sudo apt-get install -y build-essential pkg-config libssl-dev curl || log_warning "apt-get install of build tools failed"
fi

# Install rustup/cargo if not present
if ! command -v cargo >/dev/null 2>&1; then
  echo "--- Installing rustup (non-interactive) ---"
  curl https://sh.rustup.rs -sSf | sh -s -- -y || log_warning "rustup install failed"
  if [ -f "/home/vscode/.cargo/env" ]; then
    . /home/vscode/.cargo/env
  fi
  # Persist cargo PATH in shells
  if ! grep -q ". /home/vscode/.cargo/env" /home/vscode/.bashrc 2>/dev/null; then
    echo -e "\n# Add Cargo to the PATH\n. /home/vscode/.cargo/env\n" >> /home/vscode/.bashrc
  fi
  if [ -f "/home/vscode/.zshrc" ] && ! grep -q ". /home/vscode/.cargo/env" /home/vscode/.zshrc 2>/dev/null; then
    echo -e "\n# Add Cargo to the PATH\n. /home/vscode/.cargo/env\n" >> /home/vscode/.zshrc
  fi
fi

# Install jixia if missing
if ! command -v jixia >/dev/null 2>&1; then
  echo "--- Installing jixia via cargo ---"
  cargo install jixia --locked || log_warning "cargo install jixia failed"
else
  echo "--- jixia already installed ---"
fi

echo "--- Setting up frontend dependencies ---"
cd "$REPO_ROOT/frontend"

# Clean install to avoid platform-specific issues
rm -f package-lock.json
rm -rf node_modules
log_success "Cleaned previous npm installation"

# Install all dependencies with multiple fallback strategies
echo "--- Installing npm dependencies (this may take a while) ---"
npm_success=false

# Strategy 1: Standard npm install with timeout
if timeout 300 npm install 2>/dev/null; then
    npm_success=true
    log_success "npm dependencies installed successfully"
fi

# Strategy 2: Try with --legacy-peer-deps
if [ "$npm_success" = false ]; then
    log_warning "Standard npm install failed, trying with --legacy-peer-deps..."
    if timeout 300 npm install --legacy-peer-deps 2>/dev/null; then
        npm_success=true
        log_success "npm dependencies installed with --legacy-peer-deps"
    fi
fi

# Strategy 3: Try without timeout
if [ "$npm_success" = false ]; then
    log_warning "Timed npm install failed, trying without timeout..."
    if npm install --legacy-peer-deps; then
        npm_success=true
        log_success "npm dependencies installed without timeout"
    fi
fi

# Strategy 4: Install core packages individually
if [ "$npm_success" = false ]; then
    log_warning "All npm install strategies failed, trying individual packages..."
    essential_packages="react@^19.1.0 react-dom@^19.1.0 react-router-dom@^7.7.1 vite tailwindcss postcss autoprefixer"
    for package in $essential_packages; do
        if npm install "$package"; then
            log_success "Installed $package"
        else
            log_warning "Failed to install $package, continuing..."
        fi
    done
    npm_success=true
    log_success "Individual npm package installation completed"
fi

# Verify and install any missing critical dependencies
if [ "$npm_success" = true ]; then
    # Try to install missing React dependencies
    npm list react react-dom react-router-dom > /dev/null 2>&1 || {
        log_warning "Some React dependencies missing, installing..."
        npm install react@^19.1.0 react-dom@^19.1.0 react-router-dom@^7.7.1 || log_warning "Could not install missing React dependencies"
    }

    # Try to install Tailwind CSS dependencies
    npm list tailwindcss postcss autoprefixer > /dev/null 2>&1 || {
        log_warning "Tailwind CSS dependencies missing, installing..."
        npm install -D tailwindcss postcss autoprefixer || log_warning "Could not install Tailwind CSS dependencies"
    }
fi

echo "--- Returning to workspace root ---"
cd "$REPO_ROOT"

# --- Always recreate venv inside the container ---
echo "--- Setting up Python virtual environment ---"
rm -rf .venv 2>/dev/null || true
if ! python3 -m venv .venv; then
    log_error "Failed to create virtual environment with python3, trying python..."
    if ! python -m venv .venv; then
        log_error "Virtual environment creation failed completely"
        # Continue anyway, try system Python
    fi
fi

# Try to activate virtual environment, fallback to system Python if needed
if [ -f ".venv/bin/activate" ]; then
    . .venv/bin/activate
    log_success "Virtual environment created and activated"
else
    log_warning "Virtual environment not created, using system Python"
fi

echo "--- Upgrading pip ---"
if ! pip install --upgrade pip; then
    log_warning "Pip upgrade failed, continuing with current version"
fi

echo "--- Installing Python dependencies (this may take a while) ---"
# Install core requirements with multiple fallback strategies
install_success=false

# Strategy 1: Normal installation with timeout
if timeout 300 pip install -r backend/requirements.txt 2>/dev/null; then
    install_success=true
    log_success "Core Python dependencies installed successfully"
fi

# Strategy 2: Install without timeout if first attempt failed
if [ "$install_success" = false ]; then
    log_warning "Timed installation failed, trying without timeout..."
    if pip install -r backend/requirements.txt; then
        install_success=true
        log_success "Core Python dependencies installed successfully (without timeout)"
    fi
fi

# Strategy 3: Install core packages individually if bulk install failed
if [ "$install_success" = false ]; then
    log_warning "Bulk installation failed, trying individual packages..."
    core_packages="flask flask-cors python-dotenv requests PyMuPDF pexpect tqdm requests_toolbelt google-cloud-aiplatform protobuf"
    for package in $core_packages; do
        if pip install "$package"; then
            log_success "Installed $package"
        else
            log_warning "Failed to install $package, continuing..."
        fi
    done
    install_success=true
    log_success "Individual package installation completed"
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

# --- Validate and repair critical Python packages ---
echo "--- Validating critical Python packages ---"
# Helper function to check package import and reinstall if broken
ensure_python_package() {
  local pkg_name="$1"      # e.g., google-cloud-aiplatform
  local import_path="$2"   # e.g., google.cloud.aiplatform
  if ! python - <<PY
import sys
try:
    __import__("$import_path")
except Exception as e:
    sys.exit(1)
PY
  then
    log_warning "Package '$pkg_name' failed import check, attempting clean reinstall..."
    pip uninstall -y "$pkg_name" >/dev/null 2>&1 || true
    if ! pip install --no-cache-dir --upgrade --force-reinstall "$pkg_name"; then
      log_warning "Reinstall of '$pkg_name' failed. Attempting one more time without cache..."
      pip install --no-cache-dir "$pkg_name" || log_warning "Final attempt to install '$pkg_name' failed."
    else
      log_success "Reinstalled '$pkg_name' successfully"
    fi
  else
    log_success "Validated package '$pkg_name'"
  fi
}

# Specifically validate google-cloud-aiplatform which can be partially installed if a timed install was interrupted
ensure_python_package "google-cloud-aiplatform" "google.cloud.aiplatform"

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

# --- Configure Vertex/GenAI env from gcloud (project/location) ---
echo "--- Configuring Vertex/GenAI environment ---"
PROJECT_ID=$(gcloud config get-value project 2>/dev/null || echo "")
LOCATION_DEFAULT="us-east1"
if [ -n "$PROJECT_ID" ]; then
  {
    echo "export GOOGLE_CLOUD_PROJECT=$PROJECT_ID"
    echo "export GOOGLE_CLOUD_LOCATION=${GOOGLE_CLOUD_LOCATION:-$LOCATION_DEFAULT}"
    echo "export VERTEX_AI_PROJECT_ID=$PROJECT_ID"
    echo "export VERTEX_AI_LOCATION=${VERTEX_AI_LOCATION:-$LOCATION_DEFAULT}"
  } >> /home/vscode/.bashrc

  if [ ! -f "$REPO_ROOT/backend/.env" ]; then
    {
      echo "VERTEX_AI_PROJECT_ID=$PROJECT_ID"
      echo "VERTEX_AI_LOCATION=${VERTEX_AI_LOCATION:-$LOCATION_DEFAULT}"
      echo "DEFAULT_LLM_MODEL=gemini-2.5-flash"
      echo "USE_GENAI=true"
    } > "$REPO_ROOT/backend/.env"
  fi
  log_success "Vertex/GenAI env configured (project=$PROJECT_ID, location=${VERTEX_AI_LOCATION:-$LOCATION_DEFAULT})"
else
  log_warning "No gcloud project set. Run on host: gcloud auth application-default login && gcloud config set project YOUR_PROJECT_ID"
fi

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"