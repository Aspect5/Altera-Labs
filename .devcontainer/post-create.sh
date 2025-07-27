#!/bin/sh

# Exit immediately if any command fails
set -e

echo "--- Installing elan (Lean's toolchain manager) ---"
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
. /home/vscode/.elan/env

echo "--- Configuring .bashrc to make elan environment permanent ---"
if ! grep -q ". /home/vscode/.elan/env" /home/vscode/.bashrc; then
  echo -e "\n# Add Lean/Elan to the PATH\n. /home/vscode/.elan/env\n" >> /home/vscode/.bashrc
fi

LEAN_PROJECT_DIR="/workspaces/Altera-Labs/backend/lean_verifier"
WORKSPACE_ROOT="/workspaces/Altera-Labs"

if [ ! -f "$LEAN_PROJECT_DIR/lakefile.toml" ]; then
    echo "--- Lean project not found. Initializing a new one... ---"
    cd "$WORKSPACE_ROOT/backend"
    lake new lean_verifier math
else
    echo "--- Lean project found. Using existing setup. ---"
fi

cd "$LEAN_PROJECT_DIR"
echo "--- Building Lean project (will be fast if dependencies are cached)... ---"
lake build

echo "--- Setting up root dependencies (Tailwind, PostCSS, etc.) ---"
cd "$WORKSPACE_ROOT"
npm install

echo "--- Setting up frontend dependencies ---"
cd "$WORKSPACE_ROOT/frontend"
npm install

echo "--- Returning to workspace root ---"
cd "$WORKSPACE_ROOT"

# --- Always recreate venv inside the container ---
rm -rf .venv
python3 -m venv .venv
. .venv/bin/activate
pip install --upgrade pip
pip install -r backend/requirements.txt
# Ensure .venv/bin/python3 exists for compatibility
if [ ! -f ".venv/bin/python3" ]; then
  ln -s python .venv/bin/python3
fi

# --- Auto-activate venv in every new terminal ---
VENV_ACTIVATE=". /workspaces/Altera-Labs/.venv/bin/activate"
for PROFILE in /home/vscode/.bashrc /home/vscode/.zshrc /home/vscode/.profile; do
  if ! grep -Fxq "$VENV_ACTIVATE" "$PROFILE" 2>/dev/null; then
    echo "$VENV_ACTIVATE" >> "$PROFILE"
  fi
done

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"