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

echo "--- Setting up frontend dependencies ---"
cd "$WORKSPACE_ROOT/frontend"
npm install

echo "--- Returning to workspace root ---"
cd "$WORKSPACE_ROOT"

echo "--- Setting up backend Python dependencies ---"
pip install -r backend/requirements.txt

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"