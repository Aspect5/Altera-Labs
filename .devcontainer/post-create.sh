#!/bin/sh

# This script will exit immediately if any command fails.
set -e

echo "--- Installing elan (Lean's toolchain manager) ---"
# Install elan and add it to the path for the current script execution
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
. /home/vscode/.elan/env

# --- FIX: Make the elan environment permanent for all future terminals ---
echo "--- Configuring .bashrc to make elan environment permanent ---"
echo '' >> /home/vscode/.bashrc
echo '# Add Lean/Elan to the PATH' >> /home/vscode/.bashrc
echo '. /home/vscode/.elan/env' >> /home/vscode/.bashrc
echo '' >> /home/vscode/.bashrc

echo "--- Setting up Lean project in backend/lean_verifier ---"
# Create the directory structure
mkdir -p /workspaces/Altera-Labs/backend/lean_verifier
cd /workspaces/Altera-Labs/backend/lean_verifier

# Create the configuration files directly
echo "leanprover/lean4:v4.8.0-rc1" > lean-toolchain

echo '[package]
name = "lean_verifier"
version = "0.1.0"

[dependencies]
mathlib = {git = "https://github.com/leanprover-community/mathlib4"}' > lakefile.toml

# Create a dummy root file for the project to be valid
touch LeanVerifier.lean

echo "--- Building Lean project and fetching mathlib (this will take several minutes) ---"
lake build

echo "--- Setting up frontend dependencies ---"
cd /workspaces/Altera-Labs/frontend
npm install

# --- BEST PRACTICE: Install Python packages from a requirements file ---
echo "--- Setting up backend Python dependencies from requirements.txt ---"
pip install -r /workspaces/Altera-Labs/backend/requirements.txt

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"