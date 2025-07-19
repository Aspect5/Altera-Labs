#!/bin/bash

# This script will exit immediately if any command fails.
set -e

echo "--- Installing elan (Lean's toolchain manager) ---"
# Install elan for the vscode user
sudo -u vscode curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sudo -u vscode sh -s -- -y

# --- FIX: Create symbolic links in a system-wide directory ---
# This is a more robust way to ensure all processes can find the executables.
echo "--- Creating system-wide symbolic links for Lean tools ---"
sudo ln -s /home/vscode/.elan/bin/elan /usr/local/bin/elan
sudo ln -s /home/vscode/.elan/bin/lake /usr/local/bin/lake
sudo ln -s /home/vscode/.elan/bin/lean /usr/local/bin/lean

# Add elan to the PATH for the rest of this script's execution.
source /home/vscode/.elan/env

echo "--- Setting up Lean project in backend/lean_verifier ---"
# Navigate to the correct directory
cd /workspaces/Altera-Labs/backend

# Clean up any old attempts
rm -rf lean_verifier

# Create a fresh project as the 'vscode' user
sudo -u vscode lake new lean_verifier
cd lean_verifier

# Set the toolchain version
echo "leanprover/lean4:v4.8.0-rc1" > lean-toolchain

# Create the lakefile with the mathlib dependency
echo '[package]
name = "lean_verifier"
version = "0.1.0"

[dependencies]
mathlib = {git = "https://github.com/leanprover-community/mathlib4"}' > lakefile.toml

echo "--- Building Lean project and fetching mathlib (this will take several minutes) ---"
# Run the build as the 'vscode' user
sudo -u vscode lake build

echo "--- Setting up frontend dependencies ---"
cd /workspaces/Altera-Labs/frontend
npm install

# --- Install the VS Code extension at the end of the script ---
echo "--- Installing VS Code Lean 4 extension ---"
code --install-extension leanprover.lean4

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"
