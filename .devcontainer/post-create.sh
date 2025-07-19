#!/bin/bash

# This script will exit immediately if any command fails.
set -e

echo "--- Installing elan (Lean's toolchain manager) ---"
# We add 'sudo' because we are in a clean container and need permissions.
sudo -u vscode curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sudo -u vscode sh -s -- -y

# Add elan to the PATH for the rest of the script
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

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"

