#!/bin/sh

# This script will exit immediately if any command fails.
set -e

echo "--- Installing elan (Lean's toolchain manager) ---"
# The script is already running as the 'vscode' user, so no 'sudo' is needed.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# --- FIX: Use '.' instead of 'source' for POSIX shell compatibility ---
# This loads the elan environment variables into the current script's session.
. /home/vscode/.elan/env

echo "--- Setting up Lean project in backend/lean_verifier ---"
# Navigate to the correct directory
cd /workspaces/Altera-Labs/backend

# Clean up any old attempts
rm -rf lean_verifier

# Create a fresh project
lake new lean_verifier
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
# Run the build
lake build

echo "--- Setting up frontend dependencies ---"
cd /workspaces/Altera-Labs/frontend
npm install

# --- Install the VS Code extension at the end of the script ---
echo "--- Installing VS Code Lean 4 extension ---"
code --install-extension leanprover.lean4

echo "--- ✅✅✅ Dev Container setup complete! ✅✅✅ ---"
