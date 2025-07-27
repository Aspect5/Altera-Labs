#!/bin/bash

echo "=== Altera Labs Dev Container Rebuild Script ==="
echo "This script will help you rebuild the dev container if there are issues."

echo ""
echo "1. Stopping any running containers..."
docker stop $(docker ps -q --filter "ancestor=vsc-altera-labs") 2>/dev/null || true

echo ""
echo "2. Removing old containers..."
docker rm $(docker ps -aq --filter "ancestor=vsc-altera-labs") 2>/dev/null || true

echo ""
echo "3. Cleaning up Docker system..."
docker system prune -f

echo ""
echo "4. Rebuilding dev container..."
echo "Please follow these steps:"
echo "   a. In VS Code, press Cmd+Shift+P (or Ctrl+Shift+P on Windows/Linux)"
echo "   b. Type 'Dev Containers: Rebuild Container'"
echo "   c. Select 'Rebuild Container'"
echo "   d. Wait for the build to complete (this may take 5-10 minutes)"

echo ""
echo "5. If the rebuild fails, try these additional steps:"
echo "   a. Delete the .devcontainer/.devcontainer directory if it exists"
echo "   b. Restart VS Code"
echo "   c. Try rebuilding again"

echo ""
echo "6. Common troubleshooting:"
echo "   - Make sure Docker Desktop is running"
echo "   - Check that you have enough disk space"
echo "   - Ensure you have a stable internet connection"
echo "   - Try running 'docker system prune -a' to clean everything"

echo ""
echo "=== Rebuild script completed ===" 