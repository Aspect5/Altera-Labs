#!/bin/bash

echo "🚀 Rebuilding Altera Labs Dev Container with optimizations..."
echo "📋 This will create a new container with pre-installed Lean and Mathlib"
echo "⏱️  Estimated time: 2-3 minutes (much faster than before!)"

# Stop any running containers
echo "🛑 Stopping any running containers..."
docker stop $(docker ps -q --filter "name=vsc-altera-labs") 2>/dev/null || true

# Remove old containers and images
echo "🧹 Cleaning up old containers and images..."
docker rm $(docker ps -aq --filter "name=vsc-altera-labs") 2>/dev/null || true
docker rmi $(docker images -q "vsc-altera-labs*") 2>/dev/null || true

# Rebuild the dev container
echo "🔨 Rebuilding dev container..."
cd "$(dirname "$0")/.."

# Use Docker BuildKit for better caching
export DOCKER_BUILDKIT=1

# Rebuild the container
if docker build -f .devcontainer/Dockerfile -t vsc-altera-labs:latest .; then
    echo "✅ Container built successfully!"
    echo ""
    echo "🎉 Ready to start development!"
    echo "📝 To start the container:"
    echo "   1. Open VS Code"
    echo "   2. Press Cmd+Shift+P (or Ctrl+Shift+P)"
    echo "   3. Select 'Dev Containers: Reopen in Container'"
    echo ""
    echo "⚡ The container should now start much faster!"
else
    echo "❌ Container build failed!"
    exit 1
fi 