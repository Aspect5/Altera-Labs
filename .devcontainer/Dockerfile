# Start from the official base image
FROM mcr.microsoft.com/devcontainers/base:ubuntu

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Explicitly set the system PATH. This is a critical step to ensure
# all subsequent commands and scripts can find the installed tools.
ENV PATH="/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

#
# === Install All Dependencies in a Single Layer ===
#
# By running all installations in a single RUN command, we make it less
# likely for Docker to use a partially correct cached layer.
#
USER root
RUN apt-get update && \
    # Install git, curl, and Node.js prerequisites
    apt-get install -y git curl build-essential && \
    # Install Node.js v20 for npm
    curl -fsSL https://deb.nodesource.com/setup_20.x | bash - && \
    apt-get install -y nodejs && \
    # Clean up APT caches to reduce the final image size
    rm -rf /var/lib/apt/lists/*

# Switch back to the default, non-root 'vscode' user for security
USER vscode