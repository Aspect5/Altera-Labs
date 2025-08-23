#!/bin/bash

# Script to detect the actual gcloud configuration path on the host system
# This script helps create the correct mount for Windows systems

echo "🔍 Detecting gcloud configuration path..."

# Function to check if gcloud is installed and get config path
get_gcloud_config_path() {
    if command -v gcloud >/dev/null 2>&1; then
        # Try to get the actual config directory from gcloud
        local config_path=$(gcloud info --format="value(config.paths.global_config_dir)" 2>/dev/null)
        if [ -n "$config_path" ] && [ -d "$config_path" ]; then
            echo "$config_path"
            return 0
        fi
    fi
    return 1
}

# Try to get the path from gcloud itself
GCLOUD_CONFIG_PATH=$(get_gcloud_config_path)

if [ -n "$GCLOUD_CONFIG_PATH" ]; then
    echo "✅ gcloud config directory detected: $GCLOUD_CONFIG_PATH"
    
    # Check for Application Default Credentials
    if [ -f "$GCLOUD_CONFIG_PATH/application_default_credentials.json" ]; then
        echo "✅ Application Default Credentials found"
    else
        echo "⚠️  No Application Default Credentials found"
        echo "   Run: gcloud auth application-default login"
    fi
    
    # Output the mount command for devcontainer.json
    echo ""
    echo "📋 Use this mount configuration in your devcontainer.json:"
    echo "\"source=$GCLOUD_CONFIG_PATH,target=/home/vscode/.config/gcloud,type=bind,consistency=cached\""
    
    exit 0
fi

# Fallback: Check common paths
echo "⚠️  Could not detect gcloud config path automatically"
echo "🔍 Checking common locations..."

POSSIBLE_PATHS=(
    "$HOME/.config/gcloud"
    "$APPDATA/gcloud" 
    "$USERPROFILE/.config/gcloud"
    "$USERPROFILE/AppData/Roaming/gcloud"
    "$LOCALAPPDATA/gcloud"
)

for path in "${POSSIBLE_PATHS[@]}"; do
    if [ -n "$path" ] && [ -d "$path" ]; then
        echo "✅ Found gcloud config at: $path"
        if [ -f "$path/application_default_credentials.json" ]; then
            echo "✅ Application Default Credentials found"
        fi
        echo "📋 Use this mount: \"source=$path,target=/home/vscode/.config/gcloud,type=bind,consistency=cached\""
        exit 0
    fi
done

echo "❌ No gcloud configuration found"
echo ""
echo "🚀 Setup steps:"
echo "1. Install gcloud CLI: https://cloud.google.com/sdk/docs/install"
echo "2. Run: gcloud init"
echo "3. Run: gcloud auth application-default login"
echo "4. Re-run this script to detect the path"

exit 1
