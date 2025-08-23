#!/bin/bash

# Cross-platform gcloud credentials detection and setup script
# Based on official Google Cloud CLI documentation

echo "🔍 Detecting gcloud credentials and platform..."

# Detect platform
if [[ "$OSTYPE" == "darwin"* ]]; then
    PLATFORM="macOS"
elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    PLATFORM="Linux"
elif [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "win32" ]]; then
    PLATFORM="Windows"
else
    PLATFORM="Unknown"
fi

echo "📱 Platform detected: $PLATFORM"

# Check for Mac/Linux path ($HOME/.config/gcloud)
if [ -d "$HOME/.config/gcloud" ]; then
    echo "✅ Found gcloud credentials at: $HOME/.config/gcloud"
    echo "   Standard Unix path detected"
    if [ -f "$HOME/.config/gcloud/application_default_credentials.json" ]; then
        echo "✅ Application Default Credentials found"
        echo "🚀 Ready for Vertex AI integration!"
    else
        echo "⚠️  ADC not found. Run: gcloud auth application-default login"
    fi
    exit 0
fi

# Check for Windows path (%APPDATA%\gcloud)
if [ -n "$APPDATA" ] && [ -d "$APPDATA/gcloud" ]; then
    echo "✅ Found gcloud credentials at: $APPDATA/gcloud"
    echo "   Windows APPDATA path detected"
    if [ -f "$APPDATA/gcloud/application_default_credentials.json" ]; then
        echo "✅ Application Default Credentials found"
        echo "🚀 Ready for Vertex AI integration!"
    else
        echo "⚠️  ADC not found. Run: gcloud auth application-default login"
    fi
    exit 0
fi

# Check alternative Windows paths
if [ -n "$USERPROFILE" ] && [ -d "$USERPROFILE/.config/gcloud" ]; then
    echo "✅ Found gcloud credentials at: $USERPROFILE/.config/gcloud"
    echo "   Windows alternative path detected"
    exit 0
fi

echo "❌ Google Cloud credentials not found!"
echo ""
echo "📋 Platform-specific setup instructions:"

case $PLATFORM in
    "macOS")
        echo "   🍎 macOS Installation:"
        echo "      1. Install via Homebrew: brew install google-cloud-sdk"
        echo "      2. Or download from: https://cloud.google.com/sdk/docs/install-sdk#mac"
        echo "      3. Run: gcloud init"
        echo "      4. Authenticate: gcloud auth application-default login"
        echo "      📁 Credentials will be stored at: ~/.config/gcloud"
        ;;
    "Linux")
        echo "   🐧 Linux Installation:"
        echo "      Ubuntu/Debian:"
        echo "        curl https://packages.cloud.google.com/apt/doc/apt-key.gpg | sudo gpg --dearmor -o /usr/share/keyrings/cloud.google.gpg"
        echo "        echo \"deb [signed-by=/usr/share/keyrings/cloud.google.gpg] https://packages.cloud.google.com/apt cloud-sdk main\" | sudo tee -a /etc/apt/sources.list.d/google-cloud-sdk.list"
        echo "        sudo apt-get update && sudo apt-get install google-cloud-cli"
        echo "      Or download archive from: https://cloud.google.com/sdk/docs/install-sdk#linux"
        echo "      📁 Credentials will be stored at: ~/.config/gcloud"
        ;;
    "Windows")
        echo "   🪟 Windows Installation:"
        echo "      1. Download installer: https://dl.google.com/dl/cloudsdk/channels/rapid/GoogleCloudSDKInstaller.exe"
        echo "      2. Or use PowerShell:"
        echo "         (New-Object Net.WebClient).DownloadFile(\"https://dl.google.com/dl/cloudsdk/channels/rapid/GoogleCloudSDKInstaller.exe\", \"\$env:Temp\\GoogleCloudSDKInstaller.exe\")"
        echo "         & \$env:Temp\\GoogleCloudSDKInstaller.exe"
        echo "      3. Run: gcloud init"
        echo "      4. Authenticate: gcloud auth application-default login"
        echo "      📁 Credentials will be stored at: %APPDATA%\\gcloud"
        ;;
    *)
        echo "   🔧 General Installation:"
        echo "      Visit: https://cloud.google.com/sdk/docs/install"
        ;;
esac

echo ""
echo "   🔑 After installation, authenticate with:"
echo "      gcloud auth application-default login"
echo ""
echo "   🔄 Then rebuild your dev container to mount the credentials"
echo ""
echo "🔗 Full documentation: https://cloud.google.com/sdk/docs/install"

exit 1
