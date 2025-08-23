@echo off
rem Windows batch script to detect gcloud configuration path
rem This runs on the Windows host before container build

echo 🔍 Detecting gcloud credentials on Windows...

rem Check if gcloud is installed
where gcloud >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ gcloud CLI not found in PATH
    echo.
    echo 📋 Please install Google Cloud CLI:
    echo    Download: https://dl.google.com/dl/cloudsdk/channels/rapid/GoogleCloudSDKInstaller.exe
    echo    Or run: powershell -c "(New-Object Net.WebClient).DownloadFile('https://dl.google.com/dl/cloudsdk/channels/rapid/GoogleCloudSDKInstaller.exe', '%TEMP%\GoogleCloudSDKInstaller.exe'); & '%TEMP%\GoogleCloudSDKInstaller.exe'"
    echo.
    echo After installation:
    echo 1. Run: gcloud init
    echo 2. Run: gcloud auth application-default login
    echo 3. Rebuild the dev container
    exit /b 1
)

rem Get the actual gcloud config directory
for /f "tokens=*" %%i in ('gcloud info --format="value(config.paths.global_config_dir)" 2^>nul') do set GCLOUD_CONFIG_DIR=%%i

if defined GCLOUD_CONFIG_DIR (
    echo ✅ gcloud config directory detected: %GCLOUD_CONFIG_DIR%
    
    rem Check for Application Default Credentials
    if exist "%GCLOUD_CONFIG_DIR%\application_default_credentials.json" (
        echo ✅ Application Default Credentials found
        echo 🚀 Ready for Vertex AI integration!
    ) else (
        echo ⚠️  No Application Default Credentials found
        echo    Run: gcloud auth application-default login
    )
    
    echo.
    echo 📋 gcloud config directory found at: %GCLOUD_CONFIG_DIR%
    echo    This will be automatically mounted in the dev container
    exit /b 0
) else (
    echo ⚠️  Could not determine gcloud config directory
    
    rem Check common Windows locations
    set FOUND=0
    
    if exist "%APPDATA%\gcloud" (
        echo ✅ Found gcloud config at: %APPDATA%\gcloud
        set FOUND=1
    )
    
    if exist "%USERPROFILE%\.config\gcloud" (
        echo ✅ Found gcloud config at: %USERPROFILE%\.config\gcloud
        set FOUND=1
    )
    
    if exist "%USERPROFILE%\AppData\Roaming\gcloud" (
        echo ✅ Found gcloud config at: %USERPROFILE%\AppData\Roaming\gcloud
        set FOUND=1
    )
    
    if %FOUND%==1 (
        echo 📋 gcloud credentials detected and will be mounted
        exit /b 0
    ) else (
        echo ❌ No gcloud configuration found
        echo.
        echo 🚀 Setup steps:
        echo 1. Install gcloud CLI: https://cloud.google.com/sdk/docs/install
        echo 2. Run: gcloud init
        echo 3. Run: gcloud auth application-default login
        echo 4. Rebuild the dev container
        exit /b 1
    )
)
