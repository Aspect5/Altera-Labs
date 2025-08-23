#!/usr/bin/env node

/**
 * Cross-platform gcloud detection script
 * This runs on the host system before container build
 */

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const os = require('os');

console.log('🔍 Detecting gcloud credentials...');

// Detect platform
const platform = os.platform();
console.log(`📱 Platform detected: ${platform}`);

// Function to check if command exists
function commandExists(command) {
    try {
        const cmd = platform === 'win32' ? `where ${command}` : `which ${command}`;
        execSync(cmd, { stdio: 'ignore' });
        return true;
    } catch {
        return false;
    }
}

// Function to get gcloud config directory
function getGcloudConfigDir() {
    try {
        const output = execSync('gcloud info --format="value(config.paths.global_config_dir)"', { 
            encoding: 'utf8',
            stdio: ['ignore', 'pipe', 'ignore']
        });
        return output.trim();
    } catch {
        return null;
    }
}

// Function to check if directory exists
function dirExists(dirPath) {
    try {
        return fs.statSync(dirPath).isDirectory();
    } catch {
        return false;
    }
}

// Function to check if file exists
function fileExists(filePath) {
    try {
        return fs.statSync(filePath).isFile();
    } catch {
        return false;
    }
}

// Main logic
function main() {
    // Check if gcloud is installed
    if (!commandExists('gcloud')) {
        console.log('❌ gcloud CLI not found in PATH');
        console.log('');
        console.log('📋 Platform-specific installation:');
        
        if (platform === 'win32') {
            console.log('   Windows:');
            console.log('   Download: https://dl.google.com/dl/cloudsdk/channels/rapid/GoogleCloudSDKInstaller.exe');
        } else if (platform === 'darwin') {
            console.log('   macOS:');
            console.log('   brew install google-cloud-sdk');
        } else {
            console.log('   Linux:');
            console.log('   Visit: https://cloud.google.com/sdk/docs/install');
        }
        
        console.log('');
        console.log('After installation:');
        console.log('1. Run: gcloud init');
        console.log('2. Run: gcloud auth application-default login');
        console.log('3. Rebuild the dev container');
        
        process.exit(1);
    }

    // Try to get gcloud config directory
    const configDir = getGcloudConfigDir();
    
    if (configDir && dirExists(configDir)) {
        console.log(`✅ gcloud config directory detected: ${configDir}`);
        
        const credentialsFile = path.join(configDir, 'application_default_credentials.json');
        if (fileExists(credentialsFile)) {
            console.log('✅ Application Default Credentials found');
            console.log('🚀 Ready for Vertex AI integration!');
        } else {
            console.log('⚠️  No Application Default Credentials found');
            console.log('   Run: gcloud auth application-default login');
        }
        
        console.log('');
        console.log(`📋 gcloud config directory: ${configDir}`);
        console.log('   This will be mounted in the dev container');
        
        process.exit(0);
    }

    // Fallback: Check common locations
    console.log('⚠️  Could not determine gcloud config directory via gcloud command');
    console.log('🔍 Checking common locations...');
    
    const possiblePaths = [];
    
    if (platform === 'win32') {
        possiblePaths.push(
            path.join(process.env.APPDATA || '', 'gcloud'),
            path.join(process.env.USERPROFILE || '', '.config', 'gcloud'),
            path.join(process.env.USERPROFILE || '', 'AppData', 'Roaming', 'gcloud'),
            path.join(process.env.LOCALAPPDATA || '', 'gcloud'),
            path.join(process.env.PROGRAMDATA || '', 'gcloud'),
            // Additional Windows paths for different installation methods
            path.join(process.env.USERPROFILE || '', '.gcloud'),
            path.join('C:', 'Users', process.env.USERNAME || '', 'AppData', 'Roaming', 'gcloud')
        );
    } else {
        possiblePaths.push(
            path.join(process.env.HOME || '', '.config', 'gcloud'),
            path.join(process.env.HOME || '', '.gcloud'),  // Alternative location
            '/opt/google-cloud-sdk/config'  // System-wide installation
        );
    }
    
    let found = false;
    for (const possiblePath of possiblePaths) {
        if (dirExists(possiblePath)) {
            console.log(`✅ Found gcloud config at: ${possiblePath}`);
            
            const credentialsFile = path.join(possiblePath, 'application_default_credentials.json');
            if (fileExists(credentialsFile)) {
                console.log('✅ Application Default Credentials found');
            }
            
            found = true;
            break;
        }
    }
    
    if (found) {
        console.log('📋 gcloud credentials detected and will be mounted');
        process.exit(0);
    } else {
        console.log('❌ No gcloud configuration found');
        console.log('');
        console.log('🚀 Setup steps:');
        console.log('1. Install gcloud CLI: https://cloud.google.com/sdk/docs/install');
        console.log('2. Run: gcloud init');
        console.log('3. Run: gcloud auth application-default login');
        console.log('4. Rebuild the dev container');
        
        process.exit(1);
    }
}

// Run the script
main();
