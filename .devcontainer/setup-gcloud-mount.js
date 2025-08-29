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

// Workspace paths
const repoRoot = process.cwd();
const stagingDir = path.join(repoRoot, '.devcontainer', '_gcloud');

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

// Ensure a clean staging directory
function ensureCleanDir(dirPath) {
    try {
        fs.rmSync(dirPath, { recursive: true, force: true });
    } catch {}
    fs.mkdirSync(dirPath, { recursive: true });
}

// Cross-platform recursive copy
function copyRecursiveSync(src, dest) {
    const stat = fs.lstatSync(src);
    if (stat.isDirectory()) {
        fs.mkdirSync(dest, { recursive: true });
        for (const entry of fs.readdirSync(src)) {
            const srcEntry = path.join(src, entry);
            const destEntry = path.join(dest, entry);
            copyRecursiveSync(srcEntry, destEntry);
        }
    } else if (stat.isFile()) {
        fs.copyFileSync(src, dest);
    } else if (stat.isSymbolicLink && stat.isSymbolicLink()) {
        try {
            const target = fs.readlinkSync(src);
            fs.symlinkSync(target, dest);
        } catch {
            // Skip problematic symlinks
        }
    }
}

// Main logic
function main() {
    let sourceConfigDir = null;

    // Prefer gcloud-detected path if CLI is available
    if (commandExists('gcloud')) {
        const configDir = getGcloudConfigDir();
        if (configDir && dirExists(configDir)) {
            console.log(`✅ gcloud config directory detected: ${configDir}`);
            sourceConfigDir = configDir;
        } else {
            console.log('⚠️  gcloud CLI present but config directory not found via command.');
        }
    } else {
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
        console.log('Attempting to locate existing gcloud config in common locations...');
    }

    // Fallback: Check common locations if needed
    if (!sourceConfigDir) {
        console.log('🔍 Checking common locations...');
        const possiblePaths = [];
        if (platform === 'win32') {
            possiblePaths.push(
                path.join(process.env.APPDATA || '', 'gcloud'),
                path.join(process.env.USERPROFILE || '', '.config', 'gcloud'),
                path.join(process.env.USERPROFILE || '', 'AppData', 'Roaming', 'gcloud'),
                path.join(process.env.LOCALAPPDATA || '', 'gcloud'),
                path.join(process.env.PROGRAMDATA || '', 'gcloud'),
                path.join(process.env.USERPROFILE || '', '.gcloud'),
                path.join('C:', 'Users', process.env.USERNAME || '', 'AppData', 'Roaming', 'gcloud')
            );
        } else {
            possiblePaths.push(
                path.join(process.env.HOME || '', '.config', 'gcloud'),
                path.join(process.env.HOME || '', '.gcloud'),
                '/opt/google-cloud-sdk/config'
            );
        }
        for (const possiblePath of possiblePaths) {
            if (dirExists(possiblePath)) {
                console.log(`✅ Found gcloud config at: ${possiblePath}`);
                sourceConfigDir = possiblePath;
                break;
            }
        }
    }

    if (sourceConfigDir) {
        console.log(`📦 Staging gcloud config into: ${stagingDir}`);
        ensureCleanDir(stagingDir);
        copyRecursiveSync(sourceConfigDir, stagingDir);
        const stagedCreds = path.join(stagingDir, 'application_default_credentials.json');
        if (fileExists(stagedCreds)) {
            console.log('✅ Application Default Credentials staged');
            console.log('🚀 Ready for Vertex AI integration!');
        } else {
            console.log('⚠️  No Application Default Credentials found in staged directory');
            console.log('   Run: gcloud auth application-default login');
        }
        console.log('📋 Staged gcloud directory will be mounted in the dev container');
        process.exit(0);
    } else {
        console.log('❌ No gcloud configuration found');
        console.log('');
        console.log('🚀 Setup steps:');
        console.log('1. Install gcloud CLI: https://cloud.google.com/sdk/docs/install');
        console.log('2. Run: gcloud init');
        console.log('3. Run: gcloud auth application-default login');
        console.log('4. Rebuild the dev container');
        // Do not fail the devcontainer build if credentials are missing.
        // The container can still be built, and credentials can be added later.
        process.exit(0);
    }
}

// Run the script
main();
