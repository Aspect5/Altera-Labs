# Container Setup and Lean Integration

## Overview

Altera Labs uses VS Code Dev Containers to ensure a consistent, isolated development environment. This approach guarantees that all dependencies, including Lean 4, are properly installed and configured regardless of the host system.

## Container Architecture

### Key Components

1. **Base Image**: `mcr.microsoft.com/devcontainers/base:ubuntu`
2. **Language Features**: Python 3.10, Node.js 20, Git
3. **Lean 4 Integration**: Installed via `elan` (Lean's toolchain manager)
4. **Google Cloud Integration**: Mounted credentials for Vertex AI access

### Environment Variables

```json
{
  "VERTEX_AI_PROJECT_ID": "altera-labs",
  "VERTEX_AI_LOCATION": "us-east1"
}
```

## Lean 4 Integration

### Installation Process

The Lean 4 integration is handled entirely within the container:

1. **Elan Installation**: Uses the official `elan-init.sh` script
2. **Environment Configuration**: Adds Lean to PATH via `.profile` and `.bashrc`
3. **Project Setup**: Initializes a Lean project in `backend/lean_verifier/`
4. **Dependency Management**: Uses `lake` for Lean package management

### Verification Steps

The post-create script includes several verification steps:

```bash
# Verify Lean installation
lean --version

# Test Lean project build
lake build

# Test simple theorem
echo 'theorem test : 1 + 1 = 2 := by rfl' > test_integration.lean
lake lean test_integration.lean

# Test Python integration
python3 -c "import subprocess; result = subprocess.run(['lean', '--version'], capture_output=True, text=True); print('✅ Python can call Lean:', result.returncode == 0)"
```

### Python Integration

The backend uses `subprocess.run()` to call Lean through the `lake` command:

```python
# In lean_verifier.py
lean_project_dir = os.path.join(os.path.dirname(__file__), 'lean_verifier')
result = subprocess.run(
    ['lake', 'lean', temp_file],
    capture_output=True,
    text=True,
    timeout=30,
    env=env,
    cwd=lean_project_dir
)
```

## Setup Instructions

### Prerequisites

1. **Docker Desktop**: Must be running
2. **VS Code**: With Dev Containers extension
3. **Google Cloud**: Authenticated locally (`gcloud auth application-default login`)

### Container Build Process

1. **Clone Repository**:
   ```bash
   git clone <repository-url>
   cd Altera-Labs
   ```

2. **Authenticate with Google Cloud**:
   ```bash
   gcloud auth application-default login
   ```

3. **Open in Container**:
   - Open VS Code in the project directory
   - Click "Reopen in Container" when prompted
   - Wait for post-create script to complete (5-10 minutes)

### Post-Create Script Flow

```bash
# 1. Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# 2. Configure environment
export PATH="/home/vscode/.elan/bin:$PATH"
echo 'export PATH="/home/vscode/.elan/bin:$PATH"' >> /home/vscode/.profile

# 3. Initialize Lean project
lake new lean_verifier math
lake build

# 4. Install Node.js dependencies
npm install

# 5. Install Python dependencies
pip install -r backend/requirements.txt

# 6. Verify integration
python3 -c "import subprocess; subprocess.run(['lean', '--version'])"
```

## Troubleshooting

### Common Issues

**Lean Not Found Error**
- **Symptom**: `[Errno 2] No such file or directory: 'lean'`
- **Solution**: Restart the container to ensure environment is properly loaded

**Lake Build Failures**
- **Symptom**: `lake build` fails with dependency errors
- **Solution**: Check internet connectivity and try `lake update` followed by `lake build`

**Google Cloud Authentication**
- **Symptom**: Vertex AI initialization failures
- **Solution**: Ensure `gcloud auth application-default login` was run before container build

**Port Conflicts**
- **Symptom**: Backend or frontend won't start
- **Solution**: Check that ports 5000 and 5173 are available

### Debugging Commands

```bash
# Check Lean installation
lean --version
which lean

# Check environment
echo $PATH
env | grep LEAN

# Test Lean project
cd backend/lean_verifier
lake build
lake lean --help

# Test Python integration
python3 -c "import subprocess; print(subprocess.run(['lean', '--version'], capture_output=True, text=True).stdout)"
```

## Development Workflow

### Starting the Application

1. **Backend** (Terminal 1):
   ```bash
   cd backend && python -m app
   ```

2. **Frontend** (Terminal 2):
   ```bash
   cd frontend && npm run dev
   ```

### Testing Lean Integration

1. **Upload Homework**: Use `practice_question.txt` in the root directory
2. **Enable Developer Mode**: Click the developer panel toggle
3. **Monitor Logs**: Watch real-time LLM attempts and Lean verification
4. **Check Results**: View solution popup when AI solves problems

### File Structure

```
Altera-Labs/
├── .devcontainer/
│   ├── devcontainer.json    # Container configuration
│   └── post-create.sh       # Setup script
├── backend/
│   ├── lean_verifier.py     # Lean integration (fixed)
│   ├── lean_verifier/       # Lean project
│   │   ├── lakefile.toml    # Lean dependencies
│   │   └── LeanVerifier/    # Lean modules
│   └── app.py              # Flask application
├── frontend/               # React application
└── practice_question.txt   # Test file for uploads
```

## Best Practices

### Container Development

1. **Always use the container**: Don't install dependencies on the host
2. **Rebuild on major changes**: If post-create script changes, rebuild container
3. **Use volume mounts**: Google Cloud credentials are mounted from host
4. **Check logs**: Monitor post-create script output for any issues

### Lean Development

1. **Use lake commands**: Always use `lake` instead of direct `lean` calls
2. **Test incrementally**: Use simple theorems for testing
3. **Monitor timeouts**: Lean verification has 30-second timeout
4. **Check project structure**: Ensure `lakefile.toml` is properly configured

### Python Integration

1. **Use subprocess.run()**: For calling external commands
2. **Set working directory**: Use `cwd` parameter for lake commands
3. **Handle timeouts**: Always set reasonable timeouts for Lean operations
4. **Parse output**: Use structured error parsing for better debugging

## Security Considerations

1. **Isolated environment**: Container provides isolation from host system
2. **Mounted credentials**: Google Cloud credentials are securely mounted
3. **No hardcoded secrets**: All sensitive data comes from environment variables
4. **Limited permissions**: Container runs with minimal required permissions

## Performance Optimization

1. **Cached dependencies**: Lake and npm dependencies are cached
2. **Incremental builds**: Lean project only rebuilds changed files
3. **Resource limits**: Container has reasonable memory and CPU limits
4. **Timeout handling**: Prevents hanging processes

This containerized approach ensures that Altera Labs works consistently across different development environments while maintaining proper isolation and security. 