# 🚀 Altera Labs - Collaborator Setup Guide

Welcome to Altera Labs! This guide will help you get up and running with our development environment in minutes.

## 📋 Prerequisites

Before you start, make sure you have:

- **Docker Desktop** installed and running
- **VS Code** or **Cursor** IDE
- **Git** for version control

## 🎯 Quick Start (Recommended)

### 1. Clone the Repository
```bash
git clone <repository-url>
cd Altera-Labs
```

### 2. Open in Dev Container
1. Open the project in VS Code/Cursor
2. When prompted, click **"Reopen in Container"**
3. Wait for the container to build (5-10 minutes on first run)

That's it! The container will automatically install all dependencies.

## 🔧 What Gets Installed Automatically

The dev container automatically sets up:

### **Core Dependencies**
- ✅ **Python 3.10** with all backend requirements
- ✅ **Node.js 20** with frontend dependencies  
- ✅ **Lean 4** with Mathlib for theorem proving
- ✅ **Google Cloud SDK** for AI services
- ✅ **Git** for version control

### **VS Code Extensions**
- ✅ **Lean4** - Lean theorem prover support
- ✅ **Python** - Python development tools
- ✅ **Pylance** - Python language server
- ✅ **TypeScript** - Frontend development
- ✅ **JSON** - Configuration file support

### **Project Setup**
- ✅ **Backend dependencies** installed from `requirements.txt`
- ✅ **Frontend dependencies** installed from `frontend/package.json`
- ✅ **Lean project** configured with Mathlib
- ✅ **Google Cloud** authentication verified

## 🚀 Running the Application

Once the container is ready, you can start development:

### **Backend (Flask API)**
```bash
cd backend
python -m app
```
The API will be available at `http://localhost:5000`

### **Frontend (React + Vite)**
```bash
cd frontend
npm run dev
```
The frontend will be available at `http://localhost:5173`

### **Lean Development**
```bash
cd backend/lean_verifier
lake build
```

## 🔍 Troubleshooting

### **Container Won't Start**
If the container gets stuck during build:

1. **Clear Cursor/VS Code cache:**
   ```bash
   rm -rf ~/.cursor-server
   rm -rf ~/.cursor ~/.cursor-server ~/.vscode-remote-containers
   ```

2. **Restart Docker Desktop**

3. **Try again** - "Reopen in Container"

### **Dependencies Missing**
If something isn't working:

```bash
# Re-run the setup script
bash .devcontainer/post-create.sh
```

### **Google Cloud Issues**
If you need to authenticate with Google Cloud:

```bash
# For development (recommended)
gcloud auth application-default login

# Or for user authentication
gcloud auth login

# Set the correct project
gcloud config set project altera-labs
```

### **Lean Issues**
If Lean isn't working:

```bash
cd backend/lean_verifier
lake update mathlib
lake build
```

## 📁 Project Structure

```
Altera-Labs/
├── backend/                 # Python Flask API
│   ├── app.py              # Main application
│   ├── lean_verifier/      # Lean 4 theorem prover
│   └── requirements.txt    # Python dependencies
├── frontend/               # React + TypeScript
│   ├── src/               # Source code
│   ├── package.json       # Node.js dependencies
│   └── vite.config.ts     # Build configuration
├── .devcontainer/         # Dev container configuration
│   ├── devcontainer.json  # Container setup
│   └── post-create.sh     # Post-creation script
└── docs/                  # Documentation
```

## 🛠️ Development Workflow

### **Making Changes**
1. All changes are made inside the dev container
2. Code is automatically synced with your host machine
3. Use Git for version control as usual

### **Adding Dependencies**
- **Python**: Add to `backend/requirements.txt`
- **Node.js**: Add to `frontend/package.json`
- **Lean**: Add to `backend/lean_verifier/lakefile.toml`

### **Testing**
- **Backend**: `cd backend && python -m pytest`
- **Frontend**: `cd frontend && npm test`
- **Lean**: `cd backend/lean_verifier && lake test`

## 🔐 Security Notes

- Google Cloud credentials are mounted as read-only
- All dependencies are installed inside the container
- No sensitive data is stored in the repository

## 📞 Getting Help

If you encounter issues:

1. **Check the logs** in the terminal
2. **Run the setup script** manually: `bash .devcontainer/post-create.sh`
3. **Ask the team** - we're here to help!

## 🎉 You're Ready!

The dev container ensures everyone has the same development environment. No more "works on my machine" issues!

Happy coding! 🚀 