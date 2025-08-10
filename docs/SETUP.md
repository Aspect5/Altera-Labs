# 🚀 Altera Labs - Complete Setup Guide

Welcome to Altera Labs! This guide covers setup for the AI-powered math education platform.

## 📋 Prerequisites

- Docker Desktop running
- VS Code or Cursor
- Git

## 🎯 Quick Start (Recommended)

1) Clone the repository
```bash
git clone <repository-url>
cd Altera-Labs
```

2) Open in Dev Container
- Open the project in VS Code/Cursor
- Choose "Reopen in Container"
- First build takes ~5–10 minutes

The container will automatically install dependencies (Python venv, root `npm install`, frontend `npm install`, Lean via `elan` + `lake build`).

## 🔧 What Gets Installed Automatically

- Python 3.10, Node.js 20, Git
- `.venv` at repo root with `backend/requirements.txt` installed
- Tailwind/PostCSS tooling via root `package.json`
- Frontend dependencies via `frontend/package.json`
- Lean 4 via `elan` and `lake build` for `backend/lean_verifier`
- Environment variables inside container: `VERTEX_AI_PROJECT_ID=altera-labs`, `VERTEX_AI_LOCATION=us-east1`
- If present on your host, your Google Cloud credentials directory is mounted into the container (note: `gcloud` CLI is not installed)

### Development Tools
- Lean4 extension is installed automatically
- Python, Pylance, and TypeScript extensions are recommended (install from the marketplace if needed)

## 🚀 Starting Development

Inside the dev container:
```bash
# Backend (Flask API)
cd backend && python -m app

# Frontend (React + Vite) — in another terminal
cd frontend && npm run dev
```

## 🔧 Manual Setup (Alternative)

If you prefer to set up locally without containers:

### Backend Setup
```bash
cd backend
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
pip install -r requirements.txt
python -m app
```

### Frontend Setup
```bash
# From repo root (for Tailwind/PostCSS)
npm install
cd frontend
npm install
npm run dev
```

### Lean Setup
```bash
# Install elan (Lean toolchain manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.bashrc

# Build Lean project
cd backend/lean_verifier
lake build
```

## 🐛 Troubleshooting

### Container Issues
- Container won't start: Restart Docker Desktop
- Extensions not loading: Clear VS Code/Cursor cache
- Diagnose: `./scripts/manage.sh container diagnose`

### Lean Issues
- Mathlib not found: `lake update mathlib`
- Build errors: Check `lakefile.toml`
- Toolchain issues: Reinstall elan

### Python Issues
- Import errors: Check virtual environment activation
- Package not found: `pip install -r backend/requirements.txt`

## 📚 Additional Resources
- Technical Specification: `../TECHNICAL_SPEC.md`
- Frontend Architecture: `../frontend/ARCHITECTURE.md`

## 🤝 Contributing
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Submit a pull request

## 📞 Support
- Check the troubleshooting section above
- Search existing issues
- Create a new issue with details 