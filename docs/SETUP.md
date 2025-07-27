# 🚀 Altera Labs - Complete Setup Guide

Welcome to Altera Labs! This comprehensive guide covers all setup scenarios for our AI-powered math education platform.

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

### **Core Technologies**
- ✅ **Python 3.10** - Backend API with Flask
- ✅ **Node.js 20** - Frontend with React + Vite
- ✅ **Lean 4** - Theorem proving environment
- ✅ **Git** - Version control

### **Development Tools**
- ✅ **Lean4 Extension** - Syntax highlighting and proof assistance
- ✅ **Python Extension** - Code completion and debugging
- ✅ **Pylance** - Advanced Python language support
- ✅ **TypeScript Support** - Frontend development

### **Dependencies**
- ✅ **Mathlib** - Lean mathematics library
- ✅ **Flask** - Python web framework
- ✅ **React** - Frontend framework
- ✅ **Tailwind CSS** - Styling framework

## 🚀 Starting Development

Once the container is ready:

```bash
# Backend (Flask API)
cd backend && python -m app

# Frontend (React + Vite) - in another terminal
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
- **Container won't start**: Restart Docker Desktop
- **Extensions not loading**: Clear VS Code/Cursor cache
- **Build hanging**: Use simplified devcontainer configuration

### Lean Issues
- **Mathlib not found**: Run `lake update mathlib`
- **Build errors**: Check `lakefile.toml` configuration
- **Toolchain issues**: Reinstall elan

### Python Issues
- **Import errors**: Check virtual environment activation
- **Package not found**: Run `pip install -r requirements.txt`

## 📚 Additional Resources

- [Technical Specification](TECHNICAL_SPEC.md)
- [Implementation Plan](IMPLEMENTATION_PLAN.md)
- [API Documentation](backend/README.md)
- [Frontend Architecture](frontend/ARCHITECTURE.md)

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Submit a pull request

## 📞 Support

If you encounter issues:
1. Check the troubleshooting section above
2. Search existing issues
3. Create a new issue with detailed information 