# 🚀 Altera Labs Quick Start Guide

## Prerequisites

- ✅ Docker Desktop (running)
- ✅ VS Code with Dev Containers extension
- ✅ Google Cloud account with Vertex AI access

## One-Time Setup

### 1. Authenticate with Google Cloud
```bash
gcloud auth application-default login
```

### 2. Clone and Open
```bash
git clone <repository-url>
cd Altera-Labs
code .  # Opens VS Code
```

### 3. Reopen in Container 
- Click "Reopen in Container" when prompted
- Wait 5-10 minutes for setup to complete
- Look for "✅✅✅ Dev Container setup complete!" message

## Running the Application

### Terminal 1: Backend
```bash
cd backend && python -m app
```
**Expected Output:**
```
Lean Verifier initialized.
Vertex AI initialized successfully for project 'altera-labs' in 'us-east1'.
* Running on http://127.0.0.1:5000
```

### Terminal 2: Frontend
```bash
cd frontend && npm run dev
```
**Expected Output:**
```
Local:   http://localhost:5173/
```

### 4. Open Browser
Navigate to `http://localhost:5173`

## Testing the System

### 1. Create a Class
- Click "Create New Class" on dashboard
- Enter class name (e.g., "Test Math")
- Upload `practice_question.txt` from root directory

### 2. Enable Developer Mode
- Click the developer panel toggle (top-right corner)
- This shows real-time LLM attempts and Lean verification

### 3. Monitor Auto-Solve
- Watch the LLM attempt logs in real-time
- See Lean verification results
- View solution popup when AI succeeds

## Troubleshooting

### Lean Not Found Error
```bash
# Restart container
# Or manually verify Lean installation
lean --version
which lean
```

### Google Cloud Issues
```bash
# Re-authenticate
gcloud auth application-default login
```

### Port Conflicts
```bash
# Check if ports are in use
lsof -i :5000
lsof -i :5173
```

## Key Features to Test

### ✅ Homework Upload
- Upload `practice_question.txt`
- Watch auto-solve attempts
- View solution results

### ✅ Developer Tools
- Real-time LLM attempt logs
- Lean error parsing
- Configuration panel

### ✅ Gamification
- Points awarded for interactions
- Achievement unlocks
- Progress tracking

### ✅ Knowledge Visualization
- Interactive knowledge graphs
- Mastery tracking
- Progress flowers

## File Structure Overview

```
Altera-Labs/
├── .devcontainer/          # Container configuration
├── backend/               # Python Flask backend
│   ├── lean_verifier.py   # Lean 4 integration
│   ├── lean_verifier/     # Lean project
│   └── app.py            # Main Flask app
├── frontend/             # React TypeScript frontend
│   ├── components/       # Modular components
│   ├── services/         # API services
│   └── types/           # TypeScript types
└── practice_question.txt # Test file for uploads
```

## Development Workflow

### Making Changes
1. **Frontend**: Edit files in `frontend/` (hot reload enabled)
2. **Backend**: Edit files in `backend/` (auto-restart enabled)
3. **Lean**: Edit files in `backend/lean_verifier/`

### Testing Changes
1. **Frontend**: Changes appear immediately
2. **Backend**: Restart with `Ctrl+C` then `python -m app`
3. **Lean**: Use `lake build` in `backend/lean_verifier/`

### Debugging
- **Frontend**: Browser dev tools + React dev tools
- **Backend**: Flask debug mode + Python logging
- **Lean**: Developer panel with real-time logs

## Environment Variables

The container automatically sets:
- `VERTEX_AI_PROJECT_ID=altera-labs`
- `VERTEX_AI_LOCATION=us-east1`
- `PATH` includes Lean installation

## Performance Tips

- **First build**: May take 5-10 minutes (dependencies)
- **Subsequent builds**: Much faster (cached)
- **Lean verification**: 30-second timeout per attempt
- **Memory usage**: ~2GB RAM recommended

## Support

- **Container issues**: Check Docker Desktop is running
- **Lean issues**: Verify with `lean --version`
- **Google Cloud**: Ensure authentication is current
- **Port issues**: Check for conflicts on 5000/5173

---

**🎉 You're ready to build the future of AI-powered education!** 