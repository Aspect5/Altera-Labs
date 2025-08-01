# 🚀 Altera Labs - AI-Powered Math Education Platform

An intelligent tutoring system that combines Lean 4 theorem proving with AI to provide personalized math education.

## 🎯 Quick Start

# MODEL:
http://xgrg.github.io/Inserting-BibTeX-references-in-Google-Docs

### **For Collaborators (Recommended)**
1. **Clone the repository**
   ```bash
   git clone <repository-url>
   cd Altera-Labs
   ```

2. **Open in Dev Container**
   - Open in VS Code or Cursor
   - Click **"Reopen in Container"** when prompted
   - Wait 5-10 minutes for automatic setup

3. **Start Development**
   ```bash
   # Use the management script for easy development
   ./scripts/manage.sh development start
   
   # Or manually:
   # Backend (Flask API)
   cd backend && python -m app
   
   # Frontend (React + Vite)
   cd frontend && npm run dev
   ```

## 🔧 What's Included

### **Core Technologies**
- ✅ **Python 3.10** - Backend API with Flask
- ✅ **Node.js 20** - Frontend with React + TypeScript
- ✅ **Lean 4** - Theorem proving with Mathlib
- ✅ **Google Cloud** - Vertex AI integration
- ✅ **Git** - Version control

### **VS Code Extensions**
- ✅ **Lean4** - Lean theorem prover support
- ✅ **Python** - Python development tools
- ✅ **Pylance** - Python language server
- ✅ **TypeScript** - Frontend development

### **Automatic Setup**
The dev container automatically installs:
- All Python dependencies from `backend/requirements.txt`
- All Node.js dependencies from `frontend/package.json`
- Lean 4 with Mathlib for theorem proving
- Google Cloud SDK for AI services

## 🏗️ Project Structure

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
├── docs/                  # Documentation
└── COLLABORATOR_SETUP.md  # Detailed setup guide
```

## 🚀 Running the Application

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

## 🛠️ Management Tools

### **Unified Management Script**
All development tasks are now consolidated into a single script:

```bash
# Container management
./scripts/manage.sh container rebuild
./scripts/manage.sh container diagnose

# Dependency management
./scripts/manage.sh dependencies verify
./scripts/manage.sh dependencies install

# Development tasks
./scripts/manage.sh development test
./scripts/manage.sh development start
./scripts/manage.sh development build

# Maintenance
./scripts/manage.sh maintenance cleanup
./scripts/manage.sh maintenance backup
```

### **Consolidated Test Suite**
All testing is now unified in `backend/test_suite.py`:
- Unit tests for all components
- Performance benchmarking
- Integration testing
- Configuration validation

### **Comprehensive Setup Guide**
All setup documentation is consolidated in `docs/SETUP.md`:
- Quick start for collaborators
- Manual setup instructions
- Troubleshooting guide
- Development workflow

## 📚 Documentation

- **[Complete Setup Guide](docs/SETUP.md)** - All setup scenarios
- **[System Architecture](frontend/ARCHITECTURE.md)** - Frontend architecture
- **[Technical Specification](TECHNICAL_SPEC.md)** - System design

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Test thoroughly
5. Submit a pull request

## 📞 Getting Help

If you encounter issues:

1. **Check the logs** in the terminal
2. **Run the setup script** manually: `bash .devcontainer/post-create.sh`
3. **Ask the team** - we're here to help!

## 🎉 You're Ready!

The dev container ensures everyone has the same development environment. No more "works on my machine" issues!

Happy coding! 🚀

# Altera Labs - Development Environment Setup

## Best Practices for Running Backend and Frontend

### 1. **Devcontainer (Recommended for Consistency)**

- Open the project in VS Code or Cursor.
- Use "Reopen in Container" (VS Code) or the equivalent in Cursor.
- The devcontainer will automatically:
  - Create a Linux-native `.venv` in the project root
  - Install all Python dependencies in the venv
  - Set up Node and Lean dependencies
  - Auto-activate the venv in every new terminal
- **To run the backend:**
  ```sh
  cd backend
  python -m app
  ```
- **To run the frontend:**
  ```sh
  cd frontend
  npm run dev
  ```

### 2. **Running on Your Host (macOS/Linux/Windows)**

- **Do NOT use the container's `.venv` on your host.**
- Create a separate venv for your host:
  ```sh
  python3 -m venv .venv-mac  # or .venv-win, etc.
  source .venv-mac/bin/activate
  pip install --upgrade pip
  pip install -r backend/requirements.txt
  ```
- **To run the backend:**
  ```sh
  cd backend
  python -m app
  ```
- **To run the frontend:**
  ```sh
  cd frontend
  npm install
  npm run dev
  ```

### 3. **Python Import Structure**
- All imports of `developer_config` should use:
  ```python
  from config.developer_config import developer_config, developer_logger
  ```
- The `config/` directory must contain an `__init__.py` file (already present).

### 4. **.venv is in .gitignore**
- Never commit `.venv` to the repo. Each environment (host or container) should create its own venv.

### 5. **VS Code/Cursor Interpreter**
- The devcontainer sets the interpreter to `.venv/bin/python` only inside the container.
- On your host, select your host-native venv interpreter manually if needed.

---

For more details, see the devcontainer and VS Code documentation.

Graphs:


2.4. System Architecture Diagrams

The following diagrams visually represent the significant gap between the planned architecture and the current implementation.

Diagram 1: Planned Hierarchical Knowledge Architecture


Code snippet


graph TD
```
    subgraph User Interaction Layer
        UI(React Frontend)
    end

    subgraph API & Orchestration Layer
        FLASK(Flask Backend API)
    end

    subgraph AI & Reasoning Layer
        GEMINI(Gemini 2.5 Pro API <br> Socratic Dialogue, Summarization, NLP)
        PROVER_AGENT(Specialized Prover Agent <br> e.g., DeepSeek-Prover-V2)
    end

    subgraph Knowledge & Persistence Layer
        NEO4J(Neo4j Graph Database)
    end

    subgraph Data Processing Layer
        PARSER(Syllabus Parser <br> GCN/DBN Student Modeler)
        RAG_PIPELINE(Offline GraphRAG Pipeline <br> Embeddings, Community Detection)
    end

    UI -- API Calls --> FLASK
    FLASK -- Socratic Prompts --> GEMINI
    FLASK -- Graph Queries --> NEO4J
    FLASK -- Interaction Data --> PARSER
    GEMINI -- Parsed Data --> FLASK
    PARSER -- Updates PKG/DBN --> NEO4J

    subgraph NEO4J
        PKG1(PKG - Student 1)
        PKG2(PKG - Student 2)
        GLOBAL_GRAPH(Global Mathlib Graph <br> Community Partitioned)
    end

    PKG1 -- Hierarchical Query --> GLOBAL_GRAPH
    PKG2 -- Hierarchical Query --> GLOBAL_GRAPH

    RAG_PIPELINE -- Builds/Updates --> GLOBAL_GRAPH
    FLASK -- Calls Prover as Tool --> PROVER_AGENT
    PROVER_AGENT -- Formal Proof Goal --> PROVER_AGENT
    PROVER_AGENT -- Lean 4 Tactic --> FLASK

    style GLOBAL_GRAPH fill:#d5f5e3,stroke:#27ae60
    style PKG1 fill:#eaf2f8,stroke:#3498db
    style PKG2 fill:#eaf2f8,stroke:#3498db
```


Diagram 2: Current Implemented Architecture


Code snippet


graph TD
```
    subgraph User Interaction Layer
        UI(React Frontend)
    end

    subgraph Backend Layer
        FLASK(Flask Backend - app.py)
    end

    subgraph AI & Verification Layer
        GEMINI_API(Gemini API Call <br> socratic_auditor.py)
        LEAN(Lean 4 Verifier <br> Subprocess Call)
    end

    subgraph Static Knowledge & Storage
        KNOWLEDGE_DICT(Static Knowledge Base <br> lean_knowledge_base.py)
        JSON_DB(classes.json <br> Flat-File Persistence)
    end

    UI -- API Calls --> FLASK
    FLASK -- Reads/Writes --> JSON_DB
    FLASK -- General Prompts --> GEMINI_API
    FLASK -- Looks up theorems --> KNOWLEDGE_DICT
    GEMINI_API -- Text/JSON --> FLASK
    FLASK -- Sends Tactic for Verification --> LEAN
    LEAN -- Success/Error --> FLASK
```