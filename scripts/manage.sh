#!/bin/bash

# Altera Labs Management Script
# Consolidated script for all development and maintenance tasks

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to show usage
show_usage() {
    echo "Altera Labs Management Script"
    echo ""
    echo "Usage: $0 [COMMAND] [OPTIONS]"
    echo ""
    echo "Commands:"
    echo "  container    - Container management"
    echo "    rebuild    - Rebuild the dev container"
    echo "    clean      - Clean Docker resources"
    echo "    diagnose   - Diagnose container issues"
    echo ""
    echo "  dependencies - Dependency management"
    echo "    verify     - Verify all dependencies"
    echo "    install    - Install missing dependencies"
    echo "    update     - Update dependencies"
    echo ""
    echo "  development  - Development tasks"
    echo "    test       - Run all tests"
    echo "    lint       - Run linting"
    echo "    build      - Build the project"
    echo "    start      - Start development servers"
    echo ""
    echo "  maintenance  - Maintenance tasks"
    echo "    cleanup    - Clean up repository"
    echo "    backup     - Create backup"
    echo "    archive    - Archive old files"
    echo ""
    echo "  help         - Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 container rebuild"
    echo "  $0 dependencies verify"
    echo "  $0 development test"
    echo "  $0 maintenance cleanup"
}

# Container management functions
container_rebuild() {
    print_status "Rebuilding dev container..."
    
    # Clean Docker resources
    print_status "Cleaning Docker resources..."
    docker system prune -f
    
    # Remove old containers
    docker ps -aq | xargs -r docker rm -f
    
    # Remove old images
    docker images -q | xargs -r docker rmi -f
    
    print_success "Docker resources cleaned"
    print_status "Please rebuild the container in your IDE (VS Code/Cursor)"
    print_status "Use 'Reopen in Container' command"
}

container_clean() {
    print_status "Cleaning Docker resources..."
    docker system prune -f
    docker volume prune -f
    print_success "Docker resources cleaned"
}

container_diagnose() {
    print_status "Diagnosing container issues..."
    
    # Check Docker status
    if ! docker info >/dev/null 2>&1; then
        print_error "Docker is not running"
        return 1
    fi
    
    # Check devcontainer configuration
    if [ ! -f ".devcontainer/devcontainer.json" ]; then
        print_error "Dev container configuration not found"
        return 1
    fi
    
    # Check post-create script
    if [ ! -f ".devcontainer/post-create.sh" ]; then
        print_error "Post-create script not found"
        return 1
    fi
    
    print_success "Container configuration looks good"
}

# Dependency management functions
dependencies_verify() {
    print_status "Verifying dependencies..."
    
    # Check Python dependencies
    if [ -f "backend/requirements.txt" ]; then
        print_status "Checking Python dependencies..."
        cd backend
        pip check
        cd ..
    fi
    
    # Check Node.js dependencies
    if [ -f "frontend/package.json" ]; then
        print_status "Checking Node.js dependencies..."
        cd frontend
        npm audit
        cd ..
    fi
    
    # Check Lean dependencies
    if [ -f "backend/lean_verifier/lakefile.toml" ]; then
        print_status "Checking Lean dependencies..."
        cd backend/lean_verifier
        if command -v lake >/dev/null 2>&1; then
            lake list-deps
        else
            print_warning "Lake not found - Lean dependencies not checked"
        fi
        cd ../..
    fi
    
    print_success "Dependency verification complete"
}

dependencies_install() {
    print_status "Installing dependencies..."
    
    # Install Python dependencies
    if [ -f "backend/requirements.txt" ]; then
        print_status "Installing Python dependencies..."
        cd backend
        pip install -r requirements.txt
        cd ..
    fi
    
    # Install Node.js dependencies
    if [ -f "frontend/package.json" ]; then
        print_status "Installing Node.js dependencies..."
        cd frontend
        npm install
        cd ..
    fi
    
    print_success "Dependencies installed"
}

dependencies_update() {
    print_status "Updating dependencies..."
    
    # Update Python dependencies
    if [ -f "backend/requirements.txt" ]; then
        print_status "Updating Python dependencies..."
        cd backend
        pip install --upgrade -r requirements.txt
        cd ..
    fi
    
    # Update Node.js dependencies
    if [ -f "frontend/package.json" ]; then
        print_status "Updating Node.js dependencies..."
        cd frontend
        npm update
        cd ..
    fi
    
    print_success "Dependencies updated"
}

# Development functions
development_test() {
    print_status "Running tests..."
    
    # Run Python tests
    if [ -f "backend/test_suite.py" ]; then
        print_status "Running Python tests..."
        cd backend
        python test_suite.py
        cd ..
    fi
    
    # Run frontend tests
    if [ -f "frontend/package.json" ]; then
        print_status "Running frontend tests..."
        cd frontend
        npm test
        cd ..
    fi
    
    print_success "Tests completed"
}

development_lint() {
    print_status "Running linting..."
    
    # Python linting
    if command -v flake8 >/dev/null 2>&1; then
        print_status "Running Python linting..."
        flake8 backend/
    fi
    
    # TypeScript linting
    if [ -f "frontend/package.json" ]; then
        print_status "Running TypeScript linting..."
        cd frontend
        npm run lint
        cd ..
    fi
    
    print_success "Linting completed"
}

development_build() {
    print_status "Building project..."
    
    # Build backend
    if [ -f "backend/requirements.txt" ]; then
        print_status "Building backend..."
        cd backend
        pip install -r requirements.txt
        cd ..
    fi
    
    # Build frontend
    if [ -f "frontend/package.json" ]; then
        print_status "Building frontend..."
        cd frontend
        npm run build
        cd ..
    fi
    
    print_success "Build completed"
}

development_start() {
    print_status "Starting development servers..."
    
    # Start backend
    if [ -f "backend/app.py" ]; then
        print_status "Starting backend server..."
        cd backend
        python -m app &
        BACKEND_PID=$!
        cd ..
    fi
    
    # Start frontend
    if [ -f "frontend/package.json" ]; then
        print_status "Starting frontend server..."
        cd frontend
        npm run dev &
        FRONTEND_PID=$!
        cd ..
    fi
    
    print_success "Development servers started"
    print_status "Backend PID: $BACKEND_PID"
    print_status "Frontend PID: $FRONTEND_PID"
    print_status "Press Ctrl+C to stop servers"
    
    # Wait for interrupt
    trap "kill $BACKEND_PID $FRONTEND_PID 2>/dev/null; exit" INT
    wait
}

# Maintenance functions
maintenance_cleanup() {
    print_status "Cleaning up repository..."
    
    # Create archive directory
    mkdir -p docs/archive
    
    # Move old test reports
    find . -name "*test_report*.md" -not -path "./docs/archive/*" -exec mv {} docs/archive/ \;
    
    # Move old implementation summaries
    find . -name "*implementation_summary*.md" -not -path "./docs/archive/*" -exec mv {} docs/archive/ \;
    
    # Clean up temporary files
    find . -name "*.pyc" -delete
    find . -name "__pycache__" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "*.log" -delete
    
    print_success "Repository cleanup completed"
}

maintenance_backup() {
    print_status "Creating backup..."
    
    BACKUP_DIR="backup_$(date +%Y%m%d_%H%M%S)"
    mkdir -p "$BACKUP_DIR"
    
    # Copy important files
    cp -r backend "$BACKUP_DIR/"
    cp -r frontend "$BACKUP_DIR/"
    cp -r docs "$BACKUP_DIR/"
    cp -r .devcontainer "$BACKUP_DIR/"
    cp *.md "$BACKUP_DIR/"
    cp *.json "$BACKUP_DIR/"
    cp *.toml "$BACKUP_DIR/"
    
    print_success "Backup created: $BACKUP_DIR"
}

maintenance_archive() {
    print_status "Archiving old files..."
    
    # Create archive directory
    mkdir -p docs/archive
    
    # Archive old test files
    find backend -name "*test*.py" -not -name "test_suite.py" -exec mv {} docs/archive/ \;
    
    # Archive old documentation
    find . -name "*setup*.md" -not -name "SETUP.md" -not -path "./docs/archive/*" -exec mv {} docs/archive/ \;
    
    print_success "Archiving completed"
}

# Main command dispatcher
case "$1" in
    "container")
        case "$2" in
            "rebuild") container_rebuild ;;
            "clean") container_clean ;;
            "diagnose") container_diagnose ;;
            *) print_error "Unknown container command: $2"; show_usage ;;
        esac
        ;;
    "dependencies")
        case "$2" in
            "verify") dependencies_verify ;;
            "install") dependencies_install ;;
            "update") dependencies_update ;;
            *) print_error "Unknown dependencies command: $2"; show_usage ;;
        esac
        ;;
    "development")
        case "$2" in
            "test") development_test ;;
            "lint") development_lint ;;
            "build") development_build ;;
            "start") development_start ;;
            *) print_error "Unknown development command: $2"; show_usage ;;
        esac
        ;;
    "maintenance")
        case "$2" in
            "cleanup") maintenance_cleanup ;;
            "backup") maintenance_backup ;;
            "archive") maintenance_archive ;;
            *) print_error "Unknown maintenance command: $2"; show_usage ;;
        esac
        ;;
    "help"|"-h"|"--help")
        show_usage
        ;;
    *)
        print_error "Unknown command: $1"
        show_usage
        exit 1
        ;;
esac 