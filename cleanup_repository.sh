#!/bin/bash

# Repository Cleanup Script for Altera Labs
# This script helps consolidate duplicate files and organize the repository

set -e

echo "🧹 Starting Altera Labs Repository Cleanup..."
echo "📋 This script will help consolidate duplicate files and organize the repository"
echo ""

# Create backup
echo "📦 Creating backup..."
BACKUP_DIR="backup_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"
cp -r . "$BACKUP_DIR" 2>/dev/null || echo "⚠️  Some files couldn't be backed up (git, node_modules, etc.)"
echo "✅ Backup created: $BACKUP_DIR"
echo ""

# Phase 1: Create archive directory and move old test reports
echo "📁 Phase 1: Archiving old test reports..."
mkdir -p docs/archive

# Move old test reports to archive
OLD_REPORTS=(
    "backend/improvement_test_report_20250727_063602.md"
    "backend/improvement_test_report_20250727_063712.md"
    "backend/improvement_test_report_20250727_063945.md"
    "backend/improvement_test_report_20250727_064654.md"
)

for report in "${OLD_REPORTS[@]}"; do
    if [ -f "$report" ]; then
        mv "$report" "docs/archive/"
        echo "📄 Archived: $report"
    fi
done

# Keep only the latest report
if [ -f "backend/improvement_test_report_20250727_065211.md" ]; then
    mv "backend/improvement_test_report_20250727_065211.md" "docs/TEST_REPORTS.md"
    echo "📄 Moved latest report to: docs/TEST_REPORTS.md"
fi

echo ""

# Phase 2: Remove empty log files
echo "🗑️  Phase 2: Removing empty log files..."
EMPTY_LOGS=(
    "backend/simple_hard_tests.log"
    "backend/hard_test_suite.log"
)

for log in "${EMPTY_LOGS[@]}"; do
    if [ -f "$log" ] && [ ! -s "$log" ]; then
        rm "$log"
        echo "🗑️  Removed empty log: $log"
    fi
done

echo ""

# Phase 3: Create organized directory structure
echo "📂 Phase 3: Creating organized directory structure..."

# Create test suite directory
mkdir -p backend/test_suite
echo "📁 Created: backend/test_suite/"

# Create config directory
mkdir -p backend/config
echo "📁 Created: backend/config/"

# Move configuration files
if [ -f "backend/developer_config.json" ]; then
    mv "backend/developer_config.json" "backend/config/"
    echo "📄 Moved: backend/developer_config.json → backend/config/"
fi

if [ -f "backend/developer_config.py" ]; then
    mv "backend/developer_config.py" "backend/config/"
    echo "📄 Moved: backend/developer_config.py → backend/config/"
fi

if [ -f "backend/developer_logs.json" ]; then
    mv "backend/developer_logs.json" "backend/config/"
    echo "📄 Moved: backend/developer_logs.json → backend/config/"
fi

echo ""

# Phase 4: Identify files for manual review
echo "🔍 Phase 4: Files requiring manual review..."
echo ""

echo "📚 Documentation files to consider consolidating:"
echo "   - docs/COLLABORATOR_SETUP.md"
echo "   - docs/QUICKSTART.md"
echo "   - docs/IMPLEMENTATION_SUMMARY.md"
echo "   - docs/IMPLEMENTATION_PLAN.md"
echo "   - backend/IMPROVEMENTS_IMPLEMENTATION_SUMMARY.md"
echo "   - backend/ENHANCED_PROVER_IMPLEMENTATION_SUMMARY.md"
echo "   - backend/RESEARCH_BASED_IMPROVEMENTS_SUMMARY.md"
echo ""

echo "🐍 Python test files to consider consolidating:"
echo "   - backend/simple_hard_tests.py"
echo "   - backend/hard_test_suite.py"
echo "   - backend/test_improvements.py"
echo "   - backend/test_enhanced_prover.py"
echo "   - backend/llm_performance_tester.py"
echo "   - backend/performance_improvement_plan.py"
echo ""

echo "📋 Shell scripts to review:"
echo "   - rebuild_container.sh"
echo "   - verify_dependencies.sh"
echo "   - backend/rebuild_dev_container.sh"
echo ""

# Phase 5: Generate summary
echo "📊 Phase 5: Cleanup Summary"
echo "================================"
echo "✅ Backup created: $BACKUP_DIR"
echo "✅ Archived old test reports to: docs/archive/"
echo "✅ Removed empty log files"
echo "✅ Created organized directory structure:"
echo "   - backend/test_suite/"
echo "   - backend/config/"
echo ""
echo "📋 Next steps:"
echo "1. Review the files listed above for consolidation"
echo "2. Update documentation links and references"
echo "3. Test all functionality after changes"
echo "4. Update CI/CD pipelines if needed"
echo ""
echo "🔧 For code duplication analysis, consider using:"
echo "   - refactor tool: pip install refactor && refactor backend/ --min-block-size 100"
echo "   - jsinspect: npm install -g jsinspect && jsinspect frontend/src/"
echo ""
echo "🎉 Repository cleanup script completed!" 