#!/bin/bash

echo "=== Verifying Git Dependencies for Altera Labs ==="

echo ""
echo "1. Checking Lean project configuration..."
cd backend/lean_verifier

echo "   - lakefile.toml exists: $(test -f lakefile.toml && echo "✅" || echo "❌")"
echo "   - lake-manifest.json exists: $(test -f lake-manifest.json && echo "✅" || echo "❌")"

echo ""
echo "2. Checking Mathlib dependency..."
if grep -q "git.*mathlib4" lakefile.toml; then
    echo "   ✅ Mathlib4 Git dependency configured"
    grep "git.*mathlib4" lakefile.toml
else
    echo "   ❌ Mathlib4 Git dependency not found"
fi

echo ""
echo "3. Checking other dependencies in lake-manifest.json..."
echo "   Dependencies found:"
jq -r '.packages[] | "   - \(.name): \(.url) (\(.rev[0:8]))"' lake-manifest.json 2>/dev/null || echo "   (jq not available, showing raw content)"

echo ""
echo "4. Checking if packages are downloaded..."
if [ -d ".lake/packages/mathlib" ]; then
    echo "   ✅ Mathlib package downloaded"
    echo "   - Mathlib version: $(cd .lake/packages/mathlib && git rev-parse --short HEAD 2>/dev/null || echo "unknown")"
else
    echo "   ❌ Mathlib package not downloaded"
fi

echo ""
echo "5. Testing Git connectivity..."
echo "   Testing connection to Mathlib4 repository..."
if curl -s --head https://github.com/leanprover-community/mathlib4 | head -1 | grep -q "200"; then
    echo "   ✅ Mathlib4 repository accessible"
else
    echo "   ❌ Cannot access Mathlib4 repository"
fi

echo ""
echo "6. Checking for potential issues..."
echo "   - Mathlib3 archive notice: The Mathlib3 repository was archived on July 24, 2024"
echo "   - We should be using Mathlib4 (which we are)"
echo "   - Current setup uses master branch for latest features"

echo ""
echo "=== Dependency verification complete ==="
echo ""
echo "To rebuild the container with these dependencies:"
echo "1. Run: ./rebuild_container.sh"
echo "2. In VS Code: Cmd+Shift+P → 'Dev Containers: Rebuild Container'"
echo "3. Wait for post-create script to complete (5-10 minutes)" 