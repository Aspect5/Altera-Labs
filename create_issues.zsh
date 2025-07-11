#!/usr/bin/env zsh
set -e  # exit on first error

###############################################################################
# CONFIGURATION – edit if needed
###############################################################################
ORG=Aspect5
REPO=Altera-Labs
PROJECT_TITLE="Altera Sprint 2025-Q3"
LABEL=backend            # label to attach to each new issue

###############################################################################
# 1️⃣  Resolve opaque Project-ID (works for org or user scope)
###############################################################################
PROJ_ID=$(
  gh project list --owner $ORG --format json | \
  jq -r --arg t "$PROJECT_TITLE" '
        (.projects? // .)          # if .projects exists use it, else root array
        | .[]                      # iterate objects
        | select(.title == $t)
        | .id'
)

if [[ -z $PROJ_ID ]]; then
  echo "❌  Project “$PROJECT_TITLE” not found under $ORG"
  exit 1
fi
echo "📋  Using project id  $PROJ_ID"

###############################################################################
# 2️⃣  Work-item definitions  (title → body text)
###############################################################################
typeset -A WORK_ITEMS=(
  "Warm-Up Cache"                "Implement bootstrap_lean_cache.py and warm-up"
  "LeanBuildManager"             "Serialised & cached Lean builds"
  "call_gemini Resilience"       "Retry logic + local LLM stub"
  "Tone Estimator"               "Integrate ONNX sentiment model"
  "Deep-Research Scan"           "Evaluate multilingual sentiment models"
  "Benchmark Candidates"         "Run F1 & latency benchmarks"
  "Front-End Tone Border UI"     "Add border-colour based on tone"
)

typeset -A ISSUE_NUMS            # title → issue number

###############################################################################
# 3️⃣  Create issues & link to project
###############################################################################
for TITLE in ${(k)WORK_ITEMS}; do
  BODY=$WORK_ITEMS[$TITLE]

  # Create the Issue (suppresses browser pop-up)
  ISSUE_URL=$(gh issue create \
                --repo $ORG/$REPO \
                --title "$TITLE" \
                --body  "$BODY" \
                --label "$LABEL" \
                --web=false)

  NUM=${ISSUE_URL:t}             # zsh :t = tail after last “/”
  ISSUE_NUMS[$TITLE]=$NUM
  echo "➕  Issue #$NUM  $TITLE"

  # Add card to the sprint project
  gh project item-add $PROJ_ID --owner $ORG --url $ISSUE_URL >/dev/null
  echo "   ↳ linked to project"
done

echo "\n✅  All issues created & added to “$PROJECT_TITLE”"
