#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ $# -gt 1 || ( $# -eq 1 && $1 != --full ) ]]; then
  echo "Usage: bash scripts/check.sh [--full]" >&2
  exit 2
fi
python3 check.py
if [[ $# -eq 1 ]]; then
  lake build +Solution +Challenge
  audit=$(mktemp)
  trap 'rm -f "$audit"' EXIT
  lake env lean -j1 -M1536 Audit.lean | tee "$audit"
  python3 check.py --audit "$audit"
fi
