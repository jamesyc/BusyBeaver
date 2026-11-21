#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# -gt 1 || ( $# -eq 1 && $1 != --full ) ]]; then
  printf '%s\n' 'Usage: bash scripts/check.sh [--full]' >&2
  exit 2
fi

python3 scripts/gen_tables.py --check
if [[ $# -eq 1 ]]; then
  lake build +Solution +Challenge
  lake env lean -j1 -M1536 Audit.lean | python3 scripts/check_audit.py
fi
