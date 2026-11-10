#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
case "${1:-}" in
  ""|--full) ;;
  *) echo "Usage: bash scripts/check.sh [--full]" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: bash scripts/check.sh [--full]" >&2
  exit 2
fi
python3 -m unittest discover -s Lean/scripts -p 'test_*.py'
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_publication.py
python3 Lean/scripts/check_source_hygiene.py
python3 Lean/scripts/check_table.py
if [ "${1:-}" = --full ]; then
  bash Lean/metamathematics/scripts/check.sh
fi
