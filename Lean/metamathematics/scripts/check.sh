#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null || { echo "Install the pinned Lean toolchain and put lake on PATH." >&2; exit 1; }
lake env lean --version
python3 scripts/apply_foundation_patch.py
python3 scripts/apply_foundation_functions_patch.py
python3 ../scripts/build_serial.py --metamathematics
python3 scripts/check_axioms.py
