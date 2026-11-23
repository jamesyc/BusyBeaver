#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
python3 scripts/literal.py --check
lake build +I3_334.Solution +I3_334.Challenge
lake env lean -j1 -M1536 Audit.lean |
  python3 scripts/check_audit.py
