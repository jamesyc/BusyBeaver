#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_source_hygiene.py
python3 scripts/check_table.py
python3 scripts/build_serial.py
python3 scripts/check_axioms.py
