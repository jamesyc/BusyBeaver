#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_source_hygiene.py
python3 scripts/check_table.py
python3 scripts/check_contract4942.py
python3 scripts/check_contract_inputs.py
python3 scripts/check_shard000_inputs.py
python3 scripts/check_original_census.py
python3 scripts/build_serial.py
python3 scripts/check_axioms.py
