#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash PA196/scripts/check.sh "$@"
bash ZF209/scripts/check.sh "$@"
bash ZF207/scripts/check.sh "$@"
bash ZF192/scripts/check.sh "$@"
