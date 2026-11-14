#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash PA196/scripts/check.sh "$@"
