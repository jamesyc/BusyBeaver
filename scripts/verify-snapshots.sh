#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# These SHAs are the complete original commit trees, not file-level summaries.
while read -r version expected; do
  actual="$(git rev-parse "HEAD:$version")"
  if [ "$actual" != "$expected" ]; then
    echo "FAIL: $version tree is $actual, expected $expected" >&2
    exit 1
  fi
  echo "PASS: $version matches original tree $expected"
done <<'SNAPSHOTS'
PA215 2456a82396242f8eb44231145a0e7f0efc0b8b7e
PA213 37e0440ebc7a38cea565cce1202043d68f3cdc7d
PA211 8c23186eef0b05e760421c0903cdb3acdfc7f331
SNAPSHOTS
