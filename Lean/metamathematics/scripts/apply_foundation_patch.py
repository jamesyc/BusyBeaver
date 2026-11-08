#!/usr/bin/env python3
"""Apply the hash-bound Foundation repairs reviewed with PA213."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PATCHES = ROOT / "patches"
PREVIOUS = {
    "Basic": "6b700dc6ea4ea8d60bb17b7d681c46e1ac53ce52a37f5be5b84e4d033c5bb31e",
    "Functions": "2ce4186eda6c7f44fe283e44723582c19a4f216e7bc78e9333336b23a0aacb9d",
}


def main(module="Basic"):
    for entry in json.loads((PATCHES / "MANIFEST.json").read_text()):
        target = ROOT / entry["path"]
        if target.stem != module:
            continue
        digest = hashlib.sha256(target.read_bytes()).hexdigest()
        if digest == entry["working_sha256"]:
            print(f"Reviewed Foundation patch already present: {target.stem}")
            continue
        if digest not in (entry["original_sha256"], PREVIOUS[target.stem]):
            raise SystemExit(f"Refusing unexpected Foundation source bytes: {target}")
        original = (PATCHES / f"Term.{target.stem}.original.lean").read_bytes()
        if hashlib.sha256(original).hexdigest() != entry["original_sha256"]:
            raise SystemExit(f"Preserved original hash mismatch: {target}")
        with tempfile.TemporaryDirectory(dir=target.parent) as directory:
            staged = Path(directory) / target.name
            staged.write_bytes(original)
            subprocess.run(["patch", "--batch", str(staged),
                            str(PATCHES / f"foundation-term-{target.stem.lower()}.patch")], check=True)
            repaired = staged.read_bytes()
            if hashlib.sha256(repaired).hexdigest() != entry["working_sha256"]:
                raise SystemExit(f"Patched hash mismatch: {target}")
            staged.replace(target)
        print(f"Applied reviewed Foundation patch: {target.stem}")


if __name__ == "__main__":
    main()
