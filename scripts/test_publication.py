import hashlib
import json
import shutil
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from check_publication import ROOT, checked_file, lean_program_sha256
from check_table import check_inputs

sys.path.insert(0, str(ROOT / "Lean/metamathematics/scripts"))
import apply_foundation_patch as repairs
import apply_foundation_functions_patch as functions_repair


class Integrity(unittest.TestCase):
    def test_lean_identity_ignores_comments_but_preserves_the_program(self):
        original = '/-- Description. -/\ndef exampleText := "/-literal-/"\n'
        edited = original.replace('Description.', 'A more precise\ndescription.')
        self.assertEqual(lean_program_sha256(original), lean_program_sha256(edited))
        self.assertNotEqual(lean_program_sha256(original),
                            lean_program_sha256(original.replace('literal', 'changed')))

    def test_valid_tampered_missing_and_outside_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "source").write_bytes(b"exact")
            digest = hashlib.sha256(b"exact").hexdigest()
            checked_file(root, "source", digest)
            (root / "source").write_bytes(b"changed")
            for name in ("source", "missing", "../outside"):
                with self.assertRaises(ValueError):
                    checked_file(root, name, digest)

    def test_rejects_divergent_lean_table_labels_and_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("data/pa213.tm", "data/candidate_source.json",
                         "PA213/CandidateTable.lean", "PA213/Machine.lean",
                         "PA213/SourceSites.lean"):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / "Lean" / name, target)
            check_inputs(root)
            for name, old, new in (
                ("CandidateTable.lean", "some (true, true, 94)", "some (false, true, 94)"),
                ("CandidateTable.lean", "List Nat := [74, 0", "List Nat := [73, 0"),
                ("Machine.lean", "target 64", "target 63"),
                ("SourceSites.lean", ".dec 8", ".dec 7"),
            ):
                with self.subTest(name=name, old=old):
                    target = root / "PA213" / name
                    original = target.read_text()
                    self.assertIn(old, original)
                    target.write_text(original.replace(old, new, 1))
                    with self.assertRaises(AssertionError):
                        check_inputs(root)
                    target.write_text(original)


    def test_original_previous_current_and_unknown_bytes(self):
        entries = json.loads((repairs.PATCHES / "MANIFEST.json").read_text())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(repairs, "ROOT", root):
                for entry in entries:
                    target = root / entry["path"]
                    repair = repairs.main if target.stem == "Basic" else functions_repair.main
                    target.parent.mkdir(parents=True, exist_ok=True)
                    original = (repairs.PATCHES / f"Term.{target.stem}.original.lean").read_bytes()
                    for previous in (False, True):
                        with self.subTest(module=target.stem, previous=previous):
                            target.write_bytes(original)
                            if previous:
                                field, definition = {
                                    "Basic": ("func_defined", "listMax_defined"),
                                    "Functions": ("bvar_defined", "nth_defined"),
                                }[target.stem]
                                old = f"  {field} := .mk fun v ↦ by simp [blueprint]"
                                previous_proof = (
                                    f"  {field} := .mk fun v ↦ by\n"
                                    "    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]\n"
                                    "    rw [Semiformula.eval_substs]\n"
                                    f"    simp [{definition}.df]")
                                target.write_bytes(original.replace(old.encode(), previous_proof.encode(), 1))
                                self.assertEqual(hashlib.sha256(target.read_bytes()).hexdigest(),
                                                 repairs.PREVIOUS[target.stem])
                            repair()
                            self.assertEqual(hashlib.sha256(target.read_bytes()).hexdigest(),
                                             entry["working_sha256"])
                            repair()
                    target.write_bytes(b"unexpected source")
                    with self.assertRaises(SystemExit):
                        repair()
                    self.assertEqual(target.read_bytes(), b"unexpected source")



if __name__ == "__main__":
    unittest.main()
