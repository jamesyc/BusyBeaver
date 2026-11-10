import hashlib
from pathlib import Path
import tempfile
import unittest
from check_publication import checked_file, lean_program_sha256, manifest_files


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

    def test_nested_input_manifest(self):
        self.assertEqual(list(manifest_files({
            "parts": [{"path": "a.lean", "sha256": "a"}],
            "aggregator": {"path": "all.lean", "sha256": "b"},
        })), [("a.lean", "a"), ("all.lean", "b")])


if __name__ == "__main__":
    unittest.main()
