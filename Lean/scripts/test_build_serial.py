from pathlib import Path
import tempfile
import unittest
from build_serial import build_order

class Plan(unittest.TestCase):
    def plan(self, files):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for name, text in files.items():
                p = root.joinpath(*name.split('.')).with_suffix('.lean')
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(text)
            return build_order(root, 'PA215')
    def test_dependency_order_and_shared_import(self):
        self.assertEqual(self.plan({'PA215':'import PA215.A PA215.B',
          'PA215.A':'import Std PA215.B','PA215.B':''}), ['PA215.B','PA215.A','PA215'])
    def test_ignores_comments_and_drafts(self):
        self.assertEqual(self.plan({'PA215':'/- import PA215.Bad -/\nimport Std',
          'PA215.Draft':'import PA215.Missing'}), ['PA215'])
    def test_missing_fails(self):
        with self.assertRaises(ValueError): self.plan({'PA215':'import PA215.Missing'})
    def test_cycle_fails(self):
        with self.assertRaises(ValueError): self.plan({'PA215':'import PA215.A','PA215.A':'import PA215'})
    def test_public_import(self):
        self.assertEqual(self.plan({'PA215':'public import PA215.A','PA215.A':''}), ['PA215.A','PA215'])

    def test_multiple_package_roots(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'PA215.lean').write_text('')
            meta = root / 'meta'
            meta.mkdir()
            (meta / 'PA215PA.lean').write_text('import PA215')
            self.assertEqual(build_order(root, 'PA215PA', {'PA215PA':meta}),
                             ['PA215','PA215PA'])

    def test_shared_support_needs_no_standalone_root(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'PA215').mkdir()
            (root / 'PA215/Support.lean').write_text('')
            (root / 'PA211.lean').write_text('import PA215.Support')
            self.assertEqual(build_order(root), ['PA215.Support', 'PA211'])
            meta = root / 'meta'
            meta.mkdir()
            (meta / 'PA211PA.lean').write_text('import PA211')
            self.assertEqual(build_order(root, 'PA211PA', {'PA211PA': meta}),
                             ['PA215.Support', 'PA211', 'PA211PA'])

    def test_frozen_flat_modules_resolve_in_their_own_package(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            meta = root / 'meta'
            meta.mkdir()
            (root / 'TreeSite.lean').write_text('')
            (root / 'User211Source.lean').write_text('import TreeSite')
            (meta / 'User211LiteralEndpoint.lean').write_text('import User211Source')
            (meta / 'PA211PA.lean').write_text('import User211LiteralEndpoint')
            self.assertEqual(build_order(root, 'PA211PA', {'PA211PA': meta}),
                             ['TreeSite', 'User211Source', 'User211LiteralEndpoint', 'PA211PA'])

if __name__ == '__main__': unittest.main()
