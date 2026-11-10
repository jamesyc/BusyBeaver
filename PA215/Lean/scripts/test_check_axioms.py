import unittest
from check_axioms import validate_report

class AuditReportTests(unittest.TestCase):
    def test_axiom_free(self):
        self.assertEqual(validate_report(['T'], "'T' does not depend on any axioms"), {'T': frozenset()})
    def test_standard(self):
        self.assertEqual(validate_report(['T'], "'T' depends on axioms: [propext, Classical.choice, Quot.sound]")['T'], frozenset({'propext', 'Classical.choice', 'Quot.sound'}))
    def test_forbidden(self):
        for ax in ['sorryAx', 'Lean.ofReduceBool', 'researchAssumption']:
            with self.assertRaises(ValueError):
                validate_report(['T'], f"'T' depends on axioms: [{ax}]")
    def test_missing(self):
        with self.assertRaises(ValueError): validate_report(['T'], '')
    def test_extra(self):
        with self.assertRaises(ValueError): validate_report(['T'], "'T' does not depend on any axioms\n'U' does not depend on any axioms")
    def test_duplicate(self):
        with self.assertRaises(ValueError): validate_report(['T'], "'T' does not depend on any axioms\n'T' does not depend on any axioms")

if __name__ == '__main__': unittest.main()
