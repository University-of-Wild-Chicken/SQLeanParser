"""Check the actual scope contract with the project's lexical import scanner."""
import unittest

from check_lean_trust import ROOT, check_specification_independence, local_import_closure


ALLOWED = {
    "SQLean.ScopeContract.Spec", "SQLean.ScopeContract.Embedding",
    "SQLean.AdvancedSyntax", "SQLean.SyntaxBase", "Std",
}

class ScopeContractIndependence(unittest.TestCase):
    def test_import_boundary(self):
        for name in ("Spec", "Embedding"):
            self.assertTrue((ROOT / "SQLean/ScopeContract" / f"{name}.lean").is_file())
        seen = local_import_closure(ROOT, "SQLean.ScopeContract.Embedding")
        self.assertLessEqual(seen, ALLOWED)
        self.assertIn("SQLean.ScopeContract.Spec", seen)
        check_specification_independence(ROOT)

if __name__ == "__main__":
    unittest.main()
