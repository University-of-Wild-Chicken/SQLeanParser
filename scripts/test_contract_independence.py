"""Guard the independent specification's dependency boundary, without Lean.

The fixed profile and specification may import syntax/catalog data and Std.
Executable validation belongs downstream and must not become a premise of the
declarative specification. New specification dependencies require explicit review.
"""
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {
    'SQLean.SelectContract.Spec',
    'SQLean.SelectContract.Profile',
    'SQLean.SelectContract.ScalarSignatures',
    'SQLean.CatalogSyntax',
    'SQLean.AdvancedSyntax',
    'SQLean.SyntaxBase',
    'Std',
}


class ContractIndependenceTests(unittest.TestCase):
    def test_specification_imports_only_normative_rules_and_immutable_syntax(self):
        pending = ['SQLean.SelectContract.Spec']
        seen = set()
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            self.assertIn(module, ALLOWED, f'unreviewed specification dependency: {module}')
            if module == 'Std':
                continue
            source = (ROOT / (module.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
            for line in source.splitlines():
                match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$', line)
                if match:
                    pending.extend(match.group(1).split())


if __name__ == '__main__':
    unittest.main()
