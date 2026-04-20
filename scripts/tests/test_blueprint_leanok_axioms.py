from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from blueprint_leanok_axioms import parse_axiom_output


class BlueprintLeanokAxiomsTests(unittest.TestCase):
    def test_parse_axiom_output_classifies_sorry_and_missing_decls(self) -> None:
        harness = Path("/tmp/BlueprintLeanokAxioms.lean")
        output = "\n".join(
            [
                "'Foo.good' does not depend on any axioms",
                "'Foo.bad' depends on axioms: [Classical.choice, sorryAx]",
                f"{harness}:5:0: error: unknown constant 'Foo.missing'",
            ]
        )
        results = parse_axiom_output(
            output,
            ["Foo.good", "Foo.bad", "Foo.missing"],
            harness_path=harness,
            line_to_decl={3: "Foo.good", 4: "Foo.bad", 5: "Foo.missing"},
            returncode=1,
        )
        self.assertIsNotNone(results)
        self.assertTrue(results["Foo.good"].exists)
        self.assertFalse(results["Foo.good"].sorry)
        self.assertTrue(results["Foo.bad"].exists)
        self.assertTrue(results["Foo.bad"].sorry)
        self.assertFalse(results["Foo.missing"].exists)

    def test_parse_axiom_output_returns_none_on_global_harness_failure(self) -> None:
        harness = Path("/tmp/BlueprintLeanokAxioms.lean")
        output = f"{harness}:1:0: error: import Foo.Bar failed"
        results = parse_axiom_output(
            output,
            ["Foo.good"],
            harness_path=harness,
            line_to_decl={3: "Foo.good"},
            returncode=1,
        )
        self.assertIsNone(results)


if __name__ == "__main__":
    unittest.main()
