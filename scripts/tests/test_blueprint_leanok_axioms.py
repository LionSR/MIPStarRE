from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from blueprint_lean_sync import BlueprintEntry, LeanDecl  # noqa: E402
from blueprint_leanok_axioms import (  # noqa: E402
    DeclAxiomInfo,
    _decl_leanok_placement,
    audit_blueprint,
    parse_axiom_output,
)


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


class LeanokPlacementClassificationTests(unittest.TestCase):
    """Statement-level \\leanok must downgrade sorry findings to a warning.

    Proof-level \\leanok keeps today's fail-safe behavior (hard error on
    ``sorryAx``), matching the decision recorded in docs/ci-blueprint-sync.md.
    """

    def test_decl_leanok_placement_picks_strongest_marker(self) -> None:
        def mk(statement: bool, proof: bool) -> BlueprintEntry:
            return BlueprintEntry(
                file="ch.tex",
                line=1,
                env_type="theorem",
                label=None,
                lean_decl="Foo.bar",
                has_leanok=statement,
                proof_has_leanok=proof,
            )

        # A decl with both statement-level and proof-level entries is
        # classified by the strongest placement seen across entries.
        self.assertEqual(_decl_leanok_placement([mk(True, False)]), "statement")
        self.assertEqual(_decl_leanok_placement([mk(True, True)]), "proof")
        self.assertEqual(_decl_leanok_placement([mk(False, True)]), "proof")
        self.assertEqual(_decl_leanok_placement([mk(False, False)]), "none")
        self.assertEqual(
            _decl_leanok_placement([mk(True, False), mk(False, True)]),
            "proof",
        )

    def _run_audit_with_axioms(
        self,
        entries: list[BlueprintEntry],
        *,
        axioms_by_decl: dict[str, list[str]],
    ):
        """Drive ``audit_blueprint`` without touching Lean or the filesystem.

        Patches the blueprint/Lean source collection and the axiom harness
        so the test can focus on the placement-aware classification logic.
        """
        fake_lean_decls = {
            entry.lean_decl: LeanDecl(
                file="MIPStarRE/Fake.lean",
                line=1,
                fqn=entry.lean_decl,
                kind="theorem",
                short_name=entry.lean_decl.split(".")[-1],
                end_line=1,
            )
            for entry in entries
        }

        def fake_axiom_checks(decls, **_kwargs):
            return {
                decl: DeclAxiomInfo(exists=True, axioms=list(axioms_by_decl.get(decl, [])))
                for decl in decls
            }

        with (
            mock.patch(
                "blueprint_leanok_axioms.collect_blueprint_entries",
                return_value=entries,
            ),
            mock.patch(
                "blueprint_leanok_axioms.collect_lean_decls",
                return_value=fake_lean_decls,
            ),
            mock.patch(
                "blueprint_leanok_axioms.run_decl_axiom_checks",
                side_effect=fake_axiom_checks,
            ),
        ):
            return audit_blueprint(
                Path("/tmp/fake-repo"),
                lake="lake",
                check_axioms=True,
                warn_missing_leanok=False,
            )

    def _entry(
        self,
        decl: str,
        *,
        has_leanok: bool,
        proof_has_leanok: bool,
    ) -> BlueprintEntry:
        return BlueprintEntry(
            file="src/chapter/ch_test.tex",
            line=1,
            env_type="theorem",
            label=None,
            lean_decl=decl,
            has_leanok=has_leanok,
            proof_has_leanok=proof_has_leanok,
        )

    def test_proof_level_leanok_with_sorry_is_hard_failure(self) -> None:
        entries = [self._entry("Foo.proof", has_leanok=True, proof_has_leanok=True)]
        result = self._run_audit_with_axioms(
            entries,
            axioms_by_decl={"Foo.proof": ["Classical.choice", "sorryAx"]},
        )
        self.assertEqual(len(result.failures), 1)
        self.assertEqual(result.failures[0].placement, "proof")
        self.assertEqual(result.warnings, [])

    def test_statement_only_leanok_with_sorry_is_warning_not_error(self) -> None:
        entries = [self._entry("Foo.stmt", has_leanok=True, proof_has_leanok=False)]
        result = self._run_audit_with_axioms(
            entries,
            axioms_by_decl={"Foo.stmt": ["sorryAx"]},
        )
        # Statement-level only must never hard-fail: the blueprint entry does
        # not claim proof completeness, so downgrade to a warning.
        self.assertEqual(result.failures, [])
        self.assertEqual(len(result.warnings), 1)
        self.assertEqual(result.warnings[0].placement, "statement")
        self.assertIn("statement-level", result.warnings[0].reason)

    def test_proof_level_sorry_free_still_passes(self) -> None:
        entries = [self._entry("Foo.ok", has_leanok=True, proof_has_leanok=True)]
        result = self._run_audit_with_axioms(
            entries,
            axioms_by_decl={"Foo.ok": ["Classical.choice"]},
        )
        self.assertEqual(result.failures, [])
        self.assertEqual(result.warnings, [])
        self.assertEqual(result.pass_count, 1)


if __name__ == "__main__":
    unittest.main()
