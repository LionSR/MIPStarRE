#!/usr/bin/env python3
"""Regression tests for artifact-based GitHub Pages site assembly."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "assemble-pages-site.sh"


class AssemblePagesSiteTests(unittest.TestCase):
    def _write_blueprint_component(self, components: Path) -> None:
        blueprint = components / "site-blueprint"
        (blueprint / "homepage").mkdir(parents=True)
        (blueprint / "blueprint").mkdir()
        (blueprint / "homepage" / "index.html").write_text("home")
        (blueprint / "blueprint" / "index.html").write_text("blueprint")
        (blueprint / "blueprint.pdf").write_text("pdf")

    def test_assembles_preserved_site_layout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp_dir:
            root = Path(tmp_dir)
            components = root / "components"
            self._write_blueprint_component(components)
            (components / "site-docs" / "docs").mkdir(parents=True)
            (components / "site-badges").mkdir()

            (components / "site-docs" / "docs" / "index.html").write_text("docs")
            (components / "site-badges" / "sorries.json").write_text("{}")

            site = root / "site"
            subprocess.run([SCRIPT, components, site], check=True)

            self.assertEqual((site / "index.html").read_text(), "home")
            self.assertEqual(
                (site / "blueprint" / "index.html").read_text(), "blueprint"
            )
            self.assertEqual((site / "blueprint.pdf").read_text(), "pdf")
            self.assertEqual((site / "docs" / "index.html").read_text(), "docs")
            self.assertEqual((site / "badges" / "sorries.json").read_text(), "{}")

    def test_rejects_missing_required_blueprint_component(self) -> None:
        with tempfile.TemporaryDirectory() as tmp_dir:
            root = Path(tmp_dir)
            result = subprocess.run(
                [SCRIPT, root / "components", root / "site"],
                capture_output=True,
                text=True,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("site-blueprint component missing", result.stdout)

    def test_rejects_missing_docs_or_badges_to_preserve_live_components(self) -> None:
        for missing, expected in [
            ("docs", "site-docs component missing"),
            ("badges", "site-badges component missing"),
        ]:
            with self.subTest(missing=missing), tempfile.TemporaryDirectory() as tmp_dir:
                root = Path(tmp_dir)
                components = root / "components"
                self._write_blueprint_component(components)
                if missing != "docs":
                    (components / "site-docs" / "docs").mkdir(parents=True)
                if missing != "badges":
                    badges = components / "site-badges"
                    badges.mkdir()
                    (badges / "sorries.json").write_text("{}")

                result = subprocess.run(
                    [SCRIPT, components, root / "site"],
                    capture_output=True,
                    text=True,
                )

                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stdout)


if __name__ == "__main__":
    unittest.main()
