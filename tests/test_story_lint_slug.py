#!/usr/bin/env python3
"""A paper slug may contain hyphens (`sbierski-mghd`, `ers-predictability`: tools/roadmap.py
PACKAGE_OF), and its STORY.md fragments are then `## S-sbierski-mghd-1`; story_lint must read them."""
import json
import os
import subprocess
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINT = os.path.join(ROOT, "tools", "story_lint.py")


def lint(slug, story, labels):
    d = os.path.join(tempfile.mkdtemp(), slug)
    os.makedirs(os.path.join(d, "ledger"))
    with open(os.path.join(d, "ledger", "ledger.json"), "w") as f:
        json.dump({"statements": [{"label": l} for l in labels]}, f)
    with open(os.path.join(d, "STORY.md"), "w") as f:
        f.write(story)
    return subprocess.run(["python3", LINT, "--paper", d], capture_output=True, text=True)


class HyphenatedSlug(unittest.TestCase):
    def test_hyphenated_slug_fragments_are_read(self):
        r = lint("sbierski-mghd", "# x\n\n## S-sbierski-mghd-1 One\n\n`mghdthm:MGHD`.\n\n"
                 "## S-sbierski-mghd-2 Two\n\n`mghdthm:MGHD`.\n", ["mghdthm:MGHD"])
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("2 fragments", r.stdout)

    def test_plain_slug_unchanged(self):
        r = lint("bbs", "# x\n\n## S-bbs-1 One\n\n`bbsthm:t`.\n\n## S-bbs-2 Two\n\n`bbsthm:t`.\n",
                 ["bbsthm:t"])
        self.assertEqual(r.returncode, 0, r.stdout)

    def test_wrong_slug_still_fails(self):
        r = lint("sbierski-mghd", "# x\n\n## S-ers-predictability-1 One\n\n`mghdthm:MGHD`.\n",
                 ["mghdthm:MGHD"])
        self.assertNotEqual(r.returncode, 0)

    def test_misnumbered_still_fails(self):
        r = lint("sbierski-mghd", "# x\n\n## S-sbierski-mghd-2 One\n\n`mghdthm:MGHD`.\n",
                 ["mghdthm:MGHD"])
        self.assertNotEqual(r.returncode, 0)


if __name__ == "__main__":
    unittest.main()
