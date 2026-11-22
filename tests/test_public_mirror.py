"""tools/public_mirror.py: the strip rules remove the third-party material and spare the rest."""
import unittest

from tools import public_mirror as pm


class StripRules(unittest.TestCase):
    def test_third_party_is_stripped(self):
        for p in ("papers/gx/sources/MR1005085/troyanov1991.pdf",
                  "papers/bbs/sources/seppi/fig1.png",
                  "papers/bbs/references/djh1984/pdf/AnnPhys-152-220.pdf",
                  "references/sbierski/text/2001.00001.txt",
                  "references/sbierski/pdf/2001.00001.pdf",
                  "papers/barbot/legacy/orig/barbot.tex",
                  "papers/benzecri/legacy/labeled/benzecri1960_ch2.tex",
                  "papers/syracuse/programme-2026/ideas/cocycle-combinatorics/sources/fox-1953.pdf"):
            self.assertTrue(pm.stripped(p), p)

    def test_pointers_and_own_work_are_kept(self):
        for p in ("papers/gx/sources/MR1005085/NOTE.md",
                  "papers/bbs/sources/seppi/README.md",
                  "papers/bbs/references/djh1984/NOTE.md",
                  "papers/barbot/legacy/MANIFEST.json",
                  "papers/barbot/ledger/ledger.json",
                  "papers/gx/legacy/orig/RamcovGX.tex",
                  "papers/syracuse/programme-2026/approaches/polynomial-root/report.pdf",
                  "references/sbierski/notes/sbierski2022.md",
                  "lean/GFNBounds.lean",
                  "reports/atlas/atlas.html"):
            self.assertFalse(pm.stripped(p), p)


if __name__ == "__main__":
    unittest.main()
