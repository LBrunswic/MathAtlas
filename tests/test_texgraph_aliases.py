#!/usr/bin/env python3
"""A \\ref to a statement's secondary \\label resolves to the statement (T-ledger-secondary-labels).

texgraph keys a statement on its first \\label. External papers (Barbot, BBS) get a hub label
inserted first, ahead of the authors' own, and the authors' \\ref's target their own label: those
must resolve to the statement, not dangle."""
import os
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import texgraph as pg  # noqa: E402

DOC = r"""\documentclass{article}
\begin{document}
\section{S}
\begin{theorem}\label{bthm:a}\label{a-orig}
A statement.
\end{theorem}
\begin{lemma}\label{blem:b}
Uses Theorem~\ref{a-orig} and Theorem~\ref{bthm:a}, and \ref{nowhere}.
\end{lemma}
\begin{theorem}\label{bthm:c}\label{c-orig}
Refers to itself: \ref{c-orig}.
\end{theorem}
\end{document}
"""


class SecondaryLabels(unittest.TestCase):
    def graph(self):
        d = tempfile.mkdtemp()
        with open(os.path.join(d, "paper.tex"), "w") as f:
            f.write(DOC)
        pg.configure(main="paper.tex", notation=())
        return pg.parse_document(d)

    def test_secondary_label_resolves(self):
        g = self.graph()
        refs = {(a, b) for a, b, k in g.edges if k == "ref"}
        self.assertIn(("blem:b", "bthm:a"), refs)
        self.assertNotIn(("blem:b", "?a-orig"), {(a, b) for a, b, k in g.edges if k == "dangling"})

    def test_ref_records_its_resolution_for_the_ledger(self):
        g = self.graph()
        to = {r["target"]: r.get("to") for r in g.nodes["blem:b"]["refs"]}
        self.assertEqual(to["a-orig"], "bthm:a")
        self.assertIsNone(to["bthm:a"])

    def test_unknown_label_still_dangles(self):
        g = self.graph()
        self.assertIn(("blem:b", "?nowhere", "dangling"), g.edges)

    def test_no_self_edge_through_an_alias(self):
        g = self.graph()
        self.assertNotIn(("bthm:c", "bthm:c", "ref"), g.edges)
        self.assertNotIn(("bthm:c", "?c-orig", "dangling"), g.edges)

    def test_primary_key_unchanged(self):
        g = self.graph()
        self.assertIn("bthm:a", g.nodes)
        self.assertNotIn("a-orig", g.nodes)


if __name__ == "__main__":
    unittest.main()
