#!/usr/bin/env python3
"""A paper's proof macros are read as proofs (T-barbot-proof-macros).

Barbot writes `\\preua … \\fin` and `\\preuda{label}` instead of a proof environment, so before this
the ledger saw none of his proofs and papers/barbot had no statement edges."""
import os
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import texgraph as pg  # noqa: E402

DOC = r"""\documentclass{article}
\begin{document}
\begin{lema}\label{blem:a}
A first lemma.
\end{lema}
\preua
It uses nothing.\fin
\begin{lema}\label{blem:b}
A second lemma.\fin
\end{lema}
\preua By Lemma \ref{blem:a}.
The proof has no box.
\begin{lema}\label{blem:c}
A third lemma.
\end{lema}
\begin{lema}\label{blem:d}
A fourth lemma.
\end{lema}
\preuda{blem:c} By Lemma \ref{blem:b}. \fin
\end{document}
"""
MACROS = [["\\preua", "\\fin"], ["\\preuda", "\\fin", "Proof of \\ref{#1}"]]


def graph(macros):
    d = tempfile.mkdtemp()
    with open(os.path.join(d, "paper.tex"), "w") as f:
        f.write(DOC)
    pg.configure(main="paper.tex", notation=(), env_alias={"lema": "lemma"}, proof_macros=macros)
    return pg.parse_document(d)


def proved(g, lab):
    return g.nodes[lab]["proved_by"]


class ProofMacros(unittest.TestCase):
    def test_macro_proofs_attach(self):
        g = graph(MACROS)
        self.assertIsNotNone(proved(g, "blem:a"))
        self.assertIsNotNone(proved(g, "blem:b"))     # a proof with no box ends at the next lemma
        self.assertIsNotNone(proved(g, "blem:c"))     # \preuda{blem:c} names its statement
        self.assertIsNone(proved(g, "blem:d"))

    def test_refs_in_macro_proofs_are_edges(self):
        g = graph(MACROS)
        refs = {(a, b) for a, b, k in g.edges if k == "ref"}
        self.assertIn((proved(g, "blem:b"), "blem:a"), refs)     # the ledger's dep blem:b -> blem:a
        self.assertIn((proved(g, "blem:c"), "blem:b"), refs)

    def test_a_box_inside_a_statement_stays_in_its_text(self):
        g = graph(MACROS)
        self.assertIn("\\fin", g.nodes["blem:b"]["text"])

    def test_line_numbers_unchanged(self):
        g = graph(MACROS)
        self.assertEqual(g.nodes["blem:d"]["line"], DOC.split("\n").index(r"\begin{lema}\label{blem:d}") + 1)
        p = g.nodes[proved(g, "blem:c")]
        self.assertEqual(p["end_line"], len(DOC.split("\n")) - 2)

    def test_counts_proofs_per_macro(self):
        graph(MACROS)
        self.assertEqual(pg.PROOF_MACROS_USED, {"\\preua": 2, "\\preuda": 1})

    def test_no_macros_no_change(self):
        g = graph(None)
        self.assertFalse(any(n["kind"] == "proof" for n in g.nodes.values()))
        self.assertEqual(pg.proof_macros_to_env(DOC), DOC)


if __name__ == "__main__":
    unittest.main()
