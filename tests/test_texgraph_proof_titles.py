#!/usr/bin/env python3
"""A proof titled by its statement is attached to that statement (T-texgraph-proof-titles).

« Proof of Theorem~\\ref{x} » (a tie before \\ref), « of Proposition \\ref{x} », and a title whose
only \\ref names a statement (« First variation (Remark~\\ref{x}) ») used to fall back to the most
recent statement without a proof: five proofs of yamabe and gx went to the wrong row."""
import os
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import texgraph as pg  # noqa: E402

DOC = r"""\documentclass{article}
\begin{document}
\begin{theorem}\label{thm:a}
A.
\end{theorem}
\begin{proposition}\label{prop:b}
B.
\end{proposition}
\begin{remark}\label{rem:c}
C.
\end{remark}
\begin{lemma}\label{lem:d}
D.
\end{lemma}
\begin{proof}[Proof of Theorem~\ref{thm:a}]
Uses \ref{lem:d}.
\end{proof}
\begin{proof}[of Proposition \ref{prop:b}]
B's proof.
\end{proof}
\begin{proof}[First variation at $u=1$ (Remark~\ref{rem:c})]
C's proof.
\end{proof}
\begin{proof}[Proof sketch]
D's proof, by the fallback.
\end{proof}
\begin{proof}[Proof of Theorem~\ref{eq:nowhere}]
A title naming no statement.
\end{proof}
\end{document}
"""


def graph():
    d = tempfile.mkdtemp()
    with open(os.path.join(d, "paper.tex"), "w") as f:
        f.write(DOC)
    pg.configure(main="paper.tex", notation=())
    return pg.parse_document(d)


def proof_line(g, lab):
    p = g.nodes[lab]["proved_by"]
    return p and g.nodes[p]["line"]


class ProofTitles(unittest.TestCase):
    def test_tie_before_ref(self):
        self.assertEqual(proof_line(graph(), "thm:a"), 15)

    def test_title_starting_of(self):
        self.assertEqual(proof_line(graph(), "prop:b"), 18)

    def test_only_ref_in_parentheses(self):
        self.assertEqual(proof_line(graph(), "rem:c"), 21)

    def test_untitled_falls_back(self):
        self.assertEqual(proof_line(graph(), "lem:d"), 24)

    def test_unresolved_title_is_recorded(self):
        g = graph()
        self.assertEqual([(f, ln) for f, ln, _ in g.unresolved_proof_titles], [("paper.tex", 27)])


if __name__ == "__main__":
    unittest.main()
