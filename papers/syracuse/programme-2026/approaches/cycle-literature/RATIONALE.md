# Rationale — cycle-literature

## Idea

A living, citation-backed survey of **everything known about cycles of the 3x+1
(Collatz / Syracuse) map**. Not a derivation of our own: a reference shelf that the
*math* approaches (`cycle-gcd`, `diophantine-distribution`, `cocycle-combine`, …) can cite
so we never re-derive, re-prove, or accidentally re-discover a known theorem — and so we
know exactly where the frontier is.

It is organized around four standing questions:

1. **Critical band.** Does every cycle lie in the band $E = E(o) := \min\{e\in\mathbb{Z}_{>0} : 2^e - 3^o > 0\} = \lceil o\log_2 3\rceil$? More generally, what is the exact constraint tying the total halving count $E$ to the odd-step count $o$?
2. **Excluded parity-word patterns.** Which cycle *shapes* (parity words / gap words) are *proven* impossible — circuits, $m$-cycles, etc.?
3. **Divisibility conditions.** What number-theoretic / congruence / linear-forms-in-logarithms constraints must $D = 2^E - 3^o$ and the weighted sum $S$ satisfy?
4. **Bounds.** Smallest element, cycle length, number of cycles — current records and the verification bounds they rest on.

## Why it might work

A clean map of the literature is force-multiplying for every other approach:
it tells us which of our partial results are *new*, which are *re-derivations* (and of
whose theorem), and which open sub-problems are already closed by a citable bound (e.g.
Matveev lower bounds, used informally in `cycle-gcd/eventually-periodic.tex`, have a precise
provenance worth pinning down).

## Known prior art / why it isn't obviously dead

This *is* the prior art. The canonical entry point is **J. C. Lagarias's annotated
bibliography** of the 3x+1 problem (arXiv:math/0309224, continually updated) plus his edited
volume *The Ultimate Challenge: The 3x+1 Problem* (AMS, 2010). The cycle-specific pillars are
Steiner (1977, circuits), Böhm–Sontacchi (1978, closed form), Crandall (1978), Lagarias
(1985, survey), Eliahou (1993, cycle-length bound), Steiner–Simons / Simons–de Weger
(2000s, $m$-cycles), Barina (2021, verification bound), and Hercher (2023, updated records).
This folder collects their exact statements.
