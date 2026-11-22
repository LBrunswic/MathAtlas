# Seed — the reduction move and the balanced-swap workaround

**Promise:** medium — Move 1 is now verified and sharpened; the Move 2 thread matured into its own
principle draft ([inner-core-extraction](inner-core-extraction.md)). What remains here is the
move-calculus overview: positional conditions and whether the moves form a terminating rewriting
system.
**Status:** open
**Last iterated:** 2026-06-08

## Thread

Restate the two moves at the heart of the idea and pin down exactly what must be true for the
second one to work. Move 1 (repeated block) is the engine; Move 2 (balanced swap) was the bet that
lets us reach sub-patterns that can't be rolled.

## Working notes

Verified with [`../checks/move_checks.py`](../checks/move_checks.py) (uses the trusted kernel
`approaches/cocycle-combine/lib/cocycle.py`; `Su(w)=S(w)|_{(2,3)}/3^{\,len-1}` reproduces the
draft's $S(uv)=S(u)+\chi(u)S(v)$).

**Foundation — `~` absorbs every unit.** $G=\gcd_j S^{(j)}=|2^E-3^o|$ is **coprime to 6**: it is
odd, and $2^E-3^o\equiv(-1)^E\not\equiv0\pmod 3$. Checked over all words of length $\le5$,
letters $1..4$. So $a\sim b$ (equality up to a power of $2$ *and* $3$) is exactly "G divides one
iff it divides the other" — **3-powers drop too**, not just 2-powers. *(resolves old Q2.)*

**Move 1 — repeated-block reduction: VERIFIED.** $S(xyxz)-S(xzxy)=\chi(x)\bigl(S(yxz)-S(zxy)\bigr)$
holds exactly; in the homogenized kernel the prefactor is the **pure 2-power** $X^{|x|}$ (carries
no 3), so it is doubly a unit. The repeated single block telescopes away cleanly.

**Move 2 — balanced swap: FALSE as stated, but the inner core extracts.** The literal claim
$\chi(x')S(xuy)-\chi(x)S(x'uy')\sim S(yx)-S(y'x')$ fails (182/392 balanced instances give a
non-unit ratio, e.g. $17/15$). The full story is in
[inner-core-extraction](inner-core-extraction.md): the LHS instead equals exactly
$[\chi(x')S(x)-\chi(x)S(x')]+\chi(x)\chi(x')\chi(u)\,[S(y)-S(y')]$ — the inner core $u$ survives
only through the **unit** $\chi(u)$. The obstacle "we cannot roll subwords" is real for the literal
swap, but the inner subword *can* be extracted up to a unit, leaving an outer boundary term.

## Open questions

- [ ] Move 1 deletes a repeated *single* block $x$. State the precise positional condition for a
      repeat to be reducible, directly on the cyclic word (which $(j,k)$ rotation pairs telescope?).
- [ ] Do Moves 1 + (the corrected) inner-core extraction compose into a **terminating rewriting
      system** on words mod $\sim$? What is the normal form, and does some complexity measure
      (length, or #distinct blocks) strictly decrease each step?
- [ ] Reframed target family: since only genuine repeats telescope cleanly, what is the shortest
      word shape with a genuine repeat that Move 1 alone *cannot* fully reduce (e.g. two disjoint
      repeated blocks), and does iterated extraction crush it to a small core?

## Iteration log
- 2026-06-08: scaffold — recorded Move 1 (verified prototype) and Move 2 (proposed); no checks.
- 2026-06-08: ran `checks/move_checks.py`. Verified Move 1 (prefactor $X^{|x|}$, pure 2-power) and
  $G\perp6$ (so `~` drops 2- and 3-powers). Found Move 2 **false as stated** (182/392 non-unit
  ratios) with a clean symbolic obstruction ($\chi(xuy)=1$ impossible), and the exact corrected
  identity. Spun the corrected identity into `inner-core-extraction.md`; resolved old Q1, Q2;
  trimmed the Move-2 questions into the principle draft.
