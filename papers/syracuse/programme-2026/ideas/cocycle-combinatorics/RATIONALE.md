# cocycle-combinatorics

> **Rewritten objective (2026-06-08):** the formalization is now framed on the **binary step-alphabet** —
> $S=\chi\circ\partial_{\mathrm{odd}}$ (a single twisted Fox derivative), reduction modulo the
> **$\chi$-augmentation** $\ker(1-\chi(w))=\langle D\rangle$, cores $=$ the **Plücker module**. See the
> living note [`STRUCTURE.md`](STRUCTURE.md) (objective §0; verified structure §1–§3; the iterative
> note→read→update reading program §4). The move-calculus framing below is the historical entry point.

## Idea

Build a **calculus of reduction / swap moves on words** (letters in $\mathbb{N}_{\gt 0}$) that
shorten or simplify a word while preserving — *up to a $\mathbb{Z}[1/6]$ unit* — the
differences of cyclic-shift sums $S$ that control the gcd of the rotations. The known starting
move handles a repeated single block: if a pattern $x$ appears twice,
$$S(xyxz)-S(xzxy)=\chi(x)\bigl(S(yxz)-S(zxy)\bigr)\sim S(yxz)-S(zxy),$$
which deletes one copy of $x$ and effectively *reduces* the word. The directing thread is to
**push this further by extracting sub-patterns** — generating new word families whose gcd is
forced small and therefore excludable by the Matveev lower bound on $|2^E-3^o|$. The known
obstacle is that inner sub-patterns **cannot be freely "rolled"** (cyclically rotated) the way
boundary blocks can. The bet is a workaround via a **balanced-swap relation** of the form
$$\chi(x')\,S(xuy)-\chi(x)\,S(x'uy')\;\sim\;S(yx)-S(y'x')\qquad\text{when }\chi(xy)=\chi(x'y'),$$
trading two blocks of equal $\chi$-weight across a fixed inner core $u$.

## Base elements to keep in mind

- **Cocycle rule.** $S(uv)=S(u)+\chi(u)\,S(v)$, with $\chi(u)=2^{|u|}/3^{\operatorname{len}(u)}$,
  where $|u|$ is the **letter-sum** and $\operatorname{len}(u)$ the **number of letters**;
  $S(n)=1$ for every single symbol $n$. (Homogenized form used by the sister approach:
  $S(uv)=Y^{\operatorname{len}v}S(u)+X^{|u|}S(v)$, $X\leftrightarrow 2$, $Y\leftrightarrow 3$.)
- **Units and $\sim$.** $\chi(u)$ is a unit in $\mathbb{Z}[1/6]=\mathbb{Z}[1/2,1/3]$; $a\sim b$
  means $a=(\text{power of }2\text{ and }3)\cdot b$. *Caveat to respect:* the gcd $G$ is **odd**
  so it ignores powers of $2$ ($X$); whether it also ignores powers of $3$ ($Y$) must be checked
  per move, not assumed.
- **$\chi$-equality is rigid.** $\chi(xy)=\chi(x'y')\iff |x|+|y|=|x'|+|y'|$ **and**
  $\operatorname{len}(x)+\operatorname{len}(y)=\operatorname{len}(x')+\operatorname{len}(y')$
  (since $2,3$ are multiplicatively independent). The swap condition constrains *both* weight and
  length.
- **Why the gcd matters.** On a genuine Syracuse cycle with gap word $\tau$ (length $o$,
  gap-sum $E$), $G:=\gcd_{0\le j\lt o}S^{(j)}(\tau)=|2^{E}-3^{o}|=|D|$, and $G$ is odd. Any
  combination of rotation sums is $\equiv 0 \pmod G$, so a move chain collapsing a family to a
  **small core $C$** gives $|2^E-3^o|\le|C|$ (unless $C=0$).
- **The exclusion lever.** Matveev / Baker linear-forms-in-logs gives a **lower** bound on
  $|2^E-3^o|$ that grows with word length. A small-core ceiling below that lower bound kills all
  but finitely many words in the family. The degenerate locus $C=0$ is the classical
  bounded-circuit core (Steiner; Simons–de Weger) — known finite, handled separately.
- **The obstacle, precisely.** Cyclic rotation acts cleanly only at block boundaries (it is a
  shift operator on $S^{(j)}$). Sub-patterns sitting *inside* a word are not rotation images of
  each other, so the repeated-block reduction does not directly apply to them.
- **Arithmetic stays in $\mathbb{Z}[1/6]$.** Every move must be an identity over $\mathbb{Z}[1/6]$
  (equivalently a $\mathbb{Z}[X,Y]$ identity up to the unit convention above).

## What would count as progress

- A small, **verified** move-set (each move a $\mathbb{Z}[X,Y]$ identity, certified up to the unit
  convention) that strictly shortens or simplifies words — extending the repeated-block reduction.
- A precise statement of **which** repeated sub-patterns can be extracted, and under exactly which
  $\chi$-balance conditions the balanced-swap relation holds (or a proof it cannot in general).
- A **new word family** (beyond periodic $w^q w'$) with a provably small core $C$, hence excluded
  via the Matveev bound.
- Or an honest **no-go**: a clean argument that inner sub-patterns genuinely cannot be rolled,
  bounding what the calculus can ever reach.

## Relation to existing work

This is the *move-calculus* sibling of [`approaches/cocycle-combine`](../../approaches/cocycle-combine/RATIONALE.md),
which runs a per-pattern search for compensating $\mathbb{Z}[X,Y]$-combinations. Same kernel and
notation ([`lib/cocycle.py`](../../approaches/cocycle-combine/lib/cocycle.py); structural claims in
[`structure/structure.md`](../../approaches/cocycle-combine/structure/structure.md)). If a move or
family matures into a proof lever, it can graduate to its own approach.
