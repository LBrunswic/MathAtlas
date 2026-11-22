# A non-trivial representation

**Certified by** [`nontrivial_rep.py`](nontrivial_rep.py) (`ALL NON-TRIVIAL-REP ASSERTS PASSED`).
Answers "find a non-trivial (irreducible) representation," given that the *literal* Syracuse
cocycle forces reducibility ([`admissible-representations`](admissible-representations.md): the
character $\lambda=(\tfrac32,\tfrac12)$ needs a shared eigenline).

## The idea

Keep the two generators' **conjugacy data** — multipliers $\tfrac32$ and $2$, hence the
*exact* Syracuse traces $\operatorname{tr}A=\tfrac5{\sqrt6}$, $\operatorname{tr}B=\tfrac3{\sqrt2}$ —
but **reposition their axes** so they no longer share a fixed point. Reducibility is not
conjugation‑invariant data; moving the axes apart leaves the trace coordinates
$(\operatorname{tr}A,\operatorname{tr}B)$ fixed and changes only $\operatorname{tr}AB$.

## The representation (explicit, certified)

$$
A=\begin{pmatrix}1.02062&0.01021\\4.08248&1.02062\end{pmatrix}\ (\text{axis }\approx0,\ \mu=\tfrac32),\quad
B=\begin{pmatrix}8.13173&-7.05339\\7.07107&-6.01041\end{pmatrix}\ (\text{axis }\approx1,\ \mu=2).
$$

- **Same generator data as Syracuse:** $\operatorname{tr}A=\tfrac5{\sqrt6}$, $\operatorname{tr}B=\tfrac3{\sqrt2}$ (lengths $\log\tfrac32,\log2$). ✅
- **Irreducible:** $\operatorname{tr}[A,B]=827\neq2$. ✅
- **Discrete & free:** the four isometric circles $I(A^{\pm1}),I(B^{\pm1})$ are pairwise disjoint ⇒ Schottky (Klein combination). ✅ It is a **convex‑cocompact once‑holed torus**.
- **Boundary = generic BTZ.** $[A,B]$ is *hyperbolic* ($|\operatorname{tr}|\gg2$), so the puncture is a **geodesic funnel** (length $13.4$) — a *generic* (non‑extreme) BTZ black hole, **not** the extreme BTZ. The extreme/cusp limit ($\operatorname{tr}[A,B]=-2$) stays unreachable (sub‑Markoff), exactly as before.

## What it shows — and what it costs

- **Cycles are genuine closed geodesics** (all loxodromic). But their lengths are now
  **word‑dependent**, *not* the Baker quantity: `ab`$\to6.56$, `aab`$\to8.06$ (vs Baker
  $0.29,0.12$). Only pure‑generator words keep it: `a`$\to0.4055=\log\tfrac32$. The clean
  arithmetic length spectrum $|E\log2-o\log3|$ lived *only* in the abelian/reducible base.
- **The Margulis invariant wakes up.** With an affine cocycle on this base the signed
  Lorentzian lengths are nonzero (`ab`$\to-0.82$, `a`$\to+10$, `aab`$\to+3.1$): the action is
  **free**, unlike the reducible base where $\alpha\equiv0$. (Signs are *mixed* here, so this
  particular cocycle is not yet a *proper* Margulis spacetime — Goldman–Labourie–Margulis
  properness needs one sign; tunable.)
- **The cocycle is no longer literally $S$.** As proved, $S$ does not transport to an
  irreducible base; the affine part here is a free choice in $H^1(F_2,\mathbb{R}^{1,2}_{\Ad L})$,
  not the canonical Syracuse class. **Which deformation canonically carries $S$ remains open.**

## Reading

This is the honest "non‑trivial" object: a real Fuchsian convex‑cocompact once‑holed torus
with the Syracuse generator‑lengths, whose closed geodesics include the Syracuse classes. It
exists, it is discrete, the Margulis invariants are non‑degenerate — but it buys this by
**giving up the literal cocycle and the arithmetic length spectrum**, both of which are
properties of the degenerate reducible base. The short generators (sub‑Markoff) force a long
boundary geodesic (pinched handle, huge $\operatorname{tr}[A,B]$): the geometric signature of
sub‑Markoffness.
