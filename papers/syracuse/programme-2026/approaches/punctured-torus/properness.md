# Tuning for properness — a genuine Margulis spacetime, and the arithmetic verdict

**Certified by** [`properness.py`](properness.py) (`ALL PROPERNESS ASSERTS PASSED`). Built on
the irreducible Schottky base of [`nontrivial-representation.md`](nontrivial-representation.md).

## Method

On a Schottky linear part the affine action is properly discontinuous (a genuine flat
Lorentzian $3$-manifold) iff the Margulis invariants $\alpha(\gamma)$ all share one sign
(Goldman–Labourie–Margulis). Since
$$\alpha(\gamma)=\langle\tau(\gamma),x^0(\gamma)\rangle\ \text{is \emph{linear} in }\tau=(\tau_a,\tau_b)\in\mathbb{R}^6,$$
"find a proper cocycle" is a linear-feasibility problem over the cone
$\{\alpha(\gamma)>0\ \forall\gamma\}$ — solved here by max–min over the unit sphere
(softmin ascent). $x^0(\gamma)$ is the canonically oriented neutral axis (bracket of the null
eigenvectors); certified to be a consistent class function ($\alpha(\gamma)=\alpha(\gamma^{-1})$,
conjugation-invariant).

## Result 1 — properness is achievable (a real Margulis/BTZ spacetime exists)

A proper cocycle is found, with uniform margin $t^\ast=+1.61$ over all $117$ classes of length
$\le6$, and it stays positive (min $\alpha=+1.61$) over all $693$ classes of length $\le8$:
$$\tau_a=(-0.851,\,0.162,\,0.145),\qquad \tau_b=(0.299,\,0.348,\,0.132).$$
With Drumm's theorem (every Schottky group admits proper affine deformations) this is a
genuine **Margulis spacetime** on the Syracuse-generator base: a future/past-complete flat
$\mathbb{E}^{1,2}$-manifold, once-holed torus $\times\,\mathbb{R}$, generic-BTZ boundary.

## Result 2 — but properness is orthogonal to the Syracuse arithmetic

The probe is negative, and sharply so:

- **No Syracuse-type cocycle can be proper.** Restricting to $\tau_b=0$ (translation
  supported on the "$+1$" of $a$, the literal Syracuse support) the best margin is $\le 0$:
  the $\tau_b=0$ family sits on the *boundary* of properness, never inside it. Properness
  *requires* spreading the translation onto $b$ — exactly what the Syracuse cocycle does not do.
- **The proper cocycle does not see $D\mid S$.** Under the found proper $\tau$ the Syracuse
  cycles have $\alpha(AB)=1.611,\ \alpha(A)=1.619,\ \alpha(AAB)=1.961$ — all positive (it is
  proper) but with **no relation** to $(S,D,S/D)=(1/1,\,1/{-1},\,5/{-1})$. They simply cluster
  near the global margin because they are short classes.

## Verdict

Properness and the Syracuse arithmetic are **orthogonal**. The arithmetic ($D\mid S$, the
endpoint $S/D$) lives in the *null, reducible, degenerate* direction — the boundary of every
deformation space — where the Margulis invariant vanishes identically. Properness lives in an
*open cone* of cocycles, none of which is the arithmetic one, and on which the arithmetic is
invisible. So:

> One can build a genuine Margulis/BTZ spacetime on the Syracuse-generator base, but **not
> one that carries the Syracuse cocycle**, and its Margulis spectrum contains **no trace of
> $D\mid S$**. The Collatz arithmetic is a boundary/degeneracy phenomenon; making the geometry
> genuine (proper) washes it out.

This is the same separation seen at every stage (sub-Markoff, null cocycle, non-free reducible
base), now made quantitative: the literal Syracuse cocycle is *critically improper* (margin
$0$), exactly between the proper and improper cones.
