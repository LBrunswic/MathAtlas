---
id: 0001
title: Conventions — namespace, the sphere of rays, étalé opens, and the bz labels
kind: convention
created: 2026-11-03
---
**Namespace** `Benzecri` (strict `Benzecri.*`, scaffold `BenzecriScaffold.*`, never imported by the
strict library). The core imports Mathlib only (DEC-112); see `docs/CAMPAIGN.md`, "The layering rule".

**S(E) is the projective SPHERE, the space of oriented rays**: `S(E) = (E ∖ {0}) / ℝ₊*` (journal
p. 234, Déf. 3), a double cover of the projective space `P(E) = (E ∖ {0}) / ℝ*`. Benzécri's whole
geometry lives on S(E) — hemispheres, convex and *strict* convex parts, diametrically opposite
points, `GS(n−1, ℝ) = GL(n, ℝ)/ℝ₊*` acting on it — and P(E) is only named. Mathlib's
`Projectivization` (`ℙ K V`) is P(E), **not** S(E): never use it for S. Mathlib's `Module.Ray ℝ E`
(`Mathlib/LinearAlgebra/Ray.lean`, the quotient of `RayVector ℝ E = {v // v ≠ 0}` by `SameRay`) is
S(E) as a type, with no topology at this pin; for a normed `E` it is homeomorphic to
`Metric.sphere (0 : E) 1` by normalisation (`homeomorphUnitSphereProd`, polar coordinates on
`{0}ᶜ`). Index shift: Benzécri writes `S(n−1) = S(ℝⁿ)`, so `S(n)` is the sphere of `ℝⁿ⁺¹`, of
dimension n, and a locally projective n-manifold is modelled on `S(n)` with group `GS(n, ℝ)`.
Projective structures (Déf. 12) are *oriented* in this sense: a `GS`-structure, finer than an
ℝPⁿ-structure.

**"Ouvert étalé" is a spread over the model**: a space with a local homeomorphism to S(n) (resp. ℝⁿ),
i.e. an étalé space over the model, not an open subset of it (« ouvert étalé au-dessus de S(n) »,
§ 1 Prop. 2: a simply connected manifold *with its developing map* is one). Univalent = the
projection is injective. In Lean: a space with an `IsLocalHomeomorph` map to the model; the gx
library's *spread* (`lean-gx/GX/Spread/Basic.lean`) is a different, branched notion (Fox) and is
not this.

**Labels** (papers/benzecri/ledger/ledger.toml): kinds `bzdef: bzprop: bzthm: bzcor: bzlem: bzrem:`,
then `c<chapter>s<§><kind letter><number>_<French keyword>`, e.g. `bzdef:c1s1d11_corps_convexe`,
`bzprop:c1s2p2_base_cone`; a corollary appends `c` to its proposition (`bzcor:c1s3p1c_produit_cercle`);
an unnumbered remark is `r<n>` in order of appearance; the italic unnumbered statement of § 2 is
`bzthm:c1s2_isomorphisme_fonctoriel`; the introduction's results are `bzthm:intro_A`, `_B`, `_C`.
The `bz` prefix keeps every other ledger of the hub from reading a Benzécri docstring mark
(`lean-causal/kb/entries/0024`): numbering restarts in each §, so the § is part of the slug.
