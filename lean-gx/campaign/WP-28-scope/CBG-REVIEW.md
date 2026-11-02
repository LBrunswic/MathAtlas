# gx review of the CBG interface, Level B `LocalModel` (lean-causal `5080fd2`)

*Read-only review for the gate DEC-61 sets, done 2026-11-01 on node1. It covers
`lean-causal/scaffold/CausalScaffold/CBG/Geometry.lean` (Level A `Geometry`, Level B `LocalModel`
l.326–441, `toPreGeometry`, `Dev`, `Dev.IsUniversal`, `Dev.IsETTMaximal`,
`isETTMaximal_iff_isUniversal`) and `lean-causal/docs/CBG-DESIGN.md`. It reads them against what
gx has (`GX/Singular/Atlas.lean`, `GX/Structure/Basic.lean`, `scaffold/GXScaffold/SingularII/*`),
against gx §4 (`RamcovGX.tex` l.1893–1935 and l.2234–2300), against B21 §1.2
(`papers/gx/sources/2108.12631/src/BTZ_1.tex` l.356–480), and against Sbierski (1309.7591,
pp. 15–18). No Lean is authored here, and nothing below is a ruling.*

## Verdict: **OBJECT**, on one field. With the changes in §4 made, it becomes APPROVE-WITH-CHANGES.

`LocalModel.singularFlatAxioms` cannot be discharged for E₀, for two reasons.

**(a) The field asks for something false.** It asks for `SingularFlatAxioms`, which extends
`BTZAxioms`. That structure has the field `Iplus_eq : I⁺(p) = J⁺(p) ∖ sing₀` at a BTZ point. This
equation is false in E₀. Take the gx metric −2dτdr + dr² + r²dθ².
- A future causal vector has r′ ≥ 0 and 2τ′r′ ≥ r′² + r²θ′². So τ′ ≥ r′/2, and the inequality is
  strict along a timelike curve.
- Take p = (0,0) and x = (s/2, s, θ₀) with s > 0. The radial curve t ↦ (t/2, t, θ₀) is a future
  null curve from p to x, so x ∈ J⁺(p) ∖ sing₀.
- Any future timelike curve from p reaches only points with τ − τ_p > r/2, so x ∉ I⁺(p).
- The same holds in the development D(p) = 0 with u = (1,1,0): the null ray s(1,0,1) lies in
  D(reg) = {B(·,u) < 0}, and it lies on ∂J⁺(0).

ETT.tex l.1351 flags this sentence as "asserted without proof — verify", and the check fails.
The true statement is `J⁺(p′) ∖ sing₀ ⊆ I⁺(p)` for p′ > p on the line. Locally,
I⁺(p) = {r > 0, τ − τ_p > r/2}. This is also the form `BARBOT-INTERFACE.md` already sketches.

**(b) The field asks for second countability of every Hausdorff connected E₀-charted space.**
Second countability is part of the definition of a singular manifold, both in gx
(`def:singular_manifold_locally_connected`, l.474; `SingGXCat.secondCountableTopology`) and in the
thesis (`these.tex:1357`). It is not a theorem of either. DEC-49 proves it in the regular case
(Geroch). For E₀ it is open (design R2). A countable dense set does not suffice, as the Prüfer
surface shows.

Every other field is either true for E₀ or becomes dischargeable after the changes in §4.

## 1. What gx instantiates

**Y = 𝕄 ⊕ E₀.** Y = E₀ alone is excluded by `regularChart`: E₀ is connected and meets
`singY 0`, so it has no component free of singular points. `singY 0 = inr '' {r = 0}`, and
`singY α = ∅` for α ≠ 0. E₀ is ℝ³ with its natural topology (l.2234; the quotient topology is the
natural one, `prop:BTZ_virt_tame`). The presentation Γ\J⁺(Δ) with the BTZ topology
(`defi:BTZtop`, `prop:quotient_chart`) is unproved in gx and is not needed.

**G = the groupoid of a.e.-isomorphisms between open sets of Y.** Y is a singular
(Isom, 𝕄)-manifold, with Reg(Y) = 𝕄 ⊕ {r > 0}. G cannot be a `gxGroupoid`, because no group acts
on Y. G is new gx code, but every groupoid axiom is already in `Atlas.lean`:

| axiom | `Atlas.lean` source |
|---|---|
| composition | `IsAEMorphismOf.comp` |
| inverse | `IsAEMorphism.symm_of_homeomorph` |
| locality | `isAEMorphism_tfae` / `IsAEMorphismOn` (DEC-46 (b)) |
| `ClosedUnderRestriction` | `IsAEMorphismOn` restriction |

G has to contain elements that cross components, from opens of 𝕄 to opens of reg(E₀): the local
inverses of the developing map. `regularChart` needs them.

**The bridge.** An E₀-manifold in gx's sense is a singular manifold (DEC-25) with an X_A-atlas
(`def:atlas`, l.1905). It becomes a Level-B `Str M` as follows:
- At a regular point, `chartAt` is a chart of the maximal a.e. atlas composed with `inl`.
- At a singular point, `chartAt` is an X₀-chart composed with `inr`.
- `HasGroupoid M G` holds for each kind of transition:
  - **inl–inl**: `IsGXAtlas`.
  - **mixed**: the overlap is regular, so the transition is a local isometry
    (`IsAEMorphismOf.regLocusOf_eq`).
  - **inr–inr**: an a.e.-isomorphism between connected opens of E₀. Near a singular point it is a
    restriction of an element of Aut(E₀), by `def:family_singular_manifolds_endowed` together with
    B21 Prop 1.3.
- `chartedSing = Sing`, provided Sing(E₀) is exactly {r = 0}. That is a holonomy fact: no
  (G,X)-chart crosses the line, because the holonomy around it is parabolic.

The converse direction needs `regularChart`.

**This bridge belongs in gx**, in a Section 4 module, since lean-causal never imports lean-gx
(DEC-33). Three gx definitions do not exist yet: `def:family_singular_manifolds_endowed`,
`def:atlas` and `def:analytic_family_model_spaces`. `SingularII/` has only `Developing` and
`Unloopable`. **No E₀ exists anywhere in Lean.** `SingularFlat.lean` states that "the full
structure with `sing 0 ≠ ∅` has no witness".

## 2. The Level B fields, one by one, for E₀

| field | for E₀ | how gx discharges it / cost |
|---|---|---|
| `closedUnderRestriction`, `locallyConnected` | ✓ | G is defined by a local property; ℝ³ ⊕ ℝ³ is locally connected |
| `rigid` (B1) | ✓ **true** | Let U be a preconnected open set. reg(U) is connected and dense, because a line has codimension 2 (B21's "locally connected in M"). Apply Liouville on reg(U), then continuity. This is `IsAEMorphismOf.eq_of_eqOn` (DEC-42), already proved. S |
| `localUnique_sing` (B2, singular point) | ✓ **true** | This is B21 `prop:isom_strong` at α = β = 0 (l.468), i.e. thesis `prop:isom` with the injectivity it calls necessary. B21's proof uses **invariance of domain**, which mathlib does not have. A direct route avoids it: lift to E₀,∞; g∘D = D∘φ̃; g stabilises Δ and normalises ⟨P⟩; then the explicit list of rotation–translations and h_ℓ, with injectivity forcing ℓ = 1. L. **It is needed in this strong form.** On the past side, take U = M ∖ (line below a). It is a CGHD; every p < a on the line is a corresponding point; U ∩ O = reg(O) contains no singular point. Sbierski's Lemma 3.9 walks along such points using Lemma 3.8. So the weaker paper form (`prop:isom`, f defined on all of U) is not enough. Keep the field as stated |
| `localUnique_reg` | ✓ true | The only fully regular component is 𝕄. Liouville for affine maps; e = inl∘g∘inl⁻¹ belongs to G. S |
| `regularChart` | ✓ true, **forces Y to be a sum** | A local inverse of D at a regular point of E₀ lands in 𝕄; for 𝕄 itself take `refl`. S |
| `absolutelyMinimalOn_Y` | ✓ (believed) | `cor:massA_causalite`, but on a **built** E₀ causality. gx has to construct `Causality E₀` from scratch: x ≤_U y means there is a future causal curve in U (`defi:causal_Ealpha`). L |
| `chartIso_mem` | ✓ | The causality is local (a sheaf of preorders), so isometries preserve ≤_U and ≪_U on small opens, and so do elements of Aut(E₀). The mixed elements need ≤_W on regular opens of E₀ to equal the transported Minkowski ≤. M |
| `sing_mem` | ✓ | True by the definition of G together with Sing(E₀) = {r = 0}. S |
| `singularFlatAxioms` | **✗ (a) false, (b) unprovable** | See the verdict. The other fields of `BTZAxioms`/`SingularFlatAxioms` were not all re-checked. This is the **first ever witness** with sing₀ ≠ ∅, so others may fail too. `massive_line` is vacuous. `line` must allow a circle when M is not causal (E₀/⟨τ-translation⟩), and the field's `IsCausal →` guard allows it |
| `curvesExtend` | believed true, **cost XL as stated** | The ETT library leaves it unproved even in the smooth case (kb/0012). The CBG proof consumes it only on developments, which are GH. Barbot's `curvesExtend_of_timeFunction` (with the Geroch time of `SingularGeroch`) discharges it **if the field is restricted to GH M** |
| `isCompact_Jplus/Jminus_…` | believed true | R1. Limit curves at BTZ points; the Jminus version is not dual. L |
| `slice_future` | ✓ | At a BTZ point take τ = −(τ + r). Its gradient has \|d(τ + r)\|² = −3 < 0, so its level sets are spacelike and meet the line once. At regular points use the t-coordinate or the hyperboloids. M |
| `slice_past` | ✓ | τ + r, increasing along causal relations (τ′ ≥ r′/2 ≥ 0). A hyperboloid τ_q **cannot** be used at a BTZ point, since I⁻ = ∅. M |

## 3. What gx's own §4 needs, and whether the interface supplies it

- **B21 Lemma 2.3** ("M Cauchy-maximal, so M₂ embeds into M"). Take M₀ = U, a Cauchy
  sub-development of M obtained with `restrict`. The chain is: Cauchy-maximal ⇒ `IsETTMaximal` ⇒
  (by `isETTMaximal_iff_isUniversal`) universal ⇒ M₂ ↦ M. This needs `IsETTMaximal` to quantify
  only over gx manifolds. As it stands, `Dev` admits carriers that are not second countable, and
  gx's Cauchy-maximality says nothing about them. This is a second reason for change C2.
  M₂ is built by gluing a tube (B21 §2.4, `lem:extension_hausdorff`). gx proves T2 itself, but it
  should reuse a charted-space gluing.
- **DEC-59, uniqueness among gx a.e. morphisms.** It follows from Level-B uniqueness together with
  gx's `IsAEMorphism.eq_of_eqOn`, since the maps agree on `emb '' M₀`. Two bridge lemmas are
  needed:
  - `LocalModel.IsMor ⇒ GX.IsAEMorphism`, needed;
  - the converse for injective maps, **not** needed, which avoids invariance of domain.
- **Causality.** gx should **adopt `chartedCausality`** as its §4.3 causality of E₀-manifolds,
  rather than prove that the two agree.
- **Universes.** `Y : Type u` together with `Str M : Type u` forces Y into M's universe. gx's E₀
  and 𝕄 live in `Type`. Either instantiate at u = 0 or allow `Y : Type v`.

## 4. The requested changes

- **C1 (blocking, in strict `Causal/SingularFlat.lean`).** Replace `BTZAxioms.Iplus_eq` with
  `Iplus_of_lt : ∀ p ∈ S₀, ∀ p' ∈ S₀, C.le ⊤ p p' → p ≠ p' → C.Jplus ⊤ {p'} \ S₀ ⊆ C.Iplus ⊤ {p}`.
  Then audit every downstream use: `K_monotone`'s "x ∈ S, y ∉ S, x ≤ y → x ≪ y" is false at x = p,
  y = (s/2, s, θ). Record a finding against ETT `defi:causal_E0` and against the thesis.
  Add the E₀ counterexample to the paper findings (DEC-27).
- **C2 (blocking).** Make second countability a hypothesis, not an obligation:
  - add `[SecondCountableTopology M]` to the binders of `LocalModel.singularFlatAxioms`,
    `curvesExtend` and `isCompact_*`, and of the corresponding `Geometry` fields;
  - add `[sc : SecondCountableTopology carrier]` to `Dev`;
  - add one new Level B field, `secondCountable_of_cauchy : ∀ M … [ChartedSpace Y M] [HasGroupoid M G], GloballyHyperbolic → ∀ S, IsCauchySurface S → SecondCountableTopology S → SecondCountableTopology M`.
    gx discharges it by the splitting M ≅ S × ℝ (`IsCausalFlow.exists_isCauchySplitting` or
    `geroch_sing_split`). Package 10 uses it for the glued M̄.
- **C3.** Restrict `curvesExtend` (Level A and Level B) to GH M.
- **C4.** Keep `localUnique_sing` as stated (see §2). The docstring should cite B21
  `prop:isom_strong` and the past-side example.
- **C5 (requests to Barbot, not changes to Level B).**
  - Re-send B4/A3 if package 11 finds Level B too weak. The agreement on all of `O ⊓ U` comes from
    Sbierski's causal-convexity argument, through J(x, q) ⊆ U with x on the line, and is not
    supplied by B1/B2.
  - Export package 11's charted-space gluing for gx's B21 Lemma 2.3.
- **Gate.** The first gx deliverable is an E₀ instance of `BTZAxioms` (after C1) on M = E₀ itself.
  That is the satisfiability witness kb/0012 asks for, before packages 4–12 are built on it.

> **Superseded (2026-11-02, DEC-64, f84b69e):** the corrected bundle `SingularFlatAxiomsCorr` proposed here became the strict library `SingularFlatAxioms` itself (`Iplus_of_lt` replaces `Iplus_eq`); the Corr names no longer exist.
