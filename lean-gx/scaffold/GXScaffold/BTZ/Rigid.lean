import GXScaffold.BTZ.Model

/-!
# `GXScaffold.BTZ.Rigid` — the rigidity fields of the local model `𝕄 ⊕ 𝔼₀`

Package WP-41c (WAVE5-PLAN.md, WP-39c). The model data of the CBG local model
(`Causal.CBG.LocalModel`, `lean-causal` pinned `731ed99`, `Causal/CBG/Geometry.lean`) for gx's
Section 4: `Y = 𝕄 ⊕ 𝔼₀` (`GX.E0Y`), the a.e.-isomorphism groupoid `G` (`GX.e0Groupoid`), the
singular loci `sing_0 = Sing(𝔼₀)`, `sing_α = ∅` for `α ≠ 0` (`GX.e0SingY`), and the fields of
`LocalModel` that are about `Y`, `G` and `singY` alone, each a standalone theorem with the field's
statement verbatim (`Y`, `G`, `singY` substituted). **0 `sorry`.** (Round 3: `typeAgreement` is
false as stated, with a proved counterexample, SCOPE (c); it holds verbatim at the tips in `𝕄`, and its
convergence form holds at every regular tip.)

No ledger label of `RamcovGX.tex` is certified here: the fields are CBG-interface obligations
(`BARBOT-INTERFACE.md`, "gx's E₀ obligations"), not rows of the paper. Cited, unmarked:
B21 `lem:liouville` (`BTZ_1.tex:361`), B21 `prop:isom_strong` (`BTZ_1.tex:468–475`).

> **Lemma** (`lem:liouville`). Let `M →(f,g) N` be two a.e. `(G,X)`-morphisms with `M` connected.
> If `f` and `g` agree on a non-empty open subset `𝒲` of `M`, then they agree on the whole `M`.

> **Proposition** (`prop:isom_strong`). Let `α, β ∈ ℝ₊` with `α ≠ 2π`, and let `𝒰` be an open
> connected subset of `𝔼^{1,2}_α` containing a singular point and let `φ : reg(𝒰) → 𝔼^{1,2}_β` be a
> `𝔼`-morphism. If `φ` is injective then `α = β` and `φ` is the restriction of an element of
> `Isom(𝔼^{1,2}_α)`.

* `closedUnderRestriction` — `GX.e0Groupoid_closedUnderRestriction` (instance).
* `t2Y` — `GX.e0Y_t2Space` (instance).
* `isOpen_regY` — `GX.e0_isOpen_regY`.
* `dense_regY` — `GX.e0_dense_regY`.
* `sing_mem` — `GX.e0_sing_mem`.
* `regularChart` — `GX.e0_regularChart`.
* `localUnique_reg` — `GX.e0_localUnique_reg`.
* `rigid` (B1, B21 `lem:liouville`) — `GX.e0_rigid`.
* `localUnique_sing` (B2, B21 `prop:isom_strong` at `α = β = 0`) — **`GX.e0_localUnique_sing`**,
  closed: its local core `GX.e0_localUnique_sing_core` is proved by the route of CBG-REVIEW §2,
  without invariance of domain (below), and rigidity `GX.e0_eqOn_of_eqOn_open` globalises it.
* `localUnique_sing_adherent` — stated verbatim as `GX.E0LocalUniqueSingAdherent C` over a causality
  `C` of `Y` (SCOPE (b)) and reduced, for every `C`, to a property of `C`'s diamonds alone
  (`GX.e0_localUniqueSingAdherent_of_region`); that property is discharged for the model causality
  by WP-41f (`GX.E0LM.e0_localUniqueSingAdherent`, `GXScaffold.BTZ.LocalModel` §6b).
* `typeAgreement` — stated verbatim as `GX.E0TypeAgreement C`. **Finding: false for `𝕄 ⊕ 𝔼₀` at
  the regular points of `𝔼₀`** (SCOPE (c); DEC-27 counterexample **proved**:
  `GX.e0_not_typeAgreement_of`, for every `C` with two hypotheses on `C` alone, discharged for the
  model causality in `campaign/WP-41c/TypeAgreementD.lean` as `GX.e0_not_typeAgreement_D`). Its
  **convergence form** `GX.E0TypeAgreementTendsto C` (`MapClusterPt z₀ (𝓝[U] y₀) f` strengthened to
  `Tendsto f (𝓝[U] y₀) (𝓝 z₀)`, the hypothesis `CBG/FromModel`'s `germ_ext_nonBTZ` holds) is
  **proved** for every `C` in which straight timelike segments of the two chart maps are
  chronological (`GX.e0_typeAgreementTendsto_of`, hypotheses `GX.E0TASegLt`); the two segment
  hypotheses for `GX.E0.causalityYBTZ` are proved in `campaign/WP-41c/TypeAgreementD.lean`
  (`GXScaffold.BTZ.Causality` imports this file, so they cannot be proved here). **At the tips in
  `𝕄` the field holds verbatim** (`MapClusterPt`): `GX.E0TypeAgreementInl C`, the field restricted to
  `y₀ = inl m` (`GX.E0TypeAgreement.inl`), is proved for every `C` with the `𝕄` segment hypothesis
  (`GX.e0_typeAgreement_inl_of`): a connected `U ⊆ 𝕄` carries no holonomy, so `f` has one global
  development (`GX.e0TA_global_rep_inl`).
* Bonus instances: `locallyConnected` (`GX.e0Y_locallyConnectedSpace`).

**The proof of `localUnique_sing`** (`GX.e0_localUnique_core_of_region`,
`GX.btzE0_localUnique_core_of_region`). A box around the axis point, in log-polar coordinates
`(log r + iθ, t)` a convex set `B ⊆ ℂ × ℝ` invariant under `θ ↦ θ + s` (`GX.e0Box`,
`GX.e0BoxSec`). (1) `f` read on `𝔼₀` lifts through the covering `{r > 0} → reg 𝔼₀`
(mathlib's `IsCoveringMapOn.existsUnique_continuousMap_lifts`, GX's
`isCoveringMapOn_orbitMk_cylPos`); (2) Liouville (`exists_smul_eq_on_of_isLocalHomeomorphOn`)
gives `D ∘ f̃ = g ∘ D`; (3) one turn `θ ↦ θ + 2π` is a deck shift `k`, so `g P = Pᵏ g`
(`btzDevM_smul`, rigidity of `Isom(𝐌³)`); (4) in null coordinates `g` preserves the fixed line
`ℝu` of `Pᵏ` (`GX.map_line_of_conj`), hence is axis-preserving with `b(Lw) = b(w)/λ`, `λ > 0`
(`GX.IsAxisAff`, `GX.isAxisAff_of_mem`), and `D⁻¹ g D` is an explicit homeomorphism of the
cylinder, `r ↦ r/λ`, `t ↦ (λ⁻¹ − λ)r + λt + s₀` (`GX.btzConj`, `GX.IsAxisAff.homeo`), with
`D⁻¹ g D (m·y) = (km)·D⁻¹ g D (y)` (`GX.IsAxisAff.btzConj_smul`); (5) injectivity forces `k = ±1`:
for `|k| ≥ 2` the intermediate value theorem on the angle along one circle produces two points of
`reg U` in distinct `Γ`-orbits with one image (`GX.btzConj_winding`, `GX.e0BoxSec_orbit_ne`); (6)
`D⁻¹ g D` descends to `Aut(𝔼₀)` (`GX.btzE0Descend`), an element of `G` (`GX.e0Lift_mem`).
`k = −1` (a reflection `θ ↦ −θ`) is not excluded and need not be.

**The proof of `typeAgreement`'s convergence form** (`GX.e0_typeAgreementTendsto_of`). At a regular
tip `y₀ = ι(v₀)`, `ι` the chart map `inl ∘ nullToMink` (`GX.e0TAInl`) or `inr ∘ [·] ∘ D⁻¹`
(`GX.e0TAInr`), the diamond contains the cone region `K = B(v₀, ε) ∩ I^∓(v₀)` read through `ι`
(`GX.e0TA_reg_of_chart`, by `GX.E0TASegLt`). If the limit `z₀` were a BTZ point: `f ∘ ι` lifts on
the convex `K` through `{r > 0} → reg 𝔼₀`, and Liouville gives `D ∘ L = g · nullToMink`
(`GX.e0TA_lift`); `r → 0` and `nullQ (D L) = r² − r t → 0` put `g · v₀` on the line `ℝu`
(`GX.e0TA_tip`). Past cone: `g` maps it below the null plane `b = 0`, where `D` takes no value.
Future cone: `P` fixes `g · v₀`, so `g⁻¹ P g` sends a point `u` of the cone to a point `u'` of the
cone with `[L u'] = [L u]`, against injectivity (`GX.e0TA_absurd`).

## Hypothesis checklist

| interface | here |
|---|---|
| `Y = 𝕄 ⊕ Σ_α 𝔼_α` | `𝕄 ⊕ 𝔼₀` (the dispatch's `Y`): `Causal.Minkowski 2 ⊕ GX.BTZE0` |
| `G`: on the regular part the `(G,X)`-morphisms, near a singular point the restrictions of `Aut(𝔼₀)` | `G` = the a.e.-isomorphisms (BARBOT-INTERFACE, "Instance: `Y = 𝕄 ⊕ E₀`, `G` = a.e.-isomorphisms"): open partial homeomorphisms which, with their inverse, map `Reg` into `Reg` and are there, in the charts of `𝕄` and of the maximal a.e. atlas of `𝔼₀`, locally translations by `Isom(𝐌³)` |
| `sing_α(Y)` | `sing_0 = Sing(Y) = inr '' Sing(𝔼₀)` (`= inr '' {r = 0}` by `GX.btz_sing`), `sing_α = ∅` for `α ≠ 0` |
| `localUnique_sing`: `U` connected, `0 ≤ α₀` | carried verbatim; the local core uses neither (connectedness enters only through rigidity) |
| `typeAgreement`: `MapClusterPt z₀ (𝓝[U] y₀) f` | ✓ verbatim at tips in `𝕄` (`GX.E0TypeAgreementInl`); ✗ false at regular tips in `𝔼₀` (SCOPE (c), counterexample `GX.e0_not_typeAgreement_of`), where it is **strengthened** to `Tendsto f (𝓝[U] y₀) (𝓝 z₀)` (`GX.E0TypeAgreementTendsto`, every other hypothesis verbatim, `U` connected unused) |

## SCOPE (disclosed)

* (a) `rigid` is proved directly (`GX.e0_rigid`, by propagation along the preconnected dense
  `reg(U)`) rather than through the strict `IsAEMorphismOf.eq_of_eqOn` (DEC-42): that lemma is
  about global maps of a preconnected singular manifold, and an element of `G` is a partial
  homeomorphism of the sum `Y`; the bridge would need `Y`'s a.e. atlas as a singular structure on
  each source, which is longer than the direct proof.
* (b) `typeAgreement` and `localUnique_sing_adherent` mention the model causality `causalityY`,
  WP-41e's `GX.E0.causalityYBTZ` (`GXScaffold.BTZ.Causality`), which now imports this file; so they
  are stated as propositions over a causality `C`, and every argument that needs `C` is isolated in
  a named hypothesis on `C` alone: `hdiam` of `GX.e0_localUniqueSingAdherent_of_region` (discharged
  by WP-41f) and `GX.E0TASegLt` (discharged in `campaign/WP-41c/TypeAgreementD.lean`). For a
  causality whose chronological diamonds are empty these hypotheses fail, and we expect both
  statements to fail; this is not proved here, so no theorem over all `C` is claimed.
* (c) **`typeAgreement` is false as stated for `𝕄 ⊕ 𝔼₀`** (finding; **proved**,
  `GX.e0_not_typeAgreement_of`, section "The counterexample"). At a regular
  tip `y₀ ∈ 𝔼₀` the domain `U` may wind once around the axis and come back to `y₀` from a spacelike
  direction, and along that end the cluster value of `f` is a BTZ point. In null coordinates:
  `v₀ = (0, 1, 0) = D(1, 0, 1)`, `P = parab 2π`, `P v₀ = (4π², 1, 2π)`;
  `H := parab' (−1/2π) ∘ (· − P v₀)` (an orthochronous isometry, `H(P v₀) = 0 ∈ ℝu`,
  `H v₀ = (−4π², 1, 0)`); `Ũ := A ∪ T` with `A = B(v₀, 1/5) ∩ I⁻(v₀)` (`GX.e0CEA`) and the tube
  `T = ⋃_{0<s<1} B((1 − s) P v₀ + s d, s/100)`, `d = (−1/10, 9/10, 0)` (`GX.e0CET`);
  `U := [D⁻¹ Ũ]`, `f [D⁻¹ w] := [D⁻¹ H w]` (`GX.e0CEf`). Then `U` is open and connected, contains
  the past diamond of `O = [D⁻¹ B(v₀, 1/5)]` at `y₀`, and `f` is an injective local
  `G`-structomorphism (one partial homeomorphism `GX.e0CEe ∈ G` carries it): `|c| < b` on `H(Ũ)`,
  and `Ũ` meets its `Pᵏ`-translates nowhere (`GX.e0CE_injOn`: `b`, `nullQ` and `c − 2πk b` are the
  invariants; `nullQ > 0` on `A`, `< 0` near the apex of `T`). Along the apex end of `T`,
  `f → [apex, 0] ∈ sing₀` (`GX.e0CE_mapClusterPt`),
  while `y₀ ∉ sing₀`. At the tips in `𝕄` there is no domain holonomy, and the field is proved
  (`GX.e0_typeAgreement_inl_of`).
  The convergence form (`GX.E0TypeAgreementTendsto`) is what is proved; it is what
  `CBG/FromModel`'s `germ_ext_nonBTZ` can supply (there `ψ` converges along the piece, `hT`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `731ed99`.
-/

namespace GX

open Set Filter Topology Function
open scoped Real

attribute [local instance] btzE0Structure

/-! ### The model space, its charts, its regular part -/

section E0Model

/-- **The model space** `Y = 𝕄 ⊕ 𝔼₀` of gx's Section 4 local model. -/
abbrev E0Y : Type := Causal.Minkowski 2 ⊕ BTZE0

instance e0_nonempty_btzE0 : Nonempty BTZE0 := ⟨orbitMk (GammaA (2 * Real.pi)) (DInfty.apex, 0)⟩

/-- The inclusion of `𝕄` as an open partial homeomorphism. -/
noncomputable def e0Inl : OpenPartialHomeomorph (Causal.Minkowski 2) E0Y :=
  IsOpenEmbedding.inl.toOpenPartialHomeomorph Sum.inl

/-- The inclusion of `𝔼₀` as an open partial homeomorphism. -/
noncomputable def e0Inr : OpenPartialHomeomorph BTZE0 E0Y :=
  IsOpenEmbedding.inr.toOpenPartialHomeomorph Sum.inr

/-- **The regular charts of `Y`**: the identity of `𝕄`, and the charts of the maximal a.e. atlas
of `𝔼₀`. -/
noncomputable def e0Atlas : Set (OpenPartialHomeomorph E0Y (Causal.Minkowski 2)) :=
  insert e0Inl.symm
    ((fun c => e0Inr.symm.trans c) '' aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)

/-- **The regular part** of `Y`. -/
def e0Reg : Set E0Y := support e0Atlas

/-- **The singular loci** of `Y`: `sing_0` is the singular part, `sing_α = ∅` for `α ≠ 0`. -/
def e0SingY (α : ℝ) : Set E0Y := {y | α = 0 ∧ y ∉ e0Reg}


@[simp] theorem e0Inl_source : e0Inl.source = univ :=
  IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

@[simp] theorem e0Inl_target : e0Inl.target = range Sum.inl :=
  IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

@[simp] theorem e0Inr_source : e0Inr.source = univ :=
  IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

@[simp] theorem e0Inr_target : e0Inr.target = range Sum.inr :=
  IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

theorem e0Inl_symm_source : e0Inl.symm.source = range Sum.inl := by
  rw [OpenPartialHomeomorph.symm_source]; exact IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

theorem e0Inr_symm_source : e0Inr.symm.source = range Sum.inr := by
  rw [OpenPartialHomeomorph.symm_source]; exact IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

@[simp] theorem e0Inl_symm_inl (m : Causal.Minkowski 2) : e0Inl.symm (Sum.inl m) = m :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _

@[simp] theorem e0Inr_symm_inr (x : BTZE0) : e0Inr.symm (Sum.inr x) = x :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _

@[simp] theorem e0Inl_apply (m : Causal.Minkowski 2) : e0Inl m = Sum.inl m := rfl

@[simp] theorem e0Inr_apply (x : BTZE0) : e0Inr x = Sum.inr x := rfl

theorem mem_e0InrChart_source {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)} {y : E0Y} :
    y ∈ (e0Inr.symm.trans c).source ↔ ∃ x ∈ c.source, y = Sum.inr x := by
  rw [OpenPartialHomeomorph.trans_source, e0Inr_symm_source]
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by simpa using hx⟩

@[simp] theorem e0InrChart_inr (c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)) (x : BTZE0) :
    (e0Inr.symm.trans c) (Sum.inr x) = c x := by
  simp [OpenPartialHomeomorph.coe_trans]

theorem inl_notMem_e0InrChart_source (c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2))
    (m : Causal.Minkowski 2) : Sum.inl m ∉ (e0Inr.symm.trans c).source := by
  rw [mem_e0InrChart_source]; rintro ⟨x, -, h⟩; cases h

theorem inr_notMem_e0Inl_symm_source (x : BTZE0) : Sum.inr x ∉ e0Inl.symm.source := by
  rw [e0Inl_symm_source]; rintro ⟨m, h⟩; cases h

theorem mem_e0Atlas {c : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} :
    c ∈ e0Atlas ↔ c = e0Inl.symm ∨
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, c = e0Inr.symm.trans c' := by
  simp only [e0Atlas, mem_insert_iff, mem_image]
  constructor
  · rintro (h | ⟨c', hc', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c', hc', rfl⟩
  · rintro (h | ⟨c', hc', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c', hc', rfl⟩

theorem e0Inl_symm_mem_e0Atlas : e0Inl.symm ∈ e0Atlas := mem_insert _ _

theorem e0InrChart_mem_e0Atlas {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :
    e0Inr.symm.trans c ∈ e0Atlas :=
  mem_insert_of_mem _ ⟨c, hc, rfl⟩

/-- A chart of `Y` at a point of `𝕄` is the identity of `𝕄`. -/
theorem eq_of_mem_e0Atlas_inl {c : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)}
    (hc : c ∈ e0Atlas) {m : Causal.Minkowski 2} (hm : Sum.inl m ∈ c.source) : c = e0Inl.symm := by
  rcases mem_e0Atlas.1 hc with h | ⟨c', -, rfl⟩
  · exact h
  · exact absurd hm (inl_notMem_e0InrChart_source c' m)

/-- A chart of `Y` at a point of `𝔼₀` is a chart of `𝔼₀`'s maximal a.e. atlas. -/
theorem exists_of_mem_e0Atlas_inr {c : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)}
    (hc : c ∈ e0Atlas) {x : BTZE0} (hx : Sum.inr x ∈ c.source) :
    ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, c = e0Inr.symm.trans c' ∧
      x ∈ c'.source := by
  rcases mem_e0Atlas.1 hc with rfl | ⟨c', hc', rfl⟩
  · exact absurd hx (inr_notMem_e0Inl_symm_source x)
  · obtain ⟨x', hx', h⟩ := mem_e0InrChart_source.1 hx
    cases h
    exact ⟨c', hc', rfl, hx'⟩

theorem inl_mem_e0Reg (m : Causal.Minkowski 2) : Sum.inl m ∈ e0Reg :=
  mem_support.2 ⟨_, e0Inl_symm_mem_e0Atlas, by rw [e0Inl_symm_source]; exact ⟨m, rfl⟩⟩

theorem inr_mem_e0Reg_iff {x : BTZE0} :
    Sum.inr x ∈ e0Reg ↔ x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
  constructor
  · intro h
    obtain ⟨c, hc, hx⟩ := mem_support.1 h
    obtain ⟨c', hc', -, hx'⟩ := exists_of_mem_e0Atlas_inr hc hx
    exact mem_support.2 ⟨c', hc', hx'⟩
  · intro h
    obtain ⟨c', hc', hx'⟩ := mem_support.1 h
    exact mem_support.2 ⟨_, e0InrChart_mem_e0Atlas hc', mem_e0InrChart_source.2 ⟨x, hx', rfl⟩⟩

theorem e0Reg_eq : e0Reg = range Sum.inl ∪
    Sum.inr '' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
  ext (m | x)
  · simp [inl_mem_e0Reg]
  · simp [inr_mem_e0Reg_iff]

theorem isOpen_e0Reg : IsOpen e0Reg := isOpen_support _

theorem e0RegSet_eq : {y : E0Y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} = e0Reg := by
  ext y
  simp only [mem_setOf_eq, e0SingY, not_and, not_not]
  exact ⟨fun h => h 0 le_rfl rfl, fun h _ _ _ => h⟩

/-- **Chart changes** of `Y`: near every point of an overlap two regular charts differ by an
element of `Isom(𝐌³)`. -/
theorem e0Atlas_eventually_smul_eq {c c' : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)}
    (hc : c ∈ e0Atlas) (hc' : c' ∈ e0Atlas) {y : E0Y} (hy : y ∈ c.source) (hy' : y ∈ c'.source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 y, c' z = g • c z := by
  rcases y with m | x
  · rw [eq_of_mem_e0Atlas_inl hc hy, eq_of_mem_e0Atlas_inl hc' hy']
    exact ⟨1, Eventually.of_forall fun z => (one_smul _ _).symm⟩
  · obtain ⟨d, hd, rfl, hx⟩ := exists_of_mem_e0Atlas_inr hc hy
    obtain ⟨d', hd', rfl, hx'⟩ := exists_of_mem_e0Atlas_inr hc' hy'
    obtain ⟨g, hg⟩ := (isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2)
      BTZE0).1.1.eventually_smul_eq hd hd' hx hx'
    refine ⟨g, ?_⟩
    rw [← IsOpenEmbedding.inr.map_nhds_eq x, eventually_map]
    filter_upwards [hg] with w hw
    simpa using hw

end E0Model

/-! ### The groupoid of a.e.-isomorphisms -/

section Groupoid

/-- The pointwise property defining `G`: continuous at `x`, and at a regular `x`, `f x` regular
and `f` read in any regular charts at `x` and `f x` is near `x` a translation by `Isom(𝐌³)`. -/
def E0RegAt (f : E0Y → E0Y) (x : E0Y) : Prop :=
  ContinuousAt f x ∧ (x ∈ e0Reg → f x ∈ e0Reg ∧
    ∀ c ∈ e0Atlas, ∀ c' ∈ e0Atlas, x ∈ c.source → f x ∈ c'.source →
      ∃ g : Causal.Flat.isom 2, ∀ᶠ y in 𝓝 x, c' (f y) = g • c y)

/-- Chart independence: one pair of regular charts suffices. -/
theorem e0RegAt_of_exists {f : E0Y → E0Y} {x : E0Y} (hf : ContinuousAt f x)
    (h : ∃ c ∈ e0Atlas, ∃ c' ∈ e0Atlas, x ∈ c.source ∧ f x ∈ c'.source ∧
      ∃ g : Causal.Flat.isom 2, ∀ᶠ y in 𝓝 x, c' (f y) = g • c y) : E0RegAt f x := by
  obtain ⟨c, hc, c', hc', hx, hfx, g, hg⟩ := h
  refine ⟨hf, fun _ => ⟨mem_support.2 ⟨c', hc', hfx⟩, fun d hd d' hd' hxd hfxd => ?_⟩⟩
  obtain ⟨a, ha⟩ := e0Atlas_eventually_smul_eq hd hc hxd hx
  obtain ⟨b, hb⟩ := e0Atlas_eventually_smul_eq hc' hd' hfx hfxd
  refine ⟨b * g * a, ?_⟩
  filter_upwards [hf.eventually hb, hg, ha] with y h1 h2 h3
  rw [h1, h2, h3, mul_smul, mul_smul]

theorem E0RegAt.comp {f f' : E0Y → E0Y} {x : E0Y} (hf' : E0RegAt f' (f x)) (hf : E0RegAt f x) :
    E0RegAt (f' ∘ f) x := by
  refine ⟨hf'.1.comp hf.1, fun hx => ?_⟩
  obtain ⟨hfx, hfc⟩ := hf.2 hx
  obtain ⟨hffx, hf'c⟩ := hf'.2 hfx
  refine ⟨hffx, fun c hc c'' hc'' hxc hffxc => ?_⟩
  obtain ⟨c', hc', hfxc'⟩ := mem_support.1 hfx
  obtain ⟨a, ha⟩ := hfc c hc c' hc' hxc hfxc'
  obtain ⟨b, hb⟩ := hf'c c' hc' c'' hc'' hfxc' hffxc
  refine ⟨b * a, ?_⟩
  filter_upwards [hf.1.eventually hb, ha] with y h1 h2
  rw [Function.comp_apply, h1, h2, mul_smul]

theorem E0RegAt.congr {f f' : E0Y → E0Y} {x : E0Y} (hf : E0RegAt f x) (h : f' =ᶠ[𝓝 x] f) :
    E0RegAt f' x := by
  refine ⟨hf.1.congr h.symm, fun hx => ?_⟩
  obtain ⟨hfx, hc⟩ := hf.2 hx
  have hx' : f' x = f x := h.eq_of_nhds
  refine ⟨hx' ▸ hfx, fun c hc₁ c' hc' hxc hfxc => ?_⟩
  obtain ⟨g, hg⟩ := hc c hc₁ c' hc' hxc (hx' ▸ hfxc)
  refine ⟨g, ?_⟩
  filter_upwards [hg, h] with y h1 h2
  rw [h2, h1]

theorem e0RegAt_id (x : E0Y) : E0RegAt id x :=
  ⟨continuousAt_id, fun hx => ⟨hx, fun _ hc _ hc' hxc hxc' =>
    e0Atlas_eventually_smul_eq hc hc' hxc hxc'⟩⟩

/-- The pregroupoid of a.e.-isomorphisms of `Y`. -/
noncomputable def e0Pregroupoid : Pregroupoid E0Y where
  property f s := ∀ x ∈ s, E0RegAt f x
  comp {f f' u v} hf hf' _ _ _ := fun x hx => (hf' (f x) hx.2).comp (hf x hx.1)
  id_mem x _ := e0RegAt_id x
  locality {f u} _ h x hx := by
    obtain ⟨v, -, hxv, hp⟩ := h x hx
    exact hp x ⟨hx, hxv⟩
  congr {f f' u} hu heq hf x hx :=
    (hf x hx).congr (Filter.eventually_of_mem (hu.mem_nhds hx) heq)

/-- **The groupoid `G` of the local model**: the a.e.-isomorphisms between open subsets of
`Y = 𝕄 ⊕ 𝔼₀`. -/
noncomputable def e0Groupoid : StructureGroupoid E0Y := e0Pregroupoid.groupoid

theorem mem_e0Groupoid_iff {e : OpenPartialHomeomorph E0Y E0Y} :
    e ∈ e0Groupoid ↔ (∀ x ∈ e.source, E0RegAt e x) ∧ ∀ x ∈ e.target, E0RegAt e.symm x :=
  Iff.rfl

/-- **`closedUnderRestriction`** of the local model. -/
instance e0Groupoid_closedUnderRestriction : ClosedUnderRestriction e0Groupoid := by
  refine ⟨fun {e} he s _ => ?_⟩
  rw [mem_e0Groupoid_iff] at he ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact he.1 x (by rw [OpenPartialHomeomorph.restr_source] at hx; exact hx.1)
  · exact he.2 x (by rw [OpenPartialHomeomorph.restr_target] at hx; exact hx.1)

/-- Elements of `G` map regular points to regular points. -/
theorem mapsTo_e0Reg_of_mem {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) {x : E0Y}
    (hx : x ∈ e.source) (hr : x ∈ e0Reg) : e x ∈ e0Reg :=
  ((mem_e0Groupoid_iff.1 he).1 x hx).2 hr |>.1

/-- Elements of `G` preserve the regular part, both ways. -/
theorem mem_e0Reg_iff_of_mem {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid)
    {x : E0Y} (hx : x ∈ e.source) : x ∈ e0Reg ↔ e x ∈ e0Reg := by
  refine ⟨mapsTo_e0Reg_of_mem he hx, fun h => ?_⟩
  have := ((mem_e0Groupoid_iff.1 he).2 (e x) (e.map_source hx)).2 h |>.1
  rwa [e.left_inv hx] at this

/-- An open partial homeomorphism of `Y` which is, between two regular charts, a translation by
`Isom(𝐌³)` on its whole source, belongs to `G`. -/
theorem mem_e0Groupoid_of_chart_eq {e : OpenPartialHomeomorph E0Y E0Y}
    {c₁ c₂ : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} (hc₁ : c₁ ∈ e0Atlas)
    (hc₂ : c₂ ∈ e0Atlas) (hs : e.source ⊆ c₁.source) (ht : e.target ⊆ c₂.source)
    (g : Causal.Flat.isom 2) (h : ∀ y ∈ e.source, c₂ (e y) = g • c₁ y) : e ∈ e0Groupoid := by
  refine mem_e0Groupoid_iff.2 ⟨fun x hx => e0RegAt_of_exists (e.continuousAt hx)
    ⟨c₁, hc₁, c₂, hc₂, hs hx, ht (e.map_source hx), g,
      Filter.eventually_of_mem (e.open_source.mem_nhds hx) h⟩,
    fun x hx => e0RegAt_of_exists (e.continuousAt_symm hx)
    ⟨c₂, hc₂, c₁, hc₁, ht hx, hs (e.map_target hx), g⁻¹,
      Filter.eventually_of_mem (e.open_target.mem_nhds hx) fun y hy => ?_⟩⟩
  rw [← e.right_inv hy, e.left_inv (e.map_target hy), h _ (e.map_target hy), inv_smul_smul]

/-- The connected component of a point of `𝕄` lies in `𝕄`. -/
theorem connectedComponent_inl_subset (m : Causal.Minkowski 2) :
    connectedComponent (Sum.inl m : E0Y) ⊆ range Sum.inl :=
  isPreconnected_connectedComponent.subset_isClopen isClopen_range_inl
    ⟨Sum.inl m, mem_connectedComponent, m, rfl⟩

/-- The connected component of a point of `𝔼₀` lies in `𝔼₀`. -/
theorem connectedComponent_inr_subset (x : BTZE0) :
    connectedComponent (Sum.inr x : E0Y) ⊆ range Sum.inr :=
  isPreconnected_connectedComponent.subset_isClopen isClopen_range_inr
    ⟨Sum.inr x, mem_connectedComponent, x, rfl⟩

end Groupoid

/-! ### The fields `t2Y`, `isOpen_regY`, `dense_regY`, `sing_mem`, `regularChart` -/

section Fields

/-- **`t2Y`**: the model is Hausdorff. -/
instance e0Y_t2Space : T2Space E0Y :=
  haveI := (btz_instances btz_two_pi_ne_zero).1
  inferInstance

/-- `𝔼₀` is locally connected (`locallyConnected` of the local model, with `𝕄`). -/
instance e0Y_locallyConnectedSpace : LocallyConnectedSpace E0Y :=
  haveI := (btz_instances btz_two_pi_ne_zero).2.1
  inferInstance

/-- **`isOpen_regY`** for `Y = 𝕄 ⊕ 𝔼₀`. -/
theorem e0_isOpen_regY : IsOpen {y : E0Y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} := by
  rw [e0RegSet_eq]; exact isOpen_e0Reg

theorem dense_e0Reg : Dense e0Reg := by
  intro y
  rcases y with m | x
  · exact subset_closure (inl_mem_e0Reg m)
  · have hx : x ∈ closure (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :=
      (isPortly_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0).dense x
    refine closure_mono ?_ (mem_closure_image continuous_inr.continuousAt hx)
    rintro _ ⟨x', hx', rfl⟩
    exact inr_mem_e0Reg_iff.2 hx'

/-- **`dense_regY`** for `Y = 𝕄 ⊕ 𝔼₀`. -/
theorem e0_dense_regY : Dense {y : E0Y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} := by
  rw [e0RegSet_eq]; exact dense_e0Reg

/-- **`sing_mem`** for `Y = 𝕄 ⊕ 𝔼₀`: elements of `G` preserve the type of a point. -/
theorem e0_sing_mem : ∀ e ∈ e0Groupoid, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α →
    (y ∈ e0SingY α ↔ e y ∈ e0SingY α) := by
  intro e he y hy α _
  simp only [e0SingY, mem_setOf_eq, mem_e0Reg_iff_of_mem he hy]

/-- **`regularChart`** for `Y = 𝕄 ⊕ 𝔼₀`: a regular point is moved by an element of `G` into `𝕄`
(the identity at a point of `𝕄`; at a regular point of `𝔼₀`, a chart of its maximal a.e. atlas
followed by the inclusion of `𝕄`). -/
theorem e0_regularChart : ∀ y : E0Y, (∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α) → ∃ e ∈ e0Groupoid,
    y ∈ e.source ∧ ∀ z ∈ connectedComponent (e y), ∀ α : ℝ, 0 ≤ α → z ∉ e0SingY α := by
  intro y hy
  have hy' : y ∈ e0Reg := by rw [← e0RegSet_eq]; exact hy
  have hinl : ∀ m : Causal.Minkowski 2, ∀ z ∈ connectedComponent (Sum.inl m : E0Y),
      ∀ α : ℝ, 0 ≤ α → z ∉ e0SingY α := by
    intro m z hz α _ hzs
    obtain ⟨m', rfl⟩ := connectedComponent_inl_subset m hz
    exact hzs.2 (inl_mem_e0Reg m')
  rcases y with m | x
  · exact ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, mem_univ _, hinl m⟩
  · obtain ⟨c, hc, hxc⟩ := mem_support.1 (inr_mem_e0Reg_iff.1 hy')
    set e : OpenPartialHomeomorph E0Y E0Y := (e0Inr.symm.trans c).trans e0Inl
    have hes : e.source = (e0Inr.symm.trans c).source := by
      simp only [e, OpenPartialHomeomorph.trans_source]
      rw [show e0Inl.source = univ from IsOpenEmbedding.toOpenPartialHomeomorph_source _ _]
      simp
    have hmem : e ∈ e0Groupoid := by
      refine mem_e0Groupoid_of_chart_eq (e0InrChart_mem_e0Atlas hc) e0Inl_symm_mem_e0Atlas
        hes.le ?_ 1 fun z _ => ?_
      · intro z hz
        rw [OpenPartialHomeomorph.trans_target] at hz
        rw [e0Inl_symm_source]
        obtain ⟨m, rfl⟩ : z ∈ range Sum.inl := by
          have := hz.1; rwa [show e0Inl.target = range Sum.inl from
            IsOpenEmbedding.toOpenPartialHomeomorph_target _ _] at this
        exact ⟨m, rfl⟩
      · simp [e, OpenPartialHomeomorph.coe_trans]
    refine ⟨e, hmem, ?_, ?_⟩
    · rw [hes]; exact mem_e0InrChart_source.2 ⟨x, hxc, rfl⟩
    · have : e (Sum.inr x) = Sum.inl (c x) := by simp [e, OpenPartialHomeomorph.coe_trans]
      rw [this]; exact hinl _

/-- `𝔼₀` has a singular point (its axis). -/
theorem btzE0_exists_notMem_reg :
    ∃ x : BTZE0, x ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
  refine ⟨orbitMk (GammaA (2 * Real.pi)) (DInfty.apex, 0), ?_⟩
  have h := btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0
  change _ ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
  rw [h]
  exact ⟨(DInfty.apex, 0), rfl, rfl⟩

/-- The component of a point of `𝔼₀` contains a singular point. -/
theorem exists_mem_connectedComponent_inr_sing (x : BTZE0) :
    ∃ z ∈ connectedComponent (Sum.inr x : E0Y), z ∈ e0SingY 0 := by
  haveI := (btz_instances btz_two_pi_ne_zero).2.2.2
  obtain ⟨w, hw⟩ := btzE0_exists_notMem_reg
  refine ⟨Sum.inr w, ?_, rfl, fun h => hw (inr_mem_e0Reg_iff.1 h)⟩
  have hc : IsPreconnected (range (Sum.inr : BTZE0 → E0Y)) :=
    isPreconnected_range continuous_inr
  exact hc.subset_connectedComponent ⟨x, rfl⟩ ⟨w, rfl⟩

/-- A point whose component has no singular point lies in `𝕄`. -/
theorem mem_range_inl_of_forall {y : E0Y}
    (h : ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α → z ∉ e0SingY α) : y ∈ range Sum.inl := by
  rcases y with m | x
  · exact ⟨m, rfl⟩
  · obtain ⟨z, hz, hzs⟩ := exists_mem_connectedComponent_inr_sing x
    exact absurd hzs (h z hz 0 le_rfl)

/-- The element `inl ∘ g ∘ inl⁻¹` of `G`, defined on `𝕄`. -/
noncomputable def e0InlSmul (g : Causal.Flat.isom 2) : OpenPartialHomeomorph E0Y E0Y :=
  e0Inl.symm.trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans e0Inl)

theorem e0InlSmul_source (g : Causal.Flat.isom 2) : (e0InlSmul g).source = range Sum.inl := by
  simp [e0InlSmul]

theorem e0InlSmul_apply (g : Causal.Flat.isom 2) (m : Causal.Minkowski 2) :
    e0InlSmul g (Sum.inl m) = Sum.inl (g • m) := by
  simp [e0InlSmul, OpenPartialHomeomorph.coe_trans]

theorem e0InlSmul_mem (g : Causal.Flat.isom 2) : e0InlSmul g ∈ e0Groupoid := by
  refine mem_e0Groupoid_of_chart_eq e0Inl_symm_mem_e0Atlas e0Inl_symm_mem_e0Atlas
    (by rw [e0InlSmul_source, e0Inl_symm_source]) ?_ g ?_
  · intro z hz
    have : z ∈ e0Inl.target := by
      simp only [e0InlSmul, OpenPartialHomeomorph.trans_target] at hz
      exact hz.1.1
    rw [e0Inl_symm_source, ← e0Inl_target]; exact this
  · intro y hy
    rw [e0InlSmul_source] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [e0InlSmul_apply, e0Inl_symm_inl, e0Inl_symm_inl]

/-- **`localUnique_reg`** for `Y = 𝕄 ⊕ 𝔼₀` (Liouville in `𝕄`): an injective local
`G`-structomorphism on a connected open `U` of a fully regular component, into fully regular
components, is the restriction of `inl ∘ g ∘ inl⁻¹` for one `g ∈ Isom(𝐌³)`. Injectivity is not
used. -/
theorem e0_localUnique_reg : ∀ U : Set E0Y, IsOpen U → IsConnected U →
    (∀ y ∈ U, ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α → z ∉ e0SingY α) →
    ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α → w ∉ e0SingY α} →
    ∃ e ∈ e0Groupoid, (∀ y ∈ U, connectedComponent y ⊆ e.source) ∧ EqOn f e U := by
  intro U hU hUc hreg f hf _ hmaps
  have hUl : U ⊆ range Sum.inl := fun y hy => mem_range_inl_of_forall (hreg y hy)
  have hfl : ∀ y ∈ U, f y ∈ range Sum.inl := fun y hy => mem_range_inl_of_forall (hmaps hy)
  have hloc : ∀ y ∈ U, ∃ g : Causal.Flat.isom 2,
      ∀ᶠ z in 𝓝 y, e0Inl.symm (f z) = g • e0Inl.symm z := by
    intro y hy
    obtain ⟨e, he, hfe, hye⟩ := hf y hy hy
    obtain ⟨m, rfl⟩ := hUl hy
    have hey : e (Sum.inl m) = f (Sum.inl m) := (hfe ⟨hy, hye⟩).symm
    obtain ⟨m', hm'⟩ := hfl _ hy
    obtain ⟨-, hc⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hye).2 (inl_mem_e0Reg m)
    obtain ⟨g, hg⟩ := hc _ e0Inl_symm_mem_e0Atlas _ e0Inl_symm_mem_e0Atlas
      (by rw [e0Inl_symm_source]; exact ⟨m, rfl⟩)
      (by rw [e0Inl_symm_source, hey, ← hm']; exact ⟨m', rfl⟩)
    refine ⟨g, ?_⟩
    filter_upwards [hg, hU.mem_nhds hy, e.open_source.mem_nhds hye] with z h1 h2 h3
    rw [hfe ⟨h2, h3⟩]; exact h1
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected (e := e0Inl.symm) hUc.isPreconnected
    (by rw [e0Inl_symm_source]; exact hUl) hloc
  refine ⟨e0InlSmul g, e0InlSmul_mem g, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨m, rfl⟩ := hUl hy
    rw [e0InlSmul_source]; exact connectedComponent_inl_subset m
  · obtain ⟨m, rfl⟩ := hUl hy
    obtain ⟨m', hm'⟩ := hfl _ hy
    have := hg _ hy
    rw [← hm', e0Inl_symm_inl, e0Inl_symm_inl] at this
    rw [← hm', e0InlSmul_apply, this]

end Fields

/-! ### Null-coordinate algebra of the axis-preserving isometries -/

section NullAxis

/-- The paper's `D` in null coordinates (`x₀ = 0`, `v = (−1, 1, 0)`). -/
theorem btzDev_e0_apply (y : DInfty × ℝ) :
    btzDev 0 btzV0 y = (y.2 - y.1.r + y.1.r * y.1.θ ^ 2, y.1.r, y.1.r * y.1.θ) := by
  rw [btzDev_coords]; simp [btzV0]; ring

theorem btzDev_e0_b (y : DInfty × ℝ) : (btzDev 0 btzV0 y).2.1 = y.1.r := by
  rw [btzDev_e0_apply]

theorem nullQ_btzDev_e0 (y : DInfty × ℝ) : nullQ (btzDev 0 btzV0 y) = y.1.r ^ 2 - y.1.r * y.2 := by
  rw [btzDev_e0_apply, nullQ]; ring

theorem DInfty.continuous_r' : Continuous DInfty.r := by
  refine DInfty.continuous_of_posEmb ?_ fun V hV => ?_
  · exact continuous_fst.comp continuous_subtype_val
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hV
    refine ⟨ε, hε, fun p hp => h ?_⟩
    rw [DInfty.apex_r, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg p.r_nonneg]
    exact hp

/-- An explicit inverse of `D` (null coordinates) on `{b > 0} ∪ ℝu`. -/
noncomputable def btzDevInv (w : ℝ × ℝ × ℝ) : DInfty × ℝ :=
  if h : 0 < w.2.1 then (DInfty.posEmb ⟨(w.2.1, w.2.2 / w.2.1), h⟩, w.1 + w.2.1 - w.2.2 ^ 2 / w.2.1)
  else (DInfty.apex, w.1)

theorem btzDevInv_btzDev (y : DInfty × ℝ) : btzDevInv (btzDev 0 btzV0 y) = y := by
  rw [btzDev_e0_apply, btzDevInv]
  rcases y.1.pos_or_eq_apex with h | h
  · rw [dif_pos h]
    refine Prod.ext (DInfty.ext rfl ?_) ?_
    · simp only [DInfty.posEmb_θ]; field_simp
    · simp only; field_simp; ring
  · have h0 : ¬ 0 < y.1.r := by rw [h]; simp
    rw [dif_neg h0]
    refine Prod.ext h.symm ?_
    simp [h]

theorem btzDev_btzDevInv {w : ℝ × ℝ × ℝ} (h : 0 < w.2.1 ∨ (w.2.1 = 0 ∧ w.2.2 = 0)) :
    btzDev 0 btzV0 (btzDevInv w) = w := by
  rw [btzDevInv]
  rcases h with h | ⟨h1, h2⟩
  · rw [dif_pos h, btzDev_e0_apply]
    simp only [DInfty.posEmb_r, DInfty.posEmb_θ]
    ext
    · simp only; field_simp; ring
    · rfl
    · simp only; field_simp
  · have h0 : ¬ 0 < w.2.1 := by rw [h1]; exact lt_irrefl 0
    rw [dif_neg h0, btzDev_e0_apply]
    ext <;> simp [h1, h2]

theorem continuousOn_btzDevInv : ContinuousOn btzDevInv {w : ℝ × ℝ × ℝ | 0 < w.2.1} := by
  rw [continuousOn_iff_continuous_restrict]
  have : restrict {w : ℝ × ℝ × ℝ | 0 < w.2.1} btzDevInv = fun w =>
      (DInfty.posEmb ⟨(w.1.2.1, w.1.2.2 / w.1.2.1), w.2⟩,
        w.1.1 + w.1.2.1 - w.1.2.2 ^ 2 / w.1.2.1) := by
    funext w; simp only [restrict_apply, btzDevInv]; exact dif_pos w.2
  rw [this]
  have hb : Continuous fun w : {w : ℝ × ℝ × ℝ | 0 < w.2.1} => w.1.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  have hc : Continuous fun w : {w : ℝ × ℝ × ℝ | 0 < w.2.1} => w.1.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  have ha : Continuous fun w : {w : ℝ × ℝ × ℝ | 0 < w.2.1} => w.1.1 :=
    continuous_fst.comp continuous_subtype_val
  have hb0 : ∀ w : {w : ℝ × ℝ × ℝ | 0 < w.2.1}, w.1.2.1 ≠ 0 := fun w => w.2.ne'
  refine Continuous.prodMk (DInfty.continuous_posEmb.comp ?_) ?_
  · exact Continuous.subtype_mk (hb.prodMk (hc.div hb hb0)) _
  · exact (ha.add hb).sub ((hc.pow 2).div hb hb0)

/-- **An axis-preserving isometry in null coordinates**: `F(su) = (λs + s₀)u`, `λ > 0`, with the
consequences read off its linear part. -/
structure IsAxisAff (F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (lam s₀ : ℝ) : Prop where
  pos : 0 < lam
  map_zero : F 0 = s₀ • nullU
  linear_nullU : F.linear nullU = lam • nullU
  b_linear : ∀ w, lam * (F.linear w).2.1 = w.2.1
  Q_linear : ∀ w, nullQ (F.linear w) = nullQ w

theorem IsAxisAff.apply {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} (h : IsAxisAff F lam s₀)
    (w : ℝ × ℝ × ℝ) : F w = F.linear w + s₀ • nullU := by
  have := F.map_vadd 0 w
  simp only [vadd_eq_add, add_zero] at this
  rw [this, h.map_zero]

theorem nullQ_add_smul_nullU (w : ℝ × ℝ × ℝ) (t : ℝ) :
    nullQ (w + t • nullU) = nullQ w - t * w.2.1 := by
  simp [nullQ, nullU]; ring

/-- An element of `Isom₀` preserving the line `ℝu` is axis-preserving. -/
theorem isAxisAff_of_mem {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} (hF : F ∈ NullIsom0)
    (hΔ : ∀ s : ℝ, ∃ s' : ℝ, F (s • nullU) = s' • nullU) : ∃ lam s₀, IsAxisAff F lam s₀ := by
  obtain ⟨s₀, h0⟩ := hΔ 0
  obtain ⟨s₁, h1⟩ := hΔ 1
  rw [zero_smul] at h0
  rw [one_smul] at h1
  obtain ⟨hQ, -, hC⟩ := hF
  have hlin : F.linear nullU = (s₁ - s₀) • nullU := by
    have := F.map_vadd 0 nullU
    simp only [vadd_eq_add, add_zero] at this
    rw [h1, h0] at this
    rw [sub_smul, this]; abel
  set lam := s₁ - s₀
  have hb : ∀ w, lam * (F.linear w).2.1 = w.2.1 := by
    intro w
    have e1 := hQ (w + (1 : ℝ) • nullU)
    rw [map_add, map_smul, hlin, smul_smul, nullQ_add_smul_nullU, nullQ_add_smul_nullU, hQ] at e1
    linarith
  have hne : lam ≠ 0 := by
    intro h0'
    rw [h0', zero_smul] at hlin
    have := F.linear.injective (hlin.trans (map_zero _).symm)
    have h' := congrArg Prod.fst this
    simp [nullU] at h'
  have hpos : 0 < lam := by
    rcases lt_or_gt_of_ne hne with hneg | hp
    · exfalso
      set z := F.linear ((0 : ℝ), (1 : ℝ), (0 : ℝ))
      set ε := -lam / (2 * (|nullτ z| + 1))
      have hε : 0 < ε := div_pos (by linarith) (by positivity)
      have hw : nullQ ((1 : ℝ), ε, (0 : ℝ)) < 0 := by simp [nullQ]; linarith
      have hτ : 0 < nullτ ((1 : ℝ), ε, (0 : ℝ)) := by simp; linarith
      have key := hC _ hw hτ
      have hsplit : ((1 : ℝ), ε, (0 : ℝ)) = nullU + ε • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
        simp [nullU]
      rw [hsplit, map_add, map_smul, hlin, map_add, map_smul, map_smul] at key
      have hu : nullτ nullU = 1 := by simp [nullU]
      rw [hu] at key
      simp only [smul_eq_mul, mul_one] at key
      have habs : ε * nullτ z ≤ ε * |nullτ z| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      have hεabs : ε * |nullτ z| ≤ -lam / 2 := by
        have : ε * (2 * (|nullτ z| + 1)) = -lam := by
          simp only [ε]; field_simp
        nlinarith [abs_nonneg (nullτ z)]
      linarith
    · exact hp
  exact ⟨lam, s₀, hpos, h0, hlin, hb, hQ⟩

theorem IsAxisAff.symm {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} (h : IsAxisAff F lam s₀) :
    IsAxisAff F.symm lam⁻¹ (-(s₀ / lam)) := by
  have hl := h.pos
  have hsl : F.symm.linear = F.linear.symm := F.linear_symm
  refine ⟨inv_pos.2 hl, ?_, ?_, fun w => ?_, fun w => ?_⟩
  · apply F.injective
    rw [F.apply_symm_apply, h.apply, map_smul, h.linear_nullU, smul_smul, ← add_smul]
    field_simp; simp
  · rw [hsl, LinearEquiv.symm_apply_eq, map_smul, h.linear_nullU, smul_smul, inv_mul_cancel₀ hl.ne',
      one_smul]
  · rw [hsl]
    have := h.b_linear (F.linear.symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]; field_simp
  · rw [hsl, ← h.Q_linear (F.linear.symm w), LinearEquiv.apply_symm_apply]

/-- **The lift of an axis-preserving isometry to the cylinder**: `D⁻¹ ∘ F ∘ D`. -/
noncomputable def btzConj (F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (y : DInfty × ℝ) : DInfty × ℝ :=
  btzDevInv (F (btzDev 0 btzV0 y))

theorem IsAxisAff.image_mem {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} (h : IsAxisAff F lam s₀)
    (y : DInfty × ℝ) : (0 < y.1.r → 0 < (F (btzDev 0 btzV0 y)).2.1) ∧
      (y.1 = DInfty.apex → F (btzDev 0 btzV0 y) = (lam * y.2 + s₀) • nullU) := by
  have hb := h.b_linear (btzDev 0 btzV0 y)
  rw [btzDev_e0_b] at hb
  refine ⟨fun hr => ?_, fun ha => ?_⟩
  · rw [h.apply]
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, nullU, smul_eq_mul,
      mul_zero, add_zero]
    have := h.pos
    by_contra hle
    push Not at hle
    nlinarith
  · have hy : btzDev 0 btzV0 y = y.2 • nullU := by
      rw [btzDev_e0_apply, ha]; simp [nullU]
    rw [h.apply, hy, map_smul, h.linear_nullU, smul_smul, ← add_smul, mul_comm]

theorem IsAxisAff.btzDev_btzConj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) :
    btzDev 0 btzV0 (btzConj F y) = F (btzDev 0 btzV0 y) := by
  refine btzDev_btzDevInv ?_
  rcases y.1.pos_or_eq_apex with hr | ha
  · exact Or.inl ((h.image_mem y).1 hr)
  · right; rw [(h.image_mem y).2 ha]; simp [nullU]

theorem IsAxisAff.r_btzConj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) : (btzConj F y).1.r = y.1.r / lam := by
  have e := congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) (h.btzDev_btzConj y)
  simp only [btzDev_e0_b] at e
  rw [e, h.apply]
  have hb := h.b_linear (btzDev 0 btzV0 y)
  rw [btzDev_e0_b] at hb
  simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, nullU, smul_eq_mul,
    mul_zero, add_zero]
  field_simp [h.pos.ne']; linarith

theorem IsAxisAff.t_btzConj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) :
    (btzConj F y).2 = (lam⁻¹ - lam) * y.1.r + lam * y.2 + s₀ := by
  have hl := h.pos
  rcases y.1.pos_or_eq_apex with hr | ha
  · have hm := (h.image_mem y).1 hr
    rw [btzConj, btzDevInv, dif_pos hm]
    simp only
    set w := F (btzDev 0 btzV0 y)
    have hb := h.b_linear (btzDev 0 btzV0 y)
    have hQ := h.Q_linear (btzDev 0 btzV0 y)
    have hw : w = F.linear (btzDev 0 btzV0 y) + s₀ • nullU := h.apply _
    have hwb : w.2.1 = (F.linear (btzDev 0 btzV0 y)).2.1 := by
      rw [hw]; simp [nullU]
    have hwQ : nullQ w = nullQ (btzDev 0 btzV0 y) - s₀ * w.2.1 := by
      rw [hw, nullQ_add_smul_nullU, hQ]; simp [nullU]
    rw [btzDev_e0_b] at hb
    rw [nullQ_btzDev_e0] at hwQ
    rw [← hwb] at hb
    simp only [nullQ] at hwQ
    have hb0 : w.2.1 ≠ 0 := hm.ne'
    field_simp
    have hlb : lam * w.2.1 = y.1.r := hb
    linear_combination (-lam) * hwQ + (w.2.1 + lam * y.1.r - lam * y.2) * hlb
  · rw [btzConj, (h.image_mem y).2 ha, btzDevInv]
    have h0 : ¬ 0 < ((lam * y.2 + s₀) • nullU).2.1 := by simp [nullU]
    rw [dif_neg h0, ha]
    simp [nullU]

theorem IsAxisAff.continuous_btzConj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) : Continuous (btzConj F) := by
  have hF : Continuous (F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) := F.toAffineMap.continuous_of_finiteDimensional
  refine continuous_iff_continuousAt.2 fun y => ?_
  rcases y.1.pos_or_eq_apex with hr | ha
  · have hD : ContinuousAt (btzDev 0 btzV0) y :=
      (isLocalHomeomorphOn_btzDev 0 btzV0_pos).continuousAt (show y ∈ cylPos ℝ from hr)
    have hI : ContinuousAt btzDevInv (F (btzDev 0 btzV0 y)) :=
      continuousOn_btzDevInv.continuousAt
        ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds
          ((h.image_mem y).1 hr))
    exact hI.comp_of_eq ((hF.continuousAt (x := btzDev 0 btzV0 y)).comp hD) rfl
  · have hr0 : (btzConj F y).1 = DInfty.apex := by
      refine DInfty.eq_apex_of_not_pos ?_
      rw [h.r_btzConj, ha, DInfty.apex_r, zero_div]; exact lt_irrefl 0
    have hcr : Continuous fun z : DInfty × ℝ => z.1.r := DInfty.continuous_r'.comp continuous_fst
    have h2 : Continuous fun z => (btzConj F z).2 := by
      have : (fun z => (btzConj F z).2) = fun z : DInfty × ℝ =>
          (lam⁻¹ - lam) * z.1.r + lam * z.2 + s₀ := funext h.t_btzConj
      rw [this]; fun_prop
    show Tendsto (btzConj F) (𝓝 y) (𝓝 (btzConj F y))
    have e : btzConj F y = (DInfty.apex, (btzConj F y).2) := Prod.ext hr0 rfl
    rw [e]
    refine Tendsto.prodMk_nhds ?_ (h2.tendsto y)
    refine DInfty.hasBasis_nhds_apex.tendsto_right_iff.2 fun ε hε => ?_
    have hy0 : y.1.r = 0 := by rw [ha]; rfl
    have := (hcr.tendsto y).eventually (gt_mem_nhds (show y.1.r < ε * lam by
      rw [hy0]; exact mul_pos hε h.pos))
    filter_upwards [this] with z hz
    show (btzConj F z).1.r < ε
    rw [h.r_btzConj, div_lt_iff₀ h.pos]; exact hz

theorem IsAxisAff.btzConj_symm_btzConj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) : btzConj F.symm (btzConj F y) = y := by
  apply btzDev_injective 0 btzV0_pos
  rw [h.symm.btzDev_btzConj, h.btzDev_btzConj, F.symm_apply_apply]

theorem IsAxisAff.btzConj_btzConj_symm {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) : btzConj F (btzConj F.symm y) = y := by
  apply btzDev_injective 0 btzV0_pos
  rw [h.btzDev_btzConj, h.symm.btzDev_btzConj, F.apply_symm_apply]

/-- `D⁻¹ ∘ F ∘ D` as a homeomorphism of the cylinder. -/
noncomputable def IsAxisAff.homeo {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) : DInfty × ℝ ≃ₜ DInfty × ℝ where
  toFun := btzConj F
  invFun := btzConj F.symm
  left_inv := h.btzConj_symm_btzConj
  right_inv := h.btzConj_btzConj_symm
  continuous_toFun := h.continuous_btzConj
  continuous_invFun := h.symm.continuous_btzConj

theorem IsAxisAff.mem_cylPos_iff {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) (y : DInfty × ℝ) : btzConj F y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ := by
  show 0 < (btzConj F y).1.r ↔ 0 < y.1.r
  rw [h.r_btzConj]; exact div_pos_iff_of_pos_right h.pos

/-- The `2π`-parabolic in null coordinates. -/
noncomputable abbrev btzParab : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ) := parabAff 0 (2 * π)

theorem btzParab_zpow_smul (n : ℤ) (w : ℝ × ℝ × ℝ) :
    (btzParab ^ n) • w = parab (n * (2 * π)) w := by
  rw [btzParab, parabAff_zpow, sub_zero, zero_add]

theorem eq_smul_nullU_of_parab_eq {θ : ℝ} (hθ : θ ≠ 0) {w : ℝ × ℝ × ℝ} (h : parab θ w = w) :
    w = w.1 • nullU := by
  rw [parab_apply] at h
  have h1 := congrArg Prod.fst h
  have h3 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) h
  simp only at h1 h3
  have hb : w.2.1 = 0 := by
    have : θ * w.2.1 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hθ
  have hc : w.2.2 = 0 := by
    rw [hb] at h1
    have : 2 * θ * w.2.2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hθ)
  ext <;> simp [nullU, hb, hc]

/-- **Conjugation by `F`**: from `F P = Pᵏ F`, `F Pᵐ = P^{km} F` for every `m`. -/
theorem conj_zpow_of_conj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {k : ℤ}
    (hc : F * btzParab = btzParab ^ k * F) (m : ℤ) :
    F * btzParab ^ m = btzParab ^ (k * m) * F := by
  have h1 : F * btzParab * F⁻¹ = btzParab ^ k := by rw [hc, mul_inv_cancel_right]
  have h2 : F * btzParab ^ m * F⁻¹ = (F * btzParab * F⁻¹) ^ m := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [h1, ← zpow_mul] at h2
  rw [← h2, inv_mul_cancel_right]

/-- **`F` preserves the line `ℝu`** when `F P = Pᵏ F`, `k ≠ 0` (`ℝu` is the fixed set of `Pᵏ`). -/
theorem map_line_of_conj {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {k : ℤ} (hk : k ≠ 0)
    (hc : F * btzParab = btzParab ^ k * F) (s : ℝ) : ∃ s' : ℝ, F (s • nullU) = s' • nullU := by
  refine ⟨(F (s • nullU)).1, eq_smul_nullU_of_parab_eq (θ := k * (2 * π))
    (mul_ne_zero (Int.cast_ne_zero.2 hk) (by positivity)) ?_⟩
  have := congrArg (fun A : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ) => A (s • nullU)) hc
  change F (btzParab (s • nullU)) = (btzParab ^ k) (F (s • nullU)) at this
  rw [← btzParab_zpow_smul, affineEquiv_smul_def, ← this]
  congr 1
  rw [btzParab, parabAff_apply, sub_zero, zero_add, map_smul, parab_nullU]

theorem IsAxisAff.btzConj_smul {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (h : IsAxisAff F lam s₀) {k : ℤ} (hc : F * btzParab = btzParab ^ k * F)
    (m : GammaA (2 * π)) (y : DInfty × ℝ) :
    btzConj F (m • y) = (GammaA.ofInt (k * m.toInt) : GammaA (2 * π)) • btzConj F y := by
  apply btzDev_injective 0 btzV0_pos
  rw [h.btzDev_btzConj, btzDev_smul_all, btzDev_smul_all, h.btzDev_btzConj, GammaA.toInt_ofInt]
  have := congrArg (fun A : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ) => A (btzDev 0 btzV0 y))
    (conj_zpow_of_conj hc m.toInt)
  change F ((btzParab ^ m.toInt) (btzDev 0 btzV0 y)) =
    (btzParab ^ (k * m.toInt)) (F (btzDev 0 btzV0 y)) at this
  rw [affineEquiv_smul_def, affineEquiv_smul_def]
  exact this

end NullAxis

/-! ### Descent to `𝔼₀` and membership in `G` -/

section Descent

/-- A homeomorphism of the cylinder mapping `Γ`-orbits to `Γ`-orbits, both ways, descends to a
homeomorphism of `𝔼₀`. -/
noncomputable def btzE0Descend (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ)
    (h₁ : ∀ (m : GammaA (2 * π)) (y : DInfty × ℝ), ∃ m' : GammaA (2 * π), ψ (m • y) = m' • ψ y)
    (h₂ : ∀ (m : GammaA (2 * π)) (y : DInfty × ℝ), ∃ m' : GammaA (2 * π),
      ψ.symm (m • y) = m' • ψ.symm y) : BTZE0 ≃ₜ BTZE0 where
  toFun := Quotient.map' ψ fun a b hab => by
    obtain ⟨m, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    obtain ⟨m', hm'⟩ := h₁ m b
    exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨m', hm'.symm⟩)
  invFun := Quotient.map' ψ.symm fun a b hab => by
    obtain ⟨m, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    obtain ⟨m', hm'⟩ := h₂ m b
    exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨m', hm'.symm⟩)
  left_inv := fun x => Quotient.inductionOn' x fun y => by
    simp only [Quotient.map'_mk'']; rw [ψ.symm_apply_apply]
  right_inv := fun x => Quotient.inductionOn' x fun y => by
    simp only [Quotient.map'_mk'']; rw [ψ.apply_symm_apply]
  continuous_toFun := Continuous.quotient_map' ψ.continuous _
  continuous_invFun := Continuous.quotient_map' ψ.symm.continuous _

theorem btzE0Descend_mk (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (h₁ h₂) (y : DInfty × ℝ) :
    btzE0Descend ψ h₁ h₂ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y) := rfl

theorem btzE0_reg_eq :
    Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 = orbitMk (GammaA (2 * π)) '' cylPos ℝ :=
  btz_reg btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0

/-- `Ψ ∈ Aut(𝔼₀)` as an element of `G` on `range inr`. -/
noncomputable def e0Lift (Ψ : BTZE0 ≃ₜ BTZE0) : OpenPartialHomeomorph E0Y E0Y :=
  e0Inr.symm.trans (Ψ.toOpenPartialHomeomorph.trans e0Inr)

theorem e0Lift_source (Ψ : BTZE0 ≃ₜ BTZE0) : (e0Lift Ψ).source = range Sum.inr := by
  simp [e0Lift]

theorem e0Lift_target (Ψ : BTZE0 ≃ₜ BTZE0) : (e0Lift Ψ).target = range Sum.inr := by
  ext y
  simp [e0Lift]

theorem e0Lift_apply (Ψ : BTZE0 ≃ₜ BTZE0) (x : BTZE0) : e0Lift Ψ (Sum.inr x) = Sum.inr (Ψ x) := by
  simp [e0Lift, OpenPartialHomeomorph.coe_trans]

theorem e0Lift_symm_apply (Ψ : BTZE0 ≃ₜ BTZE0) (x : BTZE0) :
    (e0Lift Ψ).symm (Sum.inr x) = Sum.inr (Ψ.symm x) := by
  simp [e0Lift, OpenPartialHomeomorph.coe_trans_symm]

/-- The chart condition at a regular point, for an automorphism of `𝔼₀` lifted to the cylinder
`D`-equivariantly. -/
theorem e0RegAt_of_btzLift (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ)
    (g : Causal.Flat.isom 2)
    (hlift : ∀ y, Ψ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y))
    (hpos : ∀ y, ψ y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ)
    (hD : ∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ y) = g • btzDevM 0 btzV0 y) (x : BTZE0) :
    E0RegAt (fun y : E0Y => Sum.inr (Ψ (e0Inr.symm y))) (Sum.inr x) := by
  have hcont : ContinuousAt (fun y : E0Y => Sum.inr (Ψ (e0Inr.symm y))) (Sum.inr x) :=
    (continuous_inr : Continuous (Sum.inr : BTZE0 → E0Y)).continuousAt.comp
      (Ψ.continuous.continuousAt.comp
      (e0Inr.symm.continuousAt (by rw [e0Inr_symm_source]; exact ⟨x, rfl⟩)))
  by_cases hx : Sum.inr x ∈ e0Reg
  swap
  · exact ⟨hcont, fun h => absurd h hx⟩
  have hxR := inr_mem_e0Reg_iff.1 hx
  obtain ⟨c₀, hc₀, hxc₀⟩ := mem_support.1 hxR
  rw [btzE0_reg_eq] at hxR
  obtain ⟨yt, hyt, rfl⟩ := hxR
  have hψyt : ψ yt ∈ cylPos ℝ := (hpos yt).2 hyt
  have hΨR : Ψ (orbitMk (GammaA (2 * π)) yt) ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rw [hlift, btzE0_reg_eq]; exact ⟨_, hψyt, rfl⟩
  obtain ⟨c₀', hc₀', hxc₀'⟩ := mem_support.1 hΨR
  have hxc₀'' : orbitMk (GammaA (2 * π)) (ψ yt) ∈ c₀'.source := by rw [← hlift]; exact hxc₀'
  obtain ⟨h₁, hh₁⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 hyt hc₀ hxc₀
  obtain ⟨h₂, hh₂⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 hψyt hc₀' hxc₀''
  refine e0RegAt_of_exists hcont ⟨_, e0InrChart_mem_e0Atlas hc₀, _, e0InrChart_mem_e0Atlas hc₀',
    mem_e0InrChart_source.2 ⟨_, hxc₀, rfl⟩, ?_, h₂⁻¹ * g * h₁, ?_⟩
  · simp only [e0Inr_symm_inr]; exact mem_e0InrChart_source.2 ⟨_, hxc₀', rfl⟩
  -- the identity near `yt` in the cylinder
  have hcyl : ∀ᶠ y' in 𝓝 yt, c₀' (Ψ (orbitMk (GammaA (2 * π)) y')) =
      (h₂⁻¹ * g * h₁) • c₀ (orbitMk (GammaA (2 * π)) y') := by
    filter_upwards [hh₁, ψ.continuous.continuousAt.eventually hh₂,
      (isOpen_lt continuous_const (DInfty.continuous_r'.comp continuous_fst)).mem_nhds hyt]
      with y' e1 e2 e3
    rw [hlift, mul_smul, mul_smul, ← e1, ← hD y' e3, e2, inv_smul_smul]
  -- down to `𝔼₀`
  have hE0 : ∀ᶠ z in 𝓝 (orbitMk (GammaA (2 * π)) yt), c₀' (Ψ z) = (h₂⁻¹ * g * h₁) • c₀ z :=
    (isOpenMap_quotient_mk'_mul.nhds_le yt) (eventually_map.2 hcyl)
  -- and into `Y`
  rw [← IsOpenEmbedding.inr.map_nhds_eq, eventually_map]
  filter_upwards [hE0] with z hz
  simp only [e0Inr_symm_inr, e0InrChart_inr]
  exact hz

theorem btzLift_symm_data (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ)
    (g : Causal.Flat.isom 2)
    (hlift : ∀ y, Ψ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y))
    (hpos : ∀ y, ψ y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ)
    (hD : ∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ y) = g • btzDevM 0 btzV0 y) :
    (∀ y, Ψ.symm (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ.symm y)) ∧
    (∀ y, ψ.symm y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ) ∧
    (∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ.symm y) = g⁻¹ • btzDevM 0 btzV0 y) := by
  refine ⟨fun y => ?_, fun y => ?_, fun y hy => ?_⟩
  · rw [Ψ.symm_apply_eq, hlift, ψ.apply_symm_apply]
  · rw [← hpos, ψ.apply_symm_apply]
  · have hy' : ψ.symm y ∈ cylPos ℝ := by rw [← hpos, ψ.apply_symm_apply]; exact hy
    rw [eq_inv_smul_iff, ← hD _ hy', ψ.apply_symm_apply]

/-- **An automorphism of `𝔼₀` lifting `D`-equivariantly to the cylinder is an element of `G`**. -/
theorem e0Lift_mem (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (g : Causal.Flat.isom 2)
    (hlift : ∀ y, Ψ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y))
    (hpos : ∀ y, ψ y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ)
    (hD : ∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ y) = g • btzDevM 0 btzV0 y) :
    e0Lift Ψ ∈ e0Groupoid := by
  obtain ⟨hl', hp', hD'⟩ := btzLift_symm_data Ψ ψ g hlift hpos hD
  have hopen : IsOpen (range (Sum.inr : BTZE0 → E0Y)) := isOpen_range_inr
  refine mem_e0Groupoid_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [e0Lift_source] at hy
    obtain ⟨x, rfl⟩ := hy
    refine (e0RegAt_of_btzLift Ψ ψ g hlift hpos hD x).congr ?_
    filter_upwards [hopen.mem_nhds ⟨x, rfl⟩] with y ⟨z, hz⟩
    rw [← hz, e0Lift_apply, e0Inr_symm_inr]
  · rw [e0Lift_target] at hy
    obtain ⟨x, rfl⟩ := hy
    refine (e0RegAt_of_btzLift Ψ.symm ψ.symm g⁻¹ hl' hp' hD' x).congr ?_
    filter_upwards [hopen.mem_nhds ⟨x, rfl⟩] with y ⟨z, hz⟩
    rw [← hz, e0Lift_symm_apply, e0Inr_symm_inr]

end Descent

/-! ### The box around an axis point, in log-polar coordinates -/

section Box

/-- The section `(log r + iθ, t) ↦ (r, θ, t)` of the positive part of the cylinder. -/
noncomputable def e0BoxSec (w : ℂ × ℝ) : DInfty × ℝ := ((cylPosHomeo ℝ).symm w).1

theorem e0BoxSec_mem (w : ℂ × ℝ) : e0BoxSec w ∈ cylPos ℝ := ((cylPosHomeo ℝ).symm w).2

@[simp] theorem e0BoxSec_r (w : ℂ × ℝ) : (e0BoxSec w).1.r = Real.exp w.1.re := rfl

@[simp] theorem e0BoxSec_θ (w : ℂ × ℝ) : (e0BoxSec w).1.θ = w.1.im := by
  show w.1.im / 1 = w.1.im; rw [div_one]

@[simp] theorem e0BoxSec_t (w : ℂ × ℝ) : (e0BoxSec w).2 = w.2 := rfl

theorem isOpenEmbedding_e0BoxSec : IsOpenEmbedding e0BoxSec :=
  (DInfty.isOpen_pos.preimage continuous_fst).isOpenEmbedding_subtypeVal.comp
    (cylPosHomeo ℝ).symm.isOpenEmbedding

theorem e0BoxSec_add_two_pi (w : ℂ × ℝ) :
    e0BoxSec (w + (((2 * π : ℝ) : ℂ) * Complex.I, 0)) =
      (GammaA.ofInt 1 : GammaA (2 * π)) • e0BoxSec w := by
  rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_of_pos (e0BoxSec_mem w)]
  refine Prod.ext (DInfty.ext ?_ ?_) ?_
  · simp
  · simp only [e0BoxSec_θ, Prod.fst_add, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re]
    simp
  · simp

/-- The box `{Re < c, |t − t₀| < ε}` in `ℂ × ℝ`. -/
def e0Box (c t₀ ε : ℝ) : Set (ℂ × ℝ) := {w | w.1.re < c ∧ dist w.2 t₀ < ε}

theorem isOpen_e0Box (c t₀ ε : ℝ) : IsOpen (e0Box c t₀ ε) :=
  (isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const).inter
    (Metric.isOpen_ball.preimage continuous_snd)

theorem convex_e0Box (c t₀ ε : ℝ) : Convex ℝ (e0Box c t₀ ε) := by
  have h1 : Convex ℝ {w : ℂ × ℝ | w.1.re < c} :=
    (convex_Iio c).linear_preimage (Complex.reLm.comp (LinearMap.fst ℝ ℂ ℝ))
  have h2 : Convex ℝ {w : ℂ × ℝ | dist w.2 t₀ < ε} :=
    (convex_ball t₀ ε).linear_preimage (LinearMap.snd ℝ ℂ ℝ)
  exact h1.inter h2

theorem mem_e0Box_add {c t₀ ε : ℝ} {w : ℂ × ℝ} (hw : w ∈ e0Box c t₀ ε) (s : ℝ) :
    w + ((s : ℂ) * Complex.I, 0) ∈ e0Box c t₀ ε := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, ?_⟩
  · simpa using h1
  · simpa using h2

end Box

/-! ### The winding of a conjugating isometry is `±1` on an injective map -/

section Winding

theorem DInfty.continuousOn_θ' : ContinuousOn DInfty.θ {p : DInfty | 0 < p.r} := by
  have h : ContinuousOn (fun p : DInfty => (DInfty.posChart.symm p).1.2) DInfty.posChart.target :=
    (continuous_snd.comp continuous_subtype_val).comp_continuousOn DInfty.posChart.continuousOn_symm
  have htarget : DInfty.posChart.target = {p : DInfty | 0 < p.r} := by
    rw [DInfty.posChart, IsOpenEmbedding.toOpenPartialHomeomorph_target, DInfty.range_posEmb]
  rw [htarget] at h
  refine h.congr fun p hp => ?_
  have := DInfty.posChart.right_inv (DInfty.mem_posChart_target hp)
  rw [DInfty.posChart_apply] at this
  conv_lhs => rw [← this]
  rfl

theorem btzParab_ne_one : btzParab ≠ 1 := by
  intro h
  have := congrArg (fun A : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ) => (A ((0 : ℝ), (0 : ℝ), (1 : ℝ))).1) h
  simp only [btzParab, parabAff_apply, sub_zero, zero_add, parab_apply, AffineEquiv.coe_one,
    id_eq] at this
  have hπ : (0 : ℝ) < π := Real.pi_pos
  nlinarith

theorem conj_ne_zero {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {k : ℤ}
    (hc : F * btzParab = btzParab ^ k * F) : k ≠ 0 := by
  rintro rfl
  rw [zpow_zero, one_mul] at hc
  exact btzParab_ne_one (mul_left_cancel (a := F) (hc.trans (mul_one F).symm))

theorem e0BoxSec_orbit_ne (w : ℂ × ℝ) {s : ℝ} (h0 : 0 < s) (h1 : s < 2 * π) :
    orbitMk (GammaA (2 * π)) (e0BoxSec (w + ((s : ℂ) * Complex.I, 0))) ≠
      orbitMk (GammaA (2 * π)) (e0BoxSec w) := by
  intro h
  obtain ⟨m, hm⟩ := exists_smul_eq_of_orbitMk_eq h.symm
  have hθ := congrArg (fun y : DInfty × ℝ => y.1.θ) hm
  simp only [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_of_pos (e0BoxSec_mem w)] at hθ
  simp only [e0BoxSec_θ, Prod.fst_add, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero] at hθ
  have hs : s = m.toInt * (2 * π) := by linarith
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hm0 : (0 : ℝ) < m.toInt := by
    by_contra hle; push Not at hle; nlinarith
  have hm1 : (m.toInt : ℝ) < 1 := by
    by_contra hle; push Not at hle; nlinarith
  have a := Int.cast_pos.1 hm0
  have b : m.toInt < 1 := by exact_mod_cast hm1
  omega

/-- **The winding argument**: if `F P = Pᵏ F` with `|k| ≥ 2`, two points of one circle
`{r, t fixed}` not in one `Γ`-orbit are sent by `D⁻¹ F D` into one `Γ`-orbit. -/
theorem btzConj_winding {F : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} (hax : IsAxisAff F lam s₀)
    {kk : ℤ} (hc : F * btzParab = btzParab ^ kk * F) (hk : 2 ≤ |kk|) (w : ℂ × ℝ) :
    ∃ s : ℝ, 0 < s ∧ s < 2 * π ∧
      orbitMk (GammaA (2 * π)) (btzConj F (e0BoxSec (w + ((s : ℂ) * Complex.I, 0)))) =
        orbitMk (GammaA (2 * π)) (btzConj F (e0BoxSec w)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set p : ℝ → DInfty × ℝ := fun s => btzConj F (e0BoxSec (w + ((s : ℂ) * Complex.I, 0)))
  have hpc : Continuous p := hax.continuous_btzConj.comp (isOpenEmbedding_e0BoxSec.continuous.comp
    (continuous_const.add ((Complex.continuous_ofReal.mul continuous_const).prodMk continuous_const)))
  have hpP : ∀ s, 0 < (p s).1.r := fun s => (hax.mem_cylPos_iff _).2 (e0BoxSec_mem _)
  set Θ : ℝ → ℝ := fun s => (p s).1.θ
  have hΘc : Continuous Θ :=
    DInfty.continuousOn_θ'.comp_continuous (continuous_fst.comp hpc) hpP
  set θ₁ := (btzConj F (e0BoxSec w)).1.θ
  have hp0 : p 0 = btzConj F (e0BoxSec w) := by simp [p, Prod.mk_zero_zero]
  have hΘ0 : Θ 0 = θ₁ := by simp only [Θ, hp0, θ₁]
  have hsmulθ : ∀ (j : ℤ) (z : DInfty × ℝ), 0 < z.1.r →
      ((GammaA.ofInt j : GammaA (2 * π)) • z).1.θ = z.1.θ + j * (2 * π) := by
    intro j z hz
    rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_of_pos hz, GammaA.toInt_ofInt]
  have hp2 : p (2 * π) = (GammaA.ofInt kk : GammaA (2 * π)) • btzConj F (e0BoxSec w) := by
    simp only [p]
    rw [e0BoxSec_add_two_pi, hax.btzConj_smul hc, GammaA.toInt_ofInt, mul_one]
  have hΘ2 : Θ (2 * π) = θ₁ + kk * (2 * π) := by
    simp only [Θ]; rw [hp2, hsmulθ _ _ ((hax.mem_cylPos_iff _).2 (e0BoxSec_mem _))]
  -- the target angle
  set j : ℤ := if 0 < kk then 1 else -1
  have hj : j = 1 ∨ j = -1 := by simp only [j]; split_ifs <;> simp
  have hjk : j ≠ kk := by
    simp only [j]; split_ifs with h
    · intro h'; rw [← h'] at hk; simp at hk
    · intro h'; rw [← h'] at hk; simp at hk
  have hmem : θ₁ + j * (2 * π) ∈ Θ '' Icc 0 (2 * π) := by
    by_cases hpos : 0 < kk
    · have hj1 : j = 1 := by simp [j, hpos]
      have hk2 : (2 : ℝ) ≤ kk := by
        have : 2 ≤ kk := by rw [abs_of_pos hpos] at hk; exact hk
        exact_mod_cast this
      refine intermediate_value_Icc (by positivity) hΘc.continuousOn ⟨?_, ?_⟩
      · rw [hΘ0, hj1]; push_cast; linarith
      · rw [hΘ2, hj1]; push_cast; nlinarith
    · have hj1 : j = -1 := by simp [j, hpos]
      have hk2 : (kk : ℝ) ≤ -2 := by
        have : kk ≤ -2 := by
          push Not at hpos
          rw [abs_of_nonpos hpos] at hk; omega
        exact_mod_cast this
      refine intermediate_value_Icc' (by positivity) hΘc.continuousOn ⟨?_, ?_⟩
      · rw [hΘ2, hj1]; push_cast; nlinarith
      · rw [hΘ0, hj1]; push_cast; linarith
  obtain ⟨s, ⟨hs0, hs2⟩, hΘs⟩ := hmem
  have hjne : (j : ℝ) * (2 * π) ≠ 0 := by
    rcases hj with h | h <;> rw [h] <;> push_cast <;> positivity
  have hs0' : s ≠ 0 := by
    rintro rfl; rw [hΘ0] at hΘs; exact hjne (by linarith)
  have hs2' : s ≠ 2 * π := by
    rintro rfl
    rw [hΘ2] at hΘs
    have : ((kk : ℝ) - j) * (2 * π) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hjk (by exact_mod_cast (sub_eq_zero.1 h).symm)
    · linarith
  refine ⟨s, lt_of_le_of_ne hs0 (Ne.symm hs0'), lt_of_le_of_ne hs2 hs2', ?_⟩
  -- `p s` and `j · p 0` coincide
  have heq : p s = (GammaA.ofInt j : GammaA (2 * π)) • btzConj F (e0BoxSec w) := by
    refine Prod.ext (DInfty.ext ?_ ?_) ?_
    · rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_r]
      simp only [p, hax.r_btzConj, e0BoxSec_r]; simp
    · rw [hsmulθ _ _ ((hax.mem_cylPos_iff _).2 (e0BoxSec_mem _))]
      exact hΘs
    · rw [DInfty.smul_prod_def]
      simp only [p, hax.t_btzConj, e0BoxSec_r, e0BoxSec_t]; simp
  show orbitMk (GammaA (2 * π)) (p s) = _
  rw [heq, orbitMk_smul]

end Winding

/-! ### The core on `𝔼₀` -/

section CoreE0

/-- An axis point of `𝔼₀` has a box neighbourhood inside any open set containing it. -/
theorem btzE0_exists_box {x₀ : BTZE0}
    (hx₀ : x₀ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) {U : Set BTZE0}
    (hU : IsOpen U) (hx₀U : x₀ ∈ U) :
    ∃ t₀ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ 0 < ε₂ ∧ ∀ y : DInfty × ℝ, y.1.r < ε₁ → dist y.2 t₀ < ε₂ →
      orbitMk (GammaA (2 * π)) y ∈ U := by
  have hS : x₀ ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := hx₀
  rw [btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0] at hS
  obtain ⟨⟨p, t₀⟩, hp, rfl⟩ := hS
  simp only [mem_setOf_eq] at hp
  subst hp
  have hpre : orbitMk (GammaA (2 * π)) ⁻¹' U ∈ 𝓝 ((DInfty.apex, t₀) : DInfty × ℝ) :=
    (hU.preimage continuous_quot_mk).mem_nhds hx₀U
  rw [nhds_prod_eq] at hpre
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.1 hpre
  obtain ⟨ε₁, hε₁, h₁⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 hu
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.mem_nhds_iff.1 hv
  exact ⟨t₀, ε₁, ε₂, hε₁, hε₂, fun y hy1 hy2 => huv ⟨h₁ hy1, h₂ hy2⟩⟩

/-- **The local core of B21 `prop:isom_strong` at `α = β = 0`, on `𝔼₀`**, over a region swept by
whole circles around the axis: `B ⊆ ℂ × ℝ` open, convex, non-empty and invariant under the angle
shifts `w ↦ w + (is, 0)`, whose image `(log r + iθ, t) ↦ [r, θ, t]` lies in `U`. A map `F` which on
`U ∩ reg` is continuous, injective and locally an isometry in the charts agrees on a non-empty open
set with an automorphism `Ψ` of `𝔼₀` lifting `D`-equivariantly to the cylinder. -/
theorem btzE0_localUnique_core_of_region {B : Set (ℂ × ℝ)} (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hBne : B.Nonempty) (hBs : ∀ w ∈ B, ∀ s : ℝ, w + ((s : ℂ) * Complex.I, 0) ∈ B)
    {U : Set BTZE0} (hBU : ∀ w ∈ B, orbitMk (GammaA (2 * π)) (e0BoxSec w) ∈ U) {F : BTZE0 → BTZE0}
    (hFc : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, ContinuousAt F x)
    (hFreg : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
    (hFloc : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z)
    (hinj : InjOn F (U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)) :
    ∃ (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (g : Causal.Flat.isom 2),
      (∀ y, Ψ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y)) ∧
      (∀ y, ψ y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ) ∧
      (∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ y) = g • btzDevM 0 btzV0 y) ∧
      ∃ W : Set BTZE0, IsOpen W ∧ W.Nonempty ∧
        W ⊆ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 ∧ EqOn F Ψ W := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨w₀, hw₀⟩ := hBne
  haveI : ContractibleSpace B := hBc.contractibleSpace ⟨_, hw₀⟩
  haveI : LocPathConnectedSpace B := hBo.locPathConnectedSpace
  set σ : B → DInfty × ℝ := fun a => e0BoxSec a.1
  have hσc : Continuous σ := isOpenEmbedding_e0BoxSec.continuous.comp continuous_subtype_val
  have hσemb : IsOpenEmbedding σ := isOpenEmbedding_e0BoxSec.comp hBo.isOpenEmbedding_subtypeVal
  have hσP : ∀ a, σ a ∈ cylPos ℝ := fun a => e0BoxSec_mem _
  have hσU : ∀ a, orbitMk (GammaA (2 * π)) (σ a) ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    fun a => ⟨hBU _ a.2, by rw [btzE0_reg_eq]; exact ⟨_, hσP a, rfl⟩⟩
  have hqσ : Continuous fun a : B => orbitMk (GammaA (2 * π)) (σ a) := continuous_quot_mk.comp hσc
  -- the map to lift
  have hφc : Continuous fun a : B => F (orbitMk (GammaA (2 * π)) (σ a)) :=
    continuous_iff_continuousAt.2 fun a =>
      ContinuousAt.comp (g := F) (f := fun a : B => orbitMk (GammaA (2 * π)) (σ a))
        (hFc _ (hσU a)) hqσ.continuousAt
  set φ : C(B, BTZE0) := ⟨fun a => F (orbitMk (GammaA (2 * π)) (σ a)), hφc⟩
  have hs : ∀ a, φ a ∈ orbitMk (GammaA (2 * π)) '' cylPos ℝ := fun a => by
    rw [← btzE0_reg_eq]; exact hFreg _ (hσU a)
  have hcov := isCoveringMapOn_orbitMk_cylPos (Z := ℝ) btz_two_pi_ne_zero
  set a₀ : B := ⟨_, hw₀⟩
  obtain ⟨e₀, -, he₀⟩ := hs a₀
  obtain ⟨L, ⟨hL0, hLq⟩, -⟩ := hcov.existsUnique_continuousMap_lifts φ he₀ hs
  have hLq' : ∀ a, orbitMk (GammaA (2 * π)) (L a) = F (orbitMk (GammaA (2 * π)) (σ a)) := fun a => congrFun hLq a
  have hLP : ∀ a, L a ∈ cylPos ℝ := fun a => by
    have : L a ∈ orbitMk (GammaA (2 * π)) ⁻¹' (orbitMk (GammaA (2 * π)) '' cylPos ℝ) := by
      rw [mem_preimage, hLq']; exact hs a
    rwa [preimage_image_cylPos] at this
  -- the lift is locally a translate of `D`
  have hloc : ∀ a ∈ (univ : Set B), ∃ g : Causal.Flat.isom 2,
      ∀ᶠ a' in 𝓝 a, btzDevM 0 btzV0 (L a') = g • btzDevM 0 btzV0 (σ a') := by
    intro a _
    obtain ⟨c, hc, hxc, c', hc', hFxc, h, hh⟩ := hFloc _ (hσU a)
    obtain ⟨g₁, hg₁⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 (hσP a) hc hxc
    have hLc : orbitMk (GammaA (2 * π)) (L a) ∈ c'.source := by rw [hLq']; exact hFxc
    obtain ⟨g₂, hg₂⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 (hLP a) hc' hLc
    refine ⟨g₂ * h * g₁⁻¹, ?_⟩
    filter_upwards [L.continuous.continuousAt.eventually hg₂, hσc.continuousAt.eventually hg₁,
      hqσ.continuousAt.eventually hh] with a' e1 e2 e3
    rw [e1, hLq', e3, e2, mul_smul, mul_smul, inv_smul_smul]
  -- Liouville on the simply connected box
  have hDσ : IsLocalHomeomorphOn (btzDevM 0 btzV0 ∘ σ) univ :=
    (isLocalHomeomorphOn_btzDevM 0 btzV0_pos).comp hσemb.isLocalHomeomorph.isLocalHomeomorphOn
      fun a _ => hσP a
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn (G := Causal.Flat.isom 2)
    (F := btzDevM 0 btzV0 ∘ L) isOpen_univ hDσ isPreconnected_univ subset_rfl hloc
  have hg' : ∀ a, btzDevM 0 btzV0 (L a) = g • btzDevM 0 btzV0 (σ a) := fun a => hg a trivial
  -- the deck transformation of one turn around the axis
  set τ : B → B := fun a => ⟨a.1 + (((2 * π : ℝ) : ℂ) * Complex.I, 0), hBs _ a.2 (2 * π)⟩
  have hτc : Continuous τ := (continuous_subtype_val.add continuous_const).subtype_mk _
  have hστ : ∀ a, σ (τ a) = (GammaA.ofInt 1 : GammaA (2 * π)) • σ a := fun a =>
    e0BoxSec_add_two_pi a.1
  have hφτ : ∀ a, F (orbitMk (GammaA (2 * π)) (σ (τ a))) = F (orbitMk (GammaA (2 * π)) (σ a)) :=
    fun a => by rw [hστ, orbitMk_smul]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq (Γ := GammaA (2 * π))
    (show orbitMk (GammaA (2 * π)) (L a₀) = orbitMk (GammaA (2 * π)) (L (τ a₀)) by
      rw [hLq', hLq', hφτ])
  have he₁ : orbitMk (GammaA (2 * π)) (L (τ a₀)) = φ a₀ := by
    rw [hLq', hφτ]; rfl
  have hLτ : L.comp ⟨τ, hτc⟩ = ⟨fun a => k • L a, (continuous_const_smul k).comp L.continuous⟩ :=
    (hcov.existsUnique_continuousMap_lifts φ he₁ hs).unique
      ⟨rfl, funext fun a => by
        show orbitMk (GammaA (2 * π)) (L (τ a)) = F (orbitMk (GammaA (2 * π)) (σ a))
        rw [hLq', hφτ]⟩
      ⟨hk, funext fun a => by
        show orbitMk (GammaA (2 * π)) (k • L a) = F (orbitMk (GammaA (2 * π)) (σ a))
        rw [orbitMk_smul, hLq']⟩
  have hdeck : ∀ a, L (τ a) = k • L a := fun a => DFunLike.congr_fun hLτ a
  -- `g P = Pᵏ g`
  have hconjM : ∀ a, (g * btzHol 0 (2 * π)) • btzDevM 0 btzV0 (σ a) =
      (btzHol 0 (2 * π) ^ k.toInt * g) • btzDevM 0 btzV0 (σ a) := by
    intro a
    have e1 := btzDevM_smul 0 btzV0 (GammaA.ofInt 1 : GammaA (2 * π)) (σ a)
    rw [GammaA.toInt_ofInt, zpow_one, ← hστ] at e1
    rw [mul_smul, mul_smul, ← e1, ← hg', hdeck, btzDevM_smul, hg']
  have hopen : IsOpen (range (btzDevM 0 btzV0 ∘ σ)) :=
    (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 hDσ).isOpenMap.isOpen_range
  have hall := IsRigidAction.smul_eq_of_eqOn hopen ⟨_, a₀, rfl⟩
    (by rintro _ ⟨a, rfl⟩; exact hconjM a)
  have hGP : g * btzHol 0 (2 * π) = btzHol 0 (2 * π) ^ k.toInt * g :=
    Subtype.ext (AffineEquiv.ext fun z => hall z)
  -- null coordinates
  set Fg : NullIsom0 := nullIsom0EquivIsom.symm g
  have hgF : nullIsom0EquivIsom Fg = g := MulEquiv.apply_symm_apply _ _
  set Pn : NullIsom0 := ⟨parabAff 0 (2 * π), parab_mem 0 (2 * π)⟩
  have hPn : nullIsom0EquivIsom Pn = btzHol 0 (2 * π) := rfl
  have hcN : Fg * Pn = Pn ^ k.toInt * Fg :=
    nullIsom0EquivIsom.injective (by rw [map_mul, map_mul, map_zpow, hgF, hPn, hGP])
  have hc : (Fg : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) * btzParab =
      btzParab ^ k.toInt * (Fg : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) := by
    have := congrArg Subtype.val hcN
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow] at this
  have hbtz : ∀ a, btzDev 0 btzV0 (L a) =
      (Fg : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (btzDev 0 btzV0 (σ a)) := by
    intro a
    apply nullToMink.injective
    have := hg' a
    rw [btzDevM, btzDevM, ← hgF, ← nullToMink_smul] at this
    exact this
  have hk0 := conj_ne_zero hc
  obtain ⟨lam, s₀, hax⟩ := isAxisAff_of_mem Fg.2 (map_line_of_conj hk0 hc)
  have hLψ : ∀ a, L a = btzConj Fg (σ a) := fun a => by
    rw [← btzDevInv_btzDev (L a), hbtz]; rfl
  have hFσ : ∀ a, F (orbitMk (GammaA (2 * π)) (σ a)) =
      orbitMk (GammaA (2 * π)) (btzConj Fg (σ a)) := fun a => by rw [← hLq', hLψ]
  -- the winding is `±1` (injectivity)
  have hk1 : k.toInt * k.toInt = 1 := by
    by_contra hne
    have h2 : 2 ≤ |k.toInt| := by
      rcases le_or_gt 0 k.toInt with h | h
      · rw [abs_of_nonneg h]
        by_contra h'
        have : k.toInt = 1 := by omega
        exact hne (by rw [this]; rfl)
      · rw [abs_of_neg h]
        by_contra h'
        have : k.toInt = -1 := by omega
        exact hne (by rw [this]; rfl)
    obtain ⟨s, hs0, hs2, heq⟩ := btzConj_winding hax hc h2 a₀.1
    set a₁ : B := ⟨_, hBs _ a₀.2 s⟩
    have := hinj (hσU a₁) (hσU a₀) (by rw [hFσ, hFσ]; exact heq)
    exact e0BoxSec_orbit_ne a₀.1 hs0 hs2 this
  -- the automorphism of `𝔼₀`
  set ψ := hax.homeo
  have h₁ : ∀ (m : GammaA (2 * π)) (y : DInfty × ℝ), ∃ m' : GammaA (2 * π),
      ψ (m • y) = m' • ψ y := fun m y => ⟨_, hax.btzConj_smul hc m y⟩
  have h₂ : ∀ (m : GammaA (2 * π)) (y : DInfty × ℝ), ∃ m' : GammaA (2 * π),
      ψ.symm (m • y) = m' • ψ.symm y := by
    intro m y
    refine ⟨GammaA.ofInt (k.toInt * m.toInt), ψ.injective ?_⟩
    rw [ψ.apply_symm_apply]
    show m • y = btzConj Fg ((GammaA.ofInt (k.toInt * m.toInt) : GammaA (2 * π)) •
      btzConj (Fg : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)).symm y)
    rw [hax.btzConj_smul hc, hax.btzConj_btzConj_symm, GammaA.toInt_ofInt, ← mul_assoc, hk1,
      one_mul, GammaA.ofInt_toInt]
  refine ⟨btzE0Descend ψ h₁ h₂, ψ, g, fun y => rfl, hax.mem_cylPos_iff, fun y _ => ?_,
    orbitMk (GammaA (2 * π)) '' range σ, isOpenMap_quotient_mk'_mul _ hσemb.isOpen_range,
    ⟨_, ⟨σ a₀, ⟨a₀, rfl⟩, rfl⟩⟩, ?_, ?_⟩
  · show btzDevM 0 btzV0 (btzConj Fg y) = g • btzDevM 0 btzV0 y
    rw [btzDevM, btzDevM, hax.btzDev_btzConj, ← hgF, ← nullToMink_smul]; rfl
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩; exact hσU a
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [hFσ]; rfl

/-- **The local core at an axis point**: the box version of `btzE0_localUnique_core_of_region`. -/
theorem btzE0_localUnique_core {x₀ : BTZE0}
    (hx₀ : x₀ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) {U : Set BTZE0}
    (hU : IsOpen U) (hx₀U : x₀ ∈ U) {F : BTZE0 → BTZE0}
    (hFc : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, ContinuousAt F x)
    (hFreg : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
    (hFloc : ∀ x ∈ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z)
    (hinj : InjOn F (U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)) :
    ∃ (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (g : Causal.Flat.isom 2),
      (∀ y, Ψ (orbitMk (GammaA (2 * π)) y) = orbitMk (GammaA (2 * π)) (ψ y)) ∧
      (∀ y, ψ y ∈ cylPos ℝ ↔ y ∈ cylPos ℝ) ∧
      (∀ y ∈ cylPos ℝ, btzDevM 0 btzV0 (ψ y) = g • btzDevM 0 btzV0 y) ∧
      ∃ W : Set BTZE0, IsOpen W ∧ W.Nonempty ∧
        W ⊆ U ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 ∧ EqOn F Ψ W := by
  obtain ⟨t₀, ε₁, ε₂, hε₁, hε₂, hbox⟩ := btzE0_exists_box hx₀ hU hx₀U
  refine btzE0_localUnique_core_of_region (isOpen_e0Box (Real.log ε₁) t₀ ε₂) (convex_e0Box _ _ _)
    ⟨(((Real.log ε₁ - 1 : ℝ) : ℂ), t₀), by simp [e0Box, hε₂]⟩ (fun w hw s => mem_e0Box_add hw s)
    (fun w hw => hbox _ ((Real.lt_log_iff_exp_lt hε₁).1 hw.1) hw.2) hFc hFreg hFloc hinj

end CoreE0

/-! ### The core on `Y = 𝕄 ⊕ 𝔼₀` -/

section CoreY

/-- **The local core on `Y`**, over a region of `𝔼₀` swept by whole circles around the axis: a local
`G`-structomorphism `f` on an open `S ⊆ reg Y`, injective, with values in `𝔼₀`, agrees on a
non-empty open subset of `S` with an element of `G` defined on all of `𝔼₀`. -/
theorem e0_localUnique_core_of_region {B : Set (ℂ × ℝ)} (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hBne : B.Nonempty) (hBs : ∀ w ∈ B, ∀ s : ℝ, w + ((s : ℂ) * Complex.I, 0) ∈ B)
    {S : Set E0Y} (hSo : IsOpen S) (hSr : S ⊆ e0Reg)
    (hBS : ∀ w ∈ B, (Sum.inr (orbitMk (GammaA (2 * π)) (e0BoxSec w)) : E0Y) ∈ S)
    {f : E0Y → E0Y} (hf : ∀ y ∈ S, e0Groupoid.IsLocalStructomorphWithinAt f S y)
    (hinj : InjOn f S) (hmaps : MapsTo f S (range Sum.inr)) :
    ∃ e ∈ e0Groupoid, range Sum.inr ⊆ e.source ∧ ∃ W : Set E0Y, IsOpen W ∧ W.Nonempty ∧
      W ⊆ S ∧ EqOn f e W := by
  set U' : Set BTZE0 := Sum.inr ⁻¹' S
  set F : BTZE0 → BTZE0 := fun x => e0Inr.symm (f (Sum.inr x))
  have hU'r : ∀ x ∈ U', x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := fun x hx =>
    inr_mem_e0Reg_iff.1 (hSr hx)
  have hfF : ∀ x ∈ U', f (Sum.inr x) = Sum.inr (F x) := fun x hx => by
    obtain ⟨z, hz⟩ := hmaps hx
    simp only [F, ← hz, e0Inr_symm_inr]
  -- `f` is continuous on `S` and equal near each point to an element of `G`
  have hloc : ∀ x ∈ U', ∃ e ∈ e0Groupoid, Sum.inr x ∈ e.source ∧ f =ᶠ[𝓝 (Sum.inr x)] e := by
    intro x hx
    obtain ⟨e, he, hfe, hxe⟩ := hf _ hx hx
    exact ⟨e, he, hxe, Filter.eventually_of_mem ((hSo.inter e.open_source).mem_nhds ⟨hx, hxe⟩)
      fun z hz => hfe hz⟩
  have hFc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, ContinuousAt F x := by
    rintro x ⟨hx, -⟩
    obtain ⟨e, -, hxe, hfe⟩ := hloc x hx
    have hfc : ContinuousAt f (Sum.inr x) := (e.continuousAt hxe).congr hfe.symm
    have h1 : ContinuousAt e0Inr.symm (f (Sum.inr x)) :=
      e0Inr.symm.continuousAt (by rw [e0Inr_symm_source, hfF x hx]; exact ⟨_, rfl⟩)
    exact ContinuousAt.comp (g := e0Inr.symm) (f := fun x : BTZE0 => f (Sum.inr x)) h1
      (ContinuousAt.comp (g := f) (f := Sum.inr) hfc continuous_inr.continuousAt)
  have hFreg : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rintro x ⟨hx, -⟩
    obtain ⟨e, he, hfe, hxe⟩ := hf _ hx hx
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    have := mapsTo_e0Reg_of_mem he hxe (hSr hx)
    rw [← hfe' _ ⟨hx, hxe⟩, hfF x hx] at this
    exact inr_mem_e0Reg_iff.1 this
  have hFloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z := by
    rintro x ⟨hx, hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hf _ hx hx
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
    obtain ⟨c', hc', hFxc⟩ := mem_support.1 (hFreg x ⟨hx, hxr⟩)
    have hex : e (Sum.inr x) = Sum.inr (F x) := by rw [← hfe' _ ⟨hx, hxe⟩, hfF x hx]
    obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hxe).2 (hSr hx)
    obtain ⟨h, hh⟩ := hch _ (e0InrChart_mem_e0Atlas hc) _ (e0InrChart_mem_e0Atlas hc')
      (mem_e0InrChart_source.2 ⟨x, hxc, rfl⟩) (by rw [hex]; exact mem_e0InrChart_source.2 ⟨_, hFxc, rfl⟩)
    refine ⟨c, hc, hxc, c', hc', hFxc, h, ?_⟩
    have hS' : U' ∈ 𝓝 x := (hSo.preimage continuous_inr).mem_nhds hx
    have he' : Sum.inr ⁻¹' e.source ∈ 𝓝 x := (e.open_source.preimage continuous_inr).mem_nhds hxe
    filter_upwards [continuous_inr.continuousAt.eventually hh, hS', he'] with z hz hzS hze
    rw [← hfe' _ ⟨hzS, hze⟩, hfF z hzS, e0InrChart_inr, e0InrChart_inr] at hz
    exact hz
  have hFinj : InjOn F (U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) := by
    rintro x ⟨hx, -⟩ x' ⟨hx', -⟩ hxx'
    have := hinj hx hx' (by rw [hfF x hx, hfF x' hx', show F x = F x' from hxx'])
    exact Sum.inr_injective this
  obtain ⟨Ψ, ψ, g, hlift, hpos, hD, W, hWo, hWne, hWU, hWeq⟩ :=
    btzE0_localUnique_core_of_region hBo hBc hBne hBs (U := U') hBS hFc hFreg hFloc hFinj
  refine ⟨e0Lift Ψ, e0Lift_mem Ψ ψ g hlift hpos hD, by rw [e0Lift_source], Sum.inr '' W,
    isOpenMap_inr _ hWo, hWne.image _, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩; exact (hWU hw).1
  · rintro _ ⟨w, hw, rfl⟩
    rw [hfF w (hWU hw).1, e0Lift_apply, hWeq hw]

end CoreY

/-! ### `rigid` (B1): B21 `lem:liouville` -/

section Rigid

/-- The regular part of `Y` is locally connected in `Y` (with `dense_e0Reg`: portly). -/
theorem isPreconnected_inter_e0Reg {W : Set E0Y} (hW : IsOpen W) (hWc : IsPreconnected W) :
    IsPreconnected (W ∩ e0Reg) := by
  rcases Sum.isPreconnected_iff.1 hWc with ⟨t, -, rfl⟩ | ⟨t, -, rfl⟩
  · have : Sum.inl '' t ∩ e0Reg = Sum.inl '' t :=
      inter_eq_left.2 (by rintro _ ⟨m, -, rfl⟩; exact inl_mem_e0Reg m)
    rw [this]; exact hWc
  · have ht : IsOpen t := by
      have := hW.preimage continuous_inr
      rwa [Sum.inr_injective.preimage_image] at this
    have htc : IsPreconnected t := by
      have := hWc.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr
        (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
      rwa [Sum.inr_injective.preimage_image] at this
    have h1 := (isPortly_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0).locallyConnectedIn
      t ht htc
    have hpre : Sum.inr ⁻¹' e0Reg = Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
      ext x; exact inr_mem_e0Reg_iff
    rw [← image_inter_preimage, hpre]
    exact h1.image _ continuous_inr.continuousOn

/-- Two maps continuous at `x` agreeing on a set accumulating at `x` agree at `x`. -/
theorem e0_eq_of_mem_closure {f₁ f₂ : E0Y → E0Y} {x : E0Y} {S : Set E0Y}
    (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x) (hx : x ∈ closure S) (h : EqOn f₁ f₂ S) :
    f₁ x = f₂ x := by
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
  have t₁ : Tendsto f₁ (𝓝[S] x) (𝓝 (f₁ x)) := h₁.tendsto.mono_left nhdsWithin_le_nhds
  have t₂ : Tendsto f₁ (𝓝[S] x) (𝓝 (f₂ x)) :=
    (h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall
      fun y hy => (h hy).symm)
  exact tendsto_nhds_unique t₁ t₂

/-- **`rigid`** for `Y = 𝕄 ⊕ 𝔼₀` (B1; B21 `lem:liouville`, `BTZ_1.tex:361`): two elements of `G`
agreeing on a non-empty open subset of a preconnected open set agree on it. The regular part of
the open set is preconnected (`isPreconnected_inter_e0Reg`) and dense, the agreement propagates
along it by the rigidity of `Isom(𝐌³)` on `𝐌³`, and to the singular points by continuity. -/
theorem e0_rigid : ∀ e ∈ e0Groupoid, ∀ e' ∈ e0Groupoid, ∀ U : Set E0Y, IsOpen U →
    IsPreconnected U → U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty →
    EqOn e e' O → EqOn e e' U := by
  intro e he e' he' U hU hUc hUe hUe' O hOU hO hOne heq
  set R := U ∩ e0Reg
  have hR : IsPreconnected R := isPreconnected_inter_e0Reg hU hUc
  set T := interior {y | e y = e' y}
  have hOT : O ⊆ T := interior_maximal (fun y hy => heq hy) hO
  have hRT : R ⊆ T := by
    refine hR.subset_of_closure_inter_subset isOpen_interior ?_ ?_
    · obtain ⟨y, hyO, hyr⟩ := dense_e0Reg.inter_open_nonempty O hO hOne
      exact ⟨y, ⟨hOU hyO, hyr⟩, hOT hyO⟩
    · rintro x ⟨hxT, hxU, hxr⟩
      have hxe := hUe hxU
      have hxe' := hUe' hxU
      have hc₁ := ((mem_e0Groupoid_iff.1 he).1 x hxe)
      have hc₂ := ((mem_e0Groupoid_iff.1 he').1 x hxe')
      have hfx : e x = e' x :=
        e0_eq_of_mem_closure hc₁.1 hc₂.1 hxT fun y hy => interior_subset (s := {y | e y = e' y}) hy
      obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
      obtain ⟨hex, hch₁⟩ := hc₁.2 hxr
      obtain ⟨c', hc', hexc'⟩ := mem_support.1 hex
      have hexc'₂ : e' x ∈ c'.source := hfx ▸ hexc'
      obtain ⟨g₁, hg₁⟩ := hch₁ c hc c' hc' hxc hexc'
      obtain ⟨g₂, hg₂⟩ := (hc₂.2 hxr).2 c hc c' hc' hxc hexc'₂
      have hev : ∀ᶠ y in 𝓝 x, (c' (e y) = g₁ • c y ∧ c' (e' y) = g₂ • c y) ∧ y ∈ c.source ∧
          e y ∈ c'.source ∧ e' y ∈ c'.source := by
        filter_upwards [hg₁, hg₂, c.open_source.mem_nhds hxc,
          hc₁.1.eventually (c'.open_source.mem_nhds hexc'),
          hc₂.1.eventually (c'.open_source.mem_nhds hexc'₂)] with y a b d k l
        exact ⟨⟨a, b⟩, d, k, l⟩
      obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 hev
      obtain ⟨z, hzt, hzT⟩ := mem_closure_iff.1 hxT t hto hxt
      have hsmul : ∀ q : Causal.Minkowski 2, g₁ • q = g₂ • q := by
        refine IsRigidAction.smul_eq_of_eqOn (c.isOpen_image_of_subset_source
          (hto.inter isOpen_interior) fun y hy => (ht hy.1).2.1)
          ⟨c z, mem_image_of_mem _ ⟨hzt, hzT⟩⟩ ?_
        rintro _ ⟨y, ⟨hyt, hyT⟩, rfl⟩
        have hy : e y = e' y := interior_subset (s := {y | e y = e' y}) hyT
        show g₁ • c y = g₂ • c y
        rw [← (ht hyt).1.1, ← (ht hyt).1.2, hy]
      have hts : t ⊆ {y | e y = e' y} := fun y hy => by
        obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := ht hy
        exact c'.injOn h3 h4 (by rw [h1, h2, hsmul])
      exact mem_interior.2 ⟨t, hts, hto, hxt⟩
  intro x hxU
  exact e0_eq_of_mem_closure ((mem_e0Groupoid_iff.1 he).1 x (hUe hxU)).1
    ((mem_e0Groupoid_iff.1 he').1 x (hUe' hxU)).1
    (dense_e0Reg.open_subset_closure_inter hU hxU)
    fun y hy => interior_subset (s := {y | e y = e' y}) (hRT hy)

/-- **Propagation by rigidity**: a local `G`-structomorphism on a preconnected open `S` which
agrees with one element `e ∈ G` (defined on `S`) on a non-empty open subset agrees with it on all
of `S`. -/
theorem e0_eqOn_of_eqOn_open {S : Set E0Y} (hS : IsOpen S) (hSc : IsPreconnected S)
    {f : E0Y → E0Y} (hf : ∀ y ∈ S, e0Groupoid.IsLocalStructomorphWithinAt f S y)
    {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) (hSe : S ⊆ e.source)
    {W : Set E0Y} (hW : IsOpen W) (hWne : W.Nonempty) (hWS : W ⊆ S) (heq : EqOn f e W) :
    EqOn f e S := by
  set A := interior {y | f y = e y}
  have hWA : W ⊆ A := interior_maximal (fun y hy => heq hy) hW
  have hSA : S ⊆ A := by
    refine hSc.subset_of_closure_inter_subset isOpen_interior ?_ ?_
    · obtain ⟨y, hy⟩ := hWne; exact ⟨y, hWS hy, hWA hy⟩
    · rintro z ⟨hzA, hzS⟩
      obtain ⟨ez, hez, hfez₀, hzez⟩ := hf z hzS hzS
      have hfez : ∀ y ∈ S ∩ ez.source, f y = ez y := fun y hy => hfez₀ hy
      set N := connectedComponentIn (S ∩ ez.source) z
      have hNo : IsOpen N := (hS.inter ez.open_source).connectedComponentIn
      have hNsub : N ⊆ S ∩ ez.source := connectedComponentIn_subset _ _
      have hzN : z ∈ N := mem_connectedComponentIn ⟨hzS, hzez⟩
      obtain ⟨w, hwN, hwA⟩ := mem_closure_iff.1 hzA N hNo hzN
      have hagree : EqOn ez e N := by
        refine e0_rigid ez hez e he N hNo isPreconnected_connectedComponentIn
          (fun y hy => (hNsub hy).2) (fun y hy => hSe (hNsub hy).1) (N ∩ A)
          inter_subset_left (hNo.inter isOpen_interior) ⟨w, hwN, hwA⟩ ?_
        intro y hy
        show ez y = e y
        rw [← hfez y (hNsub hy.1)]
        exact interior_subset (s := {y | f y = e y}) hy.2
      refine mem_interior.2 ⟨N, fun y hy => ?_, hNo, hzN⟩
      show f y = e y
      rw [hfez y (hNsub hy), hagree hy]
  exact fun y hy => interior_subset (s := {y | f y = e y}) (hSA hy)

/-! ### `localUnique_sing` (B2 at a singular point): B21 `prop:isom_strong` at `α = β = 0` -/

/-- A singular point of `Y` is a point of the axis of `𝔼₀`, and `α = 0`. -/
theorem e0SingY_mem {α : ℝ} {y : E0Y} (h : y ∈ e0SingY α) :
    α = 0 ∧ ∃ x : BTZE0, y = Sum.inr x ∧
      x ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
  obtain ⟨rfl, hy⟩ := h
  refine ⟨rfl, ?_⟩
  rcases y with m | x
  · exact absurd (inl_mem_e0Reg m) hy
  · exact ⟨x, rfl, fun h => hy (inr_mem_e0Reg_iff.2 h)⟩

/-- The component of a point of `𝔼₀` in `Y` is `𝔼₀`. -/
theorem connectedComponent_inr_eq (x : BTZE0) :
    connectedComponent (Sum.inr x : E0Y) = range Sum.inr := by
  haveI := (btz_instances btz_two_pi_ne_zero).2.2.2
  refine (connectedComponent_inr_subset x).antisymm ?_
  exact (isPreconnected_range continuous_inr).subset_connectedComponent ⟨x, rfl⟩

/-- **The local core of `prop:isom_strong`** for `Y = 𝕄 ⊕ 𝔼₀`: under the hypotheses of the
field, some element of `G` defined on all of `𝔼₀` agrees with `f` on a non-empty open subset of
`reg(U)`. (The global statement `e0_localUnique_sing` follows by rigidity.) Proof: a box
`{r < ε₁, |t − t₀| < ε₂}` around the axis point inside `U`, in log-polar coordinates a convex set
invariant under the angle shifts; `e0_localUnique_core_of_region` (lift through the covering
`{r > 0} → reg 𝔼₀`, Liouville, the deck relation `g P = Pᵏ g`, winding `k = ±1` from injectivity,
descent of `D⁻¹ g D`). Connectedness of `U` and `0 ≤ α₀` are not used here. -/
theorem e0_localUnique_sing_core (U : Set E0Y) (hU : IsOpen U) (_hUc : IsConnected U)
    (y₀ : E0Y) (hy₀ : y₀ ∈ U) (α₀ : ℝ) (_hα₀ : 0 ≤ α₀) (hy₀s : y₀ ∈ e0SingY α₀) (f : E0Y → E0Y)
    (hf : ∀ y ∈ U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α},
      e0Groupoid.IsLocalStructomorphWithinAt f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) y)
    (hinj : InjOn f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}))
    (hmaps : MapsTo f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) (connectedComponent y₀)) :
    ∃ e ∈ e0Groupoid, connectedComponent y₀ ⊆ e.source ∧ ∃ W : Set E0Y, IsOpen W ∧
      W.Nonempty ∧ W ⊆ U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∧ EqOn f e W := by
  obtain ⟨-, x₀, rfl, hx₀⟩ := e0SingY_mem hy₀s
  have hreg : U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} = U ∩ e0Reg := by rw [e0RegSet_eq]
  rw [connectedComponent_inr_eq] at hmaps ⊢
  rw [hreg] at hf hinj hmaps ⊢
  obtain ⟨t₀, ε₁, ε₂, hε₁, hε₂, hbox⟩ :=
    btzE0_exists_box hx₀ (hU.preimage continuous_inr) (show Sum.inr x₀ ∈ U from hy₀)
  exact e0_localUnique_core_of_region (isOpen_e0Box (Real.log ε₁) t₀ ε₂) (convex_e0Box _ _ _)
    ⟨(((Real.log ε₁ - 1 : ℝ) : ℂ), t₀), by simp [e0Box, hε₂]⟩ (fun w hw s => mem_e0Box_add hw s)
    (hU.inter isOpen_e0Reg) inter_subset_right
    (fun w hw => ⟨hbox _ ((Real.lt_log_iff_exp_lt hε₁).1 hw.1) hw.2,
      inr_mem_e0Reg_iff.2 (by rw [btzE0_reg_eq]; exact ⟨_, e0BoxSec_mem w, rfl⟩)⟩) hf hinj hmaps

/-- **`localUnique_sing`** for `Y = 𝕄 ⊕ 𝔼₀` (B2 at a singular point; B21 `prop:isom_strong` at
`α = β = 0`, `BTZ_1.tex:468–475`): from the local core `e0_localUnique_sing_core` by rigidity on the
connected regular part of `U`. -/
theorem e0_localUnique_sing : ∀ U : Set E0Y, IsOpen U → IsConnected U → ∀ y₀ ∈ U, ∀ α₀ : ℝ,
    0 ≤ α₀ → y₀ ∈ e0SingY α₀ → ∀ f : E0Y → E0Y,
    (∀ y ∈ U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α},
      e0Groupoid.IsLocalStructomorphWithinAt f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) y) →
    InjOn f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) →
    MapsTo f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) (connectedComponent y₀) →
    ∃ e ∈ e0Groupoid, connectedComponent y₀ ⊆ e.source ∧
      EqOn f e (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) := by
  intro U hU hUc y₀ hy₀ α₀ hα₀ hy₀s f hf hinj hmaps
  obtain ⟨e, he, hsrc, W, hW, hWne, hWS, heq⟩ :=
    e0_localUnique_sing_core U hU hUc y₀ hy₀ α₀ hα₀ hy₀s f hf hinj hmaps
  refine ⟨e, he, hsrc, ?_⟩
  have hreg : U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} = U ∩ e0Reg := by rw [e0RegSet_eq]
  have hSo : IsOpen (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) := hreg ▸ hU.inter isOpen_e0Reg
  have hSc : IsPreconnected (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}) :=
    hreg ▸ isPreconnected_inter_e0Reg hU hUc.isPreconnected
  have hUy : U ⊆ connectedComponent y₀ := hUc.isPreconnected.subset_connectedComponent hy₀
  exact e0_eqOn_of_eqOn_open hSo hSc hf he (fun y hy => hsrc (hUy hy.1)) hW hWne hWS heq

end Rigid

/-! ### `localUnique_sing_adherent` and `typeAgreement`, over a causality of `Y` -/

section CausalFields

open TopologicalSpace

/-- **`localUnique_sing_adherent`** for `Y = 𝕄 ⊕ 𝔼₀`, the field's statement verbatim with the model
causality a parameter `C` (the causality of `Y` is WP-39e's, not yet built). -/
def E0LocalUniqueSingAdherent (C : Causal.Causality E0Y) : Prop :=
  ∀ U : Set E0Y, IsOpen U → IsConnected U →
    U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} → ∀ y₀ : E0Y, ∀ α₀ : ℝ, 0 ≤ α₀ → y₀ ∈ e0SingY α₀ →
    (∃ O : Opens E0Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∧
      C.lt O y₀ r ∧
      {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∩ C.Iplus O {y₀} ∩ C.Iminus O {r} ⊆ U) →
    ∀ z₀ ∈ e0SingY α₀, ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
    InjOn f U → MapsTo f U (connectedComponent y₀) → MapClusterPt z₀ (𝓝[U] y₀) f →
    ∃ e ∈ e0Groupoid, connectedComponent y₀ ⊆ e.source ∧ EqOn f e U

/-- **`typeAgreement`** for `Y = 𝕄 ⊕ 𝔼₀`, the field's statement verbatim with the model causality a
parameter `C`. -/
def E0TypeAgreement (C : Causal.Causality E0Y) : Prop :=
  ∀ U : Set E0Y, IsOpen U → IsConnected U → ∀ y₀ : E0Y, y₀ ∉ e0SingY 0 →
    (∃ O : Opens E0Y, y₀ ∈ O ∧ ∃ r ∈ O,
      (C.lt O r y₀ ∧ C.Iplus O {r} ∩ C.Iminus O {y₀} ⊆ U) ∨
      (C.lt O y₀ r ∧ C.Iplus O {y₀} ∩ C.Iminus O {r} ⊆ U)) →
    ∀ z₀ : E0Y, ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
    InjOn f U → MapClusterPt z₀ (𝓝[U] y₀) f →
    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ e0SingY α ↔ z₀ ∈ e0SingY α)) ∧
      ((∃ α : ℝ, 0 ≤ α ∧ y₀ ∈ e0SingY α) → z₀ ∈ connectedComponent y₀)

/-- **Reduction of `localUnique_sing_adherent`** to its local core, for every causality: it
suffices that some element of `G` defined on `𝔼₀` agrees with `f` on a non-empty open subset of
`U` (the rest is rigidity, `e0_eqOn_of_eqOn_open`). -/
theorem e0_localUniqueSingAdherent_of_local (C : Causal.Causality E0Y)
    (hloc : ∀ U : Set E0Y, IsOpen U → IsConnected U →
      U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} → ∀ y₀ : E0Y, ∀ α₀ : ℝ, 0 ≤ α₀ →
      y₀ ∈ e0SingY α₀ →
      (∃ O : Opens E0Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∧
        C.lt O y₀ r ∧
        {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∩ C.Iplus O {y₀} ∩ C.Iminus O {r} ⊆ U) →
      ∀ z₀ ∈ e0SingY α₀, ∀ f : E0Y → E0Y,
      (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
      InjOn f U → MapsTo f U (connectedComponent y₀) → MapClusterPt z₀ (𝓝[U] y₀) f →
      ∃ e ∈ e0Groupoid, connectedComponent y₀ ⊆ e.source ∧ ∃ W : Set E0Y, IsOpen W ∧
        W.Nonempty ∧ W ⊆ U ∧ EqOn f e W) :
    E0LocalUniqueSingAdherent C := by
  intro U hU hUc hUr y₀ α₀ hα₀ hy₀ hdia z₀ hz₀ f hf hinj hmaps hcl
  obtain ⟨e, he, hsrc, W, hW, hWne, hWU, heq⟩ :=
    hloc U hU hUc hUr y₀ α₀ hα₀ hy₀ hdia z₀ hz₀ f hf hinj hmaps hcl
  refine ⟨e, he, hsrc, ?_⟩
  -- `U` lies in the component of `y₀`: it is connected and adherent to `y₀`.
  have hy₀U : y₀ ∈ closure U := by
    by_contra h
    have : 𝓝[U] y₀ = ⊥ := by
      rw [← notMem_closure_iff_nhdsWithin_eq_bot]; exact h
    rw [MapClusterPt, this, Filter.map_bot] at hcl
    exact (ClusterPt.neBot hcl).ne (inf_bot_eq _)
  have hUy : U ⊆ connectedComponent y₀ := by
    have : IsPreconnected (insert y₀ U) :=
      hUc.isPreconnected.subset_closure (subset_insert _ _)
        (insert_subset hy₀U subset_closure)
    exact fun y hy => this.subset_connectedComponent (mem_insert _ _) (mem_insert_of_mem _ hy)
  exact e0_eqOn_of_eqOn_open hU hUc.isPreconnected hf he (fun y hy => hsrc (hUy hy)) hW hWne
    hWU heq

/-- **Reduction of `typeAgreement`**, for every causality: at a regular `y₀` (the only case the
field asks, `y₀ ∉ sing_0` and `sing_α = ∅` for `α ≠ 0`), the second clause is vacuous and the first
says that `z₀` is regular. -/
theorem e0_typeAgreement_of_reg (C : Causal.Causality E0Y)
    (hreg : ∀ U : Set E0Y, IsOpen U → IsConnected U → ∀ y₀ : E0Y, y₀ ∉ e0SingY 0 →
      (∃ O : Opens E0Y, y₀ ∈ O ∧ ∃ r ∈ O,
        (C.lt O r y₀ ∧ C.Iplus O {r} ∩ C.Iminus O {y₀} ⊆ U) ∨
        (C.lt O y₀ r ∧ C.Iplus O {y₀} ∩ C.Iminus O {r} ⊆ U)) →
      ∀ z₀ : E0Y, ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
      InjOn f U → MapClusterPt z₀ (𝓝[U] y₀) f → z₀ ∈ e0Reg) :
    E0TypeAgreement C := by
  intro U hU hUc y₀ hy₀ hdia z₀ f hf hinj hcl
  have hy₀r : y₀ ∈ e0Reg := by
    by_contra h; exact hy₀ ⟨rfl, h⟩
  have hz₀r := hreg U hU hUc y₀ hy₀ hdia z₀ f hf hinj hcl
  refine ⟨fun α _ => ?_, fun ⟨α, _, h⟩ => absurd h.2 (not_not.2 hy₀r)⟩
  simp only [e0SingY, mem_setOf_eq, not_not.2 hy₀r, not_not.2 hz₀r, and_false]

/-- **Reduction of `localUnique_sing_adherent` to a property of the causality `C` alone**: it holds
as soon as every chronological diamond `reg ∩ I⁺_O(y₀) ∩ I⁻_O(r)` with a BTZ tip `y₀` contains the
image of a region swept by whole circles around the axis (an open, convex, non-empty `B ⊆ ℂ × ℝ`
invariant under the angle shifts, read through `(log r + iθ, t) ↦ [r, θ, t]`). The rest is
`e0_localUnique_core_of_region` and rigidity. -/
theorem e0_localUniqueSingAdherent_of_region (C : Causal.Causality E0Y)
    (hdiam : ∀ y₀ : E0Y, y₀ ∈ e0SingY 0 → ∀ O : Opens E0Y, y₀ ∈ O → ∀ r ∈ O,
      r ∈ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} → C.lt O y₀ r →
      ∃ B : Set (ℂ × ℝ), IsOpen B ∧ Convex ℝ B ∧ B.Nonempty ∧
        (∀ w ∈ B, ∀ s : ℝ, w + ((s : ℂ) * Complex.I, 0) ∈ B) ∧
        ∀ w ∈ B, (Sum.inr (orbitMk (GammaA (2 * π)) (e0BoxSec w)) : E0Y) ∈
          {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} ∩ C.Iplus O {y₀} ∩ C.Iminus O {r}) :
    E0LocalUniqueSingAdherent C := by
  refine e0_localUniqueSingAdherent_of_local C
    fun U hU _ hUr y₀ α₀ _ hy₀ hdia _ _ f hf hinj hmaps _ => ?_
  obtain ⟨rfl, x₀, rfl, -⟩ := e0SingY_mem hy₀
  obtain ⟨O, hyO, r, hrO, hrreg, hlt, hsub⟩ := hdia
  obtain ⟨B, hBo, hBc, hBne, hBs, hBS⟩ := hdiam _ hy₀ O hyO r hrO hrreg hlt
  rw [connectedComponent_inr_eq] at hmaps ⊢
  have hUr' : U ⊆ e0Reg := fun y hy => by rw [← e0RegSet_eq]; exact hUr hy
  exact e0_localUnique_core_of_region hBo hBc hBne hBs hU hUr' (fun w hw => hsub (hBS w hw)) hf
    hinj hmaps

end CausalFields

/-! ### `typeAgreement`, the convergence form -/

section TypeAgreementTendsto

open TopologicalSpace

/-- `typeAgreement` with the cluster hypothesis strengthened to convergence. -/
def E0TypeAgreementTendsto (C : Causal.Causality E0Y) : Prop :=
  ∀ U : Set E0Y, IsOpen U → IsConnected U → ∀ y₀ : E0Y, y₀ ∉ e0SingY 0 →
    (∃ O : Opens E0Y, y₀ ∈ O ∧ ∃ r ∈ O,
      (C.lt O r y₀ ∧ C.Iplus O {r} ∩ C.Iminus O {y₀} ⊆ U) ∨
      (C.lt O y₀ r ∧ C.Iplus O {y₀} ∩ C.Iminus O {r} ⊆ U)) →
    ∀ z₀ : E0Y, ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
    InjOn f U → Tendsto f (𝓝[U] y₀) (𝓝 z₀) →
    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ e0SingY α ↔ z₀ ∈ e0SingY α)) ∧
      ((∃ α : ℝ, 0 ≤ α ∧ y₀ ∈ e0SingY α) → z₀ ∈ connectedComponent y₀)


/-! #### The open future cone in null coordinates -/

/-- The open future timelike cone of `(ℝ³, nullQ)`: `b > 0`, `c² < ab` (the same body as
`GX.e0TACone` of `GXScaffold.BTZ.Causality`). -/
def e0TACone (V : ℝ × ℝ × ℝ) : Prop := 0 < V.2.1 ∧ V.2.2 ^ 2 < V.1 * V.2.1

theorem e0TACone.fst_pos {V : ℝ × ℝ × ℝ} (h : e0TACone V) : 0 < V.1 := by
  obtain ⟨hb, hc⟩ := h
  by_contra ha
  have ha' : V.1 ≤ 0 := not_lt.1 ha
  nlinarith [sq_nonneg V.2.2]

theorem e0TA_cross_le {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁)
    (h₁ : c₁ ^ 2 ≤ a₁ * b₁) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) (h₂ : c₂ ^ 2 ≤ a₂ * b₂) :
    2 * (c₁ * c₂) ≤ a₁ * b₂ + a₂ * b₁ := by
  have hprod : (c₁ * c₂) ^ 2 ≤ (a₁ * b₁) * (a₂ * b₂) := by
    rw [mul_pow]; exact mul_le_mul h₁ h₂ (sq_nonneg _) (mul_nonneg ha₁ hb₁)
  have hamgm : 4 * ((a₁ * b₁) * (a₂ * b₂)) ≤ (a₁ * b₂ + a₂ * b₁) ^ 2 := by
    nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]
  have hS : 0 ≤ a₁ * b₂ + a₂ * b₁ := by positivity
  have h4 : (2 * (c₁ * c₂)) ^ 2 ≤ (a₁ * b₂ + a₂ * b₁) ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h4 hS).2

theorem e0TACone.smul {V : ℝ × ℝ × ℝ} (hV : e0TACone V) {s : ℝ} (hs : 0 < s) :
    e0TACone (s • V) := by
  obtain ⟨hb, h⟩ := hV
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]; positivity
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
    have : (s * V.2.2) ^ 2 = s ^ 2 * V.2.2 ^ 2 := by ring
    rw [this, show s * V.1 * (s * V.2.1) = s ^ 2 * (V.1 * V.2.1) by ring]
    exact mul_lt_mul_of_pos_left h (by positivity)

theorem e0TACone.add {V W : ℝ × ℝ × ℝ} (hV : e0TACone V) (hW : e0TACone W) :
    e0TACone (V + W) := by
  have ha₁ := hV.fst_pos.le
  have ha₂ := hW.fst_pos.le
  obtain ⟨hb₁, h₁⟩ := hV
  obtain ⟨hb₂, h₂⟩ := hW
  have hx := e0TA_cross_le ha₁ hb₁.le h₁.le ha₂ hb₂.le h₂.le
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add]; linarith
  · simp only [Prod.fst_add, Prod.snd_add]
    nlinarith

theorem e0TA_isOpen_cone : IsOpen {V : ℝ × ℝ × ℝ | e0TACone V} := by
  have h1 : Continuous fun V : ℝ × ℝ × ℝ => V.2.1 := continuous_snd.fst
  have h2 : Continuous fun V : ℝ × ℝ × ℝ => V.2.2 ^ 2 := continuous_snd.snd.pow 2
  have h3 : Continuous fun V : ℝ × ℝ × ℝ => V.1 * V.2.1 := continuous_fst.mul continuous_snd.fst
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt h2 h3)

/-- **Minkowski's chronology in null coordinates**: `nullToMink P ≪ nullToMink Q` iff `Q − P` lies
in the open future cone. -/
theorem e0TA_minkowski_lt_iff (P Q : ℝ × ℝ × ℝ) :
    (Causal.minkowski 2).lt ⊤ (nullToMink P) (nullToMink Q) ↔ e0TACone (Q - P) := by
  rw [Causal.Flat.lt_top_iff_minkQ, ← map_sub, isFutureTimelike_nullToMink_iff]
  simp only [nullτ_apply, nullQ]
  constructor
  · rintro ⟨hc, hab⟩
    refine ⟨?_, by linarith⟩
    by_contra h
    have h' : (Q - P).2.1 ≤ 0 := not_lt.1 h
    have ha : 0 < (Q - P).1 := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le h', sq_nonneg (Q - P).2.2]
  · intro h
    have ha := h.fst_pos
    obtain ⟨hb, hc⟩ := h
    exact ⟨by linarith, by linarith⟩

theorem e0TA_btzDevInv_mem {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) : btzDevInv v ∈ cylPos ℝ := by
  have h := btzDev_e0_b (btzDevInv v)
  rw [btzDev_btzDevInv (Or.inl hv)] at h
  show 0 < (btzDevInv v).1.r
  rw [← h]; exact hv

/-- A local `G`-structomorphism on an open `U` is continuous at every point of `U`. -/
theorem e0TA_continuousAt {U : Set E0Y} (hU : IsOpen U) {f : E0Y → E0Y}
    (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) {y : E0Y} (hy : y ∈ U) :
    ContinuousAt f y := by
  obtain ⟨e, -, heq, hye⟩ := hf y hy hy
  have h : f =ᶠ[𝓝 y] e :=
    Filter.eventually_of_mem ((hU.inter e.open_source).mem_nhds ⟨hy, hye⟩) fun z hz => heq hz
  exact (e.continuousAt hye).congr h.symm

/-- **Lift and Liouville on a convex region of `𝐌³`** (null coordinates). Let `ι` map an open
convex `K ⊆ ℝ³` into `U ∩ reg Y`, read in regular charts of `Y` as translates of `nullToMink`, and
let `f` be a local `G`-structomorphism on `U` sending `ι(K)` into `𝔼₀`. Then `f ∘ ι` lifts through
the covering `{r > 0} → reg 𝔼₀` to `L`, and `D ∘ L = g · nullToMink` on `K` for one `g ∈ Isom(𝐌³)`. -/
theorem e0TA_lift {K : Set (ℝ × ℝ × ℝ)} (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {ι : ℝ × ℝ × ℝ → E0Y} (hιc : ContinuousOn ι K)
    (hchart : ∀ v ∈ K, ∃ c ∈ e0Atlas, ι v ∈ c.source ∧ ∃ g₁ : Causal.Flat.isom 2,
      ∀ᶠ v' in 𝓝 v, c (ι v') = g₁ • nullToMink v')
    {U : Set E0Y} (hU : IsOpen U) (hιU : ∀ v ∈ K, ι v ∈ U) (hιreg : ∀ v ∈ K, ι v ∈ e0Reg)
    {f : E0Y → E0Y} (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y)
    (hfr : ∀ v ∈ K, f (ι v) ∈ range Sum.inr) :
    ∃ (L : ℝ × ℝ × ℝ → DInfty × ℝ) (g : Causal.Flat.isom 2), ∀ v ∈ K, L v ∈ cylPos ℝ ∧
      f (ι v) = Sum.inr (orbitMk (GammaA (2 * π)) (L v)) ∧
      btzDevM 0 btzV0 (L v) = g • nullToMink v := by
  classical
  obtain ⟨w₀, hw₀⟩ := hKne
  haveI : ContractibleSpace K := hKc.contractibleSpace ⟨_, hw₀⟩
  haveI : LocPathConnectedSpace K := hKo.locPathConnectedSpace
  set R : E0Y → BTZE0 := Sum.elim (fun _ => orbitMk (GammaA (2 * π)) (DInfty.apex, 0)) id
    with hRdef
  have hR : Continuous R := Continuous.sumElim continuous_const continuous_id
  have hfR : ∀ v ∈ K, f (ι v) = Sum.inr (R (f (ι v))) := fun v hv => by
    obtain ⟨x, hx⟩ := hfr v hv; rw [← hx]; rfl
  have hιa : ∀ a : K, ContinuousAt (fun a' : K => ι a'.1) a := fun a =>
    (hιc.continuousAt (hKo.mem_nhds a.2)).comp continuous_subtype_val.continuousAt
  have hφc : Continuous fun a : K => R (f (ι a.1)) :=
    hR.comp (continuous_iff_continuousAt.2 fun a =>
      ContinuousAt.comp (g := f) (e0TA_continuousAt hU hf (hιU _ a.2)) (hιa a))
  set φ : C(K, BTZE0) := ⟨_, hφc⟩
  have hreg : ∀ a : K, φ a ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := fun a => by
    obtain ⟨e, he, heq, hye⟩ := hf _ (hιU _ a.2) (hιU _ a.2)
    have h1 := mapsTo_e0Reg_of_mem he hye (hιreg _ a.2)
    have h2 : f (ι a.1) = e (ι a.1) := heq ⟨hιU _ a.2, hye⟩
    rw [← h2, hfR _ a.2] at h1
    exact inr_mem_e0Reg_iff.1 h1
  have hs : ∀ a, φ a ∈ orbitMk (GammaA (2 * π)) '' cylPos ℝ := fun a => by
    rw [← btzE0_reg_eq]; exact hreg a
  have hcov := isCoveringMapOn_orbitMk_cylPos (Z := ℝ) btz_two_pi_ne_zero
  set a₀ : K := ⟨_, hw₀⟩
  obtain ⟨e₀, -, he₀⟩ := hs a₀
  obtain ⟨L, ⟨-, hLq⟩, -⟩ := hcov.existsUnique_continuousMap_lifts φ he₀ hs
  have hLq' : ∀ a, orbitMk (GammaA (2 * π)) (L a) = φ a := fun a => congrFun hLq a
  have hLP : ∀ a, L a ∈ cylPos ℝ := fun a => by
    have : L a ∈ orbitMk (GammaA (2 * π)) ⁻¹' (orbitMk (GammaA (2 * π)) '' cylPos ℝ) := by
      rw [mem_preimage, hLq']; exact hs a
    rwa [preimage_image_cylPos] at this
  -- `D ∘ L` is locally a translate of `nullToMink`
  have hloc : ∀ a ∈ (univ : Set K), ∃ g : Causal.Flat.isom 2,
      ∀ᶠ a' in 𝓝 a, btzDevM 0 btzV0 (L a') = g • nullToMink a'.1 := by
    intro a _
    obtain ⟨c, hc, hac, g₁, hg₁⟩ := hchart a.1 a.2
    obtain ⟨e, he, heq, hye⟩ := hf _ (hιU _ a.2) (hιU _ a.2)
    obtain ⟨c₀', hc₀', hφc₀'⟩ := mem_support.1 (hreg a)
    have hc' := e0InrChart_mem_e0Atlas hc₀'
    have h2 : f (ι a.1) = e (ι a.1) := heq ⟨hιU _ a.2, hye⟩
    have hfa : e (ι a.1) ∈ (e0Inr.symm.trans c₀').source := by
      rw [← h2, hfR _ a.2]; exact mem_e0InrChart_source.2 ⟨_, hφc₀', rfl⟩
    obtain ⟨h, hh⟩ := (((mem_e0Groupoid_iff.1 he).1 _ hye).2 (hιreg _ a.2)).2 c hc _ hc' hac hfa
    have hLc : orbitMk (GammaA (2 * π)) (L a) ∈ c₀'.source := by rw [hLq']; exact hφc₀'
    obtain ⟨g₂, hg₂⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 (hLP a) hc₀' hLc
    refine ⟨g₂ * h * g₁, ?_⟩
    have hUe : ∀ᶠ y in 𝓝 (ι a.1), f y = e y :=
      Filter.eventually_of_mem ((hU.inter e.open_source).mem_nhds ⟨hιU _ a.2, hye⟩)
        fun y hy => (heq hy : f y = e y)
    filter_upwards [L.continuous.continuousAt.eventually hg₂, (hιa a).eventually hh,
      (hιa a).eventually hUe, continuous_subtype_val.continuousAt.eventually hg₁] with a' e1 e2 e3 e4
    have e5 : c₀' (orbitMk (GammaA (2 * π)) (L a')) = (e0Inr.symm.trans c₀') (f (ι a'.1)) := by
      rw [hfR _ a'.2, e0InrChart_inr, hLq']; rfl
    rw [e1, e5, e3, e2, e4, mul_smul, mul_smul]
  have hD : IsLocalHomeomorphOn (fun a : K => nullToMink a.1) univ :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.1
      (nullToMinkHomeomorph.isLocalHomeomorph.comp hKo.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn (G := Causal.Flat.isom 2)
    (F := fun a : K => btzDevM 0 btzV0 (L a)) isOpen_univ hD isPreconnected_univ subset_rfl hloc
  refine ⟨fun v => if h : v ∈ K then L ⟨v, h⟩ else (DInfty.apex, 0), g, fun v hv => ?_⟩
  simp only [dif_pos hv]
  refine ⟨hLP _, ?_, hg _ trivial⟩
  rw [hfR v hv, hLq']; rfl

/-- **The tip goes to the singular line.** If on `K` the lift `L` develops as `g · nullToMink` and
`[L v] → x₁` at a BTZ point as `v → v₀` in `K`, then `g · nullToMink v₀` lies on the line `ℝu`:
the `b`-coordinate of `D(L v)` is `r(L v) → 0`, and `nullQ (D (L v)) = r² − r t → 0`. -/
theorem e0TA_tip {F : Filter (ℝ × ℝ × ℝ)} [hne : F.NeBot] {v₀ : ℝ × ℝ × ℝ} (hF : F ≤ 𝓝 v₀)
    {L : ℝ × ℝ × ℝ → DInfty × ℝ} {g : Causal.Flat.isom 2}
    (hL : ∀ᶠ v in F, btzDevM 0 btzV0 (L v) = g • nullToMink v) {x₁ : BTZE0}
    (hx₁ : x₁ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
    (hT : Tendsto (fun v => orbitMk (GammaA (2 * π)) (L v)) F (𝓝 x₁)) :
    ∃ a : ℝ, g • nullToMink v₀ = nullToMink (a • nullU) := by
  have hS : x₁ ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := hx₁
  rw [btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0] at hS
  obtain ⟨⟨p, t₁⟩, hp, rfl⟩ := hS
  simp only [mem_setOf_eq] at hp
  subst hp
  set G : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun v => nullToMink.symm (g • nullToMink v) with hGdef
  have hGc : Continuous G := by
    have h1 : Continuous fun v : ℝ × ℝ × ℝ => g • nullToMink v :=
      (continuous_const_smul g).comp nullToMinkHomeomorph.continuous
    exact nullToMinkHomeomorph.symm.continuous.comp h1
  have hGL : ∀ᶠ v in F, btzDev 0 btzV0 (L v) = G v := hL.mono fun v hv => by
    apply nullToMink.injective
    rw [hGdef]; simp only [LinearEquiv.apply_symm_apply]
    exact hv
  have hr : Tendsto (fun v => (L v).1.r) F (𝓝 0) := by
    have h := ((continuous_norm.comp (continuous_fst.comp
      (cylHomeomorph btz_two_pi_ne_zero ℝ).continuous)).tendsto _).comp hT
    simp only [Function.comp_def, cylHomeomorph_apply, DInfty.norm_cplx, DInfty.apex_r] at h
    exact h
  have ht : Tendsto (fun v => (L v).2) F (𝓝 t₁) := by
    have h := ((continuous_snd.comp (cylHomeomorph btz_two_pi_ne_zero ℝ).continuous).tendsto
      _).comp hT
    simp only [Function.comp_def, cylHomeomorph_apply] at h
    exact h
  have hGt : Tendsto G F (𝓝 (G v₀)) := hGc.continuousAt.tendsto.mono_left hF
  have hb : (G v₀).2.1 = 0 := by
    have h1 : Tendsto (fun v => (G v).2.1) F (𝓝 (G v₀).2.1) :=
      ((continuous_fst.comp continuous_snd).tendsto _).comp hGt
    refine tendsto_nhds_unique h1 (hr.congr' ?_)
    filter_upwards [hGL] with v hv
    rw [← hv, btzDev_e0_b]
  have hq : nullQ (G v₀) = 0 := by
    have hQc : Continuous nullQ := by unfold nullQ; fun_prop
    have h1 : Tendsto (fun v => nullQ (G v)) F (𝓝 (nullQ (G v₀))) :=
      (hQc.tendsto _).comp hGt
    have h2 : Tendsto (fun v => (L v).1.r ^ 2 - (L v).1.r * (L v).2) F
        (𝓝 (0 ^ 2 - 0 * t₁)) := (hr.pow 2).sub (hr.mul ht)
    rw [zero_pow two_ne_zero, zero_mul, sub_zero] at h2
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [hGL] with v hv
    rw [← hv, nullQ_btzDev_e0]
  have hc : (G v₀).2.2 = 0 := by
    have : (G v₀).2.2 ^ 2 - (G v₀).1 * (G v₀).2.1 = 0 := hq
    rw [hb, mul_zero, sub_zero] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨(G v₀).1, ?_⟩
  have hGv : G v₀ = (G v₀).1 • nullU := by
    ext <;> simp [nullU, hb, hc]
  rw [← hGv, hGdef]; simp only [LinearEquiv.apply_symm_apply]

/-- The open future timelike cone (null coordinates) is convex. -/
theorem e0TA_nullConeLt_combo {V W : ℝ × ℝ × ℝ} (hV : e0TACone V) (hW : e0TACone W)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : e0TACone (a • V + b • W) := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; simpa using hW
  · rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab; simpa using hV
    · exact (hV.smul ha').add (hW.smul hb')

theorem e0TA_convex_past (v₀ : ℝ × ℝ × ℝ) : Convex ℝ {v | e0TACone (v₀ - v)} := by
  intro x hx y hy a b ha hb hab
  have h : a • (v₀ - x) + b • (v₀ - y) = (a + b) • v₀ - (a • x + b • y) := by module
  rw [hab, one_smul] at h
  show e0TACone (v₀ - (a • x + b • y))
  rw [← h]; exact e0TA_nullConeLt_combo hx hy ha hb hab

theorem e0TA_convex_future (v₀ : ℝ × ℝ × ℝ) : Convex ℝ {v | e0TACone (v - v₀)} := by
  intro x hx y hy a b ha hb hab
  have h : a • (x - v₀) + b • (y - v₀) = (a • x + b • y) - (a + b) • v₀ := by module
  rw [hab, one_smul] at h
  show e0TACone ((a • x + b • y) - v₀)
  rw [← h]; exact e0TA_nullConeLt_combo hx hy ha hb hab

/-- The timelike vector `(1, 1, 0)` of null coordinates. -/
theorem e0TA_cone_e : e0TACone ((1, 1, 0) : ℝ × ℝ × ℝ) := ⟨one_pos, by norm_num⟩

/-- **The contradiction from a representation** on a cone region `K` at `v₀`: `f ∘ ι = [L]` with
`D ∘ L = g · nullToMink` on `K`, and `g · v₀` on the line `ℝu`. Past cone: `g` maps it below the
null plane, where `D` takes no value. Future cone: `P` fixes `g · v₀`, so `g⁻¹ P g` maps a point `u`
of the cone to another point `u'` of the cone with `[L u'] = [L u]`, against injectivity. -/
theorem e0TA_absurd_rep {ι : ℝ × ℝ × ℝ → E0Y} {v₀ : ℝ × ℝ × ℝ} {ε₀ : ℝ}
    (hinj : InjOn ι (Metric.ball v₀ ε₀)) {K : Set (ℝ × ℝ × ℝ)} (hKne : K.Nonempty)
    (hKb : K ⊆ Metric.ball v₀ ε₀)
    (hcone : (∀ v ∈ K, e0TACone (v₀ - v)) ∨
      (∃ ε > 0, ∀ v, dist v v₀ < ε → e0TACone (v - v₀) → v ∈ K))
    {U : Set E0Y} (hιU : ∀ v ∈ K, ι v ∈ U) {f : E0Y → E0Y} (hfinj : InjOn f U)
    {L : ℝ × ℝ × ℝ → DInfty × ℝ} {g : Causal.Flat.isom 2}
    (hL : ∀ v ∈ K, L v ∈ cylPos ℝ ∧ f (ι v) = Sum.inr (orbitMk (GammaA (2 * π)) (L v)) ∧
      btzDevM 0 btzV0 (L v) = g • nullToMink v)
    {a : ℝ} (ha : g • nullToMink v₀ = nullToMink (a • nullU)) : False := by
  rcases hcone with hpast | ⟨ε, hε, hfut⟩
  · -- past cone: `b < 0` below the line, `b = r > 0` on the image
    obtain ⟨v, hv⟩ := hKne
    have h1 : (Causal.minkowski 2).lt ⊤ (nullToMink v) (nullToMink v₀) :=
      (e0TA_minkowski_lt_iff v v₀).2 (hpast v hv)
    have h2 := (Causal.Flat.isom_lt_top_iff g).2 h1
    rw [← (hL v hv).2.2, ha, btzDevM, e0TA_minkowski_lt_iff] at h2
    have h3 := h2.1
    have h4 : (L v).1.r > 0 := (hL v hv).1
    simp only [Prod.snd_sub, Prod.fst_sub, btzDev_e0_b, nullU, Prod.smul_snd, Prod.smul_fst,
      smul_zero] at h3
    linarith
  · -- future cone: the parabolic `P` identifies two points of the cone
    set P : Causal.Flat.isom 2 := btzHol 0 (2 * π)
    have hfix : P • (g • nullToMink v₀) = g • nullToMink v₀ :=
      btzHol_smul_of_mem_btzLine 0 (2 * π) ⟨a, by show nullToMink (0 + a • nullU) = _; rw [zero_add, ha]⟩
    set h : Causal.Flat.isom 2 := g⁻¹ * P * g with hhdef
    have hhfix : h • nullToMink v₀ = nullToMink v₀ := by
      rw [hhdef, mul_smul, mul_smul, hfix, inv_smul_smul]
    set e : ℝ × ℝ × ℝ := (1, 1, 0)
    set u : ℝ → ℝ × ℝ × ℝ := fun s => v₀ + s • e with hudef
    set u' : ℝ → ℝ × ℝ × ℝ := fun s => nullToMink.symm (h • nullToMink (u s)) with hu'def
    have hu : Continuous u := continuous_const.add (continuous_id.smul continuous_const)
    have hu' : Continuous u' := nullToMinkHomeomorph.symm.continuous.comp
      ((continuous_const_smul h).comp (nullToMinkHomeomorph.continuous.comp hu))
    have hu0 : u 0 = v₀ := by simp [hudef]
    have hu'0 : u' 0 = v₀ := by
      simp only [hu'def, hu0, hhfix, LinearEquiv.symm_apply_apply]
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), dist (u s) v₀ < min ε ε₀ ∧ dist (u' s) v₀ < min ε ε₀ ∧
        0 < s := by
      have hm : (0 : ℝ) < min ε ε₀ := lt_min hε (by
        obtain ⟨v, hv⟩ := hKne; exact (Metric.pos_of_mem_ball (hKb hv)))
      have t1 : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 v₀) :=
        (hu0 ▸ hu.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      have t2 : Tendsto u' (𝓝[>] (0 : ℝ)) (𝓝 v₀) :=
        (hu'0 ▸ hu'.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      filter_upwards [t1 (Metric.ball_mem_nhds _ hm), t2 (Metric.ball_mem_nhds _ hm),
        self_mem_nhdsWithin] with s h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨s, hs1, hs2, hs0⟩ := hev.exists
    have hcu : e0TACone (u s - v₀) := by
      have : u s - v₀ = s • e := by simp [hudef]
      rw [this]; exact e0TA_cone_e.smul hs0
    have huK : u s ∈ K := hfut _ (hs1.trans_le (min_le_left _ _)) hcu
    have hcu' : e0TACone (u' s - v₀) := by
      rw [← e0TA_minkowski_lt_iff]
      have e1 : nullToMink (u' s) = h • nullToMink (u s) := by
        simp only [hu'def, LinearEquiv.apply_symm_apply]
      rw [e1, ← hhfix, Causal.Flat.isom_lt_top_iff, e0TA_minkowski_lt_iff]
      exact hcu
    have hu'K : u' s ∈ K := hfut _ (hs2.trans_le (min_le_left _ _)) hcu'
    have hD : btzDevM 0 btzV0 (L (u' s)) =
        btzDevM 0 btzV0 ((GammaA.ofInt 1 : GammaA (2 * π)) • L (u s)) := by
      rw [btzDevM_smul, GammaA.toInt_ofInt, zpow_one, (hL _ hu'K).2.2, (hL _ huK).2.2]
      have e1 : nullToMink (u' s) = h • nullToMink (u s) := by
        simp only [hu'def, LinearEquiv.apply_symm_apply]
      rw [e1, hhdef, ← mul_smul, ← mul_smul]
      congr 1
      simp only [mul_assoc, mul_inv_cancel_left]; rfl
    have hLeq := btzDevM_injective 0 btzV0_pos hD
    have hfeq : f (ι (u' s)) = f (ι (u s)) := by
      rw [(hL _ hu'K).2.1, (hL _ huK).2.1, hLeq, orbitMk_smul]
    have hueq : u' s = u s := hinj (hKb hu'K) (hKb huK) (hfinj (hιU _ hu'K) (hιU _ huK) hfeq)
    rw [hueq] at hLeq
    exact btzDevM_ofInt_one_smul_ne 0 btzV0_pos btz_two_pi_ne_zero (hL _ huK).1
      (congrArg (btzDevM 0 btzV0) hLeq.symm)


/-- **The contradiction**, on a cone region `K` at `v₀` read through `ι`, for a BTZ cluster value.
Past cone: `g` maps the past cone of `v₀` into the past of a point of `ℝu`, where `b < 0`, while
`D(L v)` has `b = r > 0`. Future cone: `P` fixes the image of the tip, so `g⁻¹ P g` maps a point
`u` of the cone to another point `u'` of the cone with `D(L u') = P · D(L u)`, i.e.
`[L u'] = [L u]`, against injectivity. -/
theorem e0TA_absurd {ι : ℝ × ℝ × ℝ → E0Y} {Ω : Set (ℝ × ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hιc : ContinuousOn ι Ω) (hιreg : ∀ v ∈ Ω, ι v ∈ e0Reg)
    (hchart : ∀ v ∈ Ω, ∃ c ∈ e0Atlas, ι v ∈ c.source ∧ ∃ g₁ : Causal.Flat.isom 2,
      ∀ᶠ v' in 𝓝 v, c (ι v') = g₁ • nullToMink v')
    {v₀ : ℝ × ℝ × ℝ} (hv₀ : v₀ ∈ Ω) {ε₀ : ℝ} (hinj : InjOn ι (Metric.ball v₀ ε₀))
    {K : Set (ℝ × ℝ × ℝ)} (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    (hNe : (𝓝[K] v₀).NeBot) (hKΩ : K ⊆ Ω) (hKb : K ⊆ Metric.ball v₀ ε₀)
    (hcone : (∀ v ∈ K, e0TACone (v₀ - v)) ∨
      (∃ ε > 0, ∀ v, dist v v₀ < ε → e0TACone (v - v₀) → v ∈ K))
    {U : Set E0Y} (hU : IsOpen U) (hιU : ∀ v ∈ K, ι v ∈ U)
    {z₀ : E0Y} {f : E0Y → E0Y} (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y)
    (hfinj : InjOn f U) (hT : Tendsto f (𝓝[U] (ι v₀)) (𝓝 z₀)) (hz : z₀ ∉ e0Reg) : False := by
  obtain ⟨x₁, rfl, hx₁⟩ : ∃ x₁ : BTZE0, z₀ = Sum.inr x₁ ∧
      x₁ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rcases z₀ with m | x
    · exact absurd (inl_mem_e0Reg m) hz
    · exact ⟨x, rfl, fun h => hz (inr_mem_e0Reg_iff.2 h)⟩
  have hιv₀ : ContinuousAt ι v₀ := hιc.continuousAt (hΩ.mem_nhds hv₀)
  have hT' : Tendsto (f ∘ ι) (𝓝[K] v₀) (𝓝 (Sum.inr x₁)) :=
    hT.comp (tendsto_nhdsWithin_iff.2 ⟨hιv₀.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono hιU⟩)
  -- `f ∘ ι` maps `K` into `𝔼₀`
  have hcont : ContinuousOn (f ∘ ι) K := fun v hv =>
    ((e0TA_continuousAt hU hf (hιU v hv)).comp
      (hιc.continuousAt (hΩ.mem_nhds (hKΩ hv)))).continuousWithinAt
  obtain ⟨v₁, hv₁r, hv₁K⟩ := ((hT'.eventually (isOpen_range_inr.mem_nhds ⟨x₁, rfl⟩)).and
    eventually_mem_nhdsWithin).exists
  have hsub := (hKc.isPreconnected.image _ hcont).subset_isClopen isClopen_range_inr
    ⟨_, ⟨v₁, hv₁K, rfl⟩, hv₁r⟩
  have hfr : ∀ v ∈ K, f (ι v) ∈ range Sum.inr := fun v hv => hsub ⟨v, hv, rfl⟩
  obtain ⟨L, g, hL⟩ := e0TA_lift hKo hKc hKne (hιc.mono hKΩ) (fun v hv => hchart v (hKΩ hv)) hU
    hιU (fun v hv => hιreg v (hKΩ hv)) hf hfr
  have hTq : Tendsto (fun v => orbitMk (GammaA (2 * π)) (L v)) (𝓝[K] v₀) (𝓝 x₁) := by
    rw [(IsEmbedding.inr : IsEmbedding (Sum.inr : BTZE0 → E0Y)).tendsto_nhds_iff]
    refine hT'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hL v hv).2.1
  obtain ⟨a, ha⟩ := e0TA_tip nhdsWithin_le_nhds
    (eventually_mem_nhdsWithin.mono fun v hv => (hL v hv).2.2) hx₁ hTq
  exact e0TA_absurd_rep hinj hKne hKb hcone hιU hfinj hL ha

/-- A ball at the tip on which `ι` stays in `Ω`, `O` and an open `W ∋ ι v₀`. -/
theorem e0TA_exists_ball {ι : ℝ × ℝ × ℝ → E0Y} {Ω : Set (ℝ × ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hιc : ContinuousOn ι Ω) {v₀ : ℝ × ℝ × ℝ} (hv₀ : v₀ ∈ Ω) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {O : Opens E0Y} {W : Set E0Y} (hWo : IsOpen W) (hyO : ι v₀ ∈ O) (hyW : ι v₀ ∈ W) :
    ∃ ε > 0, ε ≤ ε₀ ∧ ∀ v ∈ Metric.ball v₀ ε, v ∈ Ω ∧ ι v ∈ O ∧ ι v ∈ W := by
  have hN : IsOpen (Ω ∩ ι ⁻¹' ((O : Set E0Y) ∩ W)) :=
    hιc.isOpen_inter_preimage hΩ (O.isOpen.inter hWo)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hN v₀ ⟨hv₀, hyO, hyW⟩
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, min_le_left _ _, fun v hv => ?_⟩
  have := hball (Metric.ball_subset_ball (min_le_right _ _) hv)
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- A ball at the tip cut by an open convex `S` containing the open ray `v₀ + (0, ∞) d`: open,
convex, non-empty, with the tip adherent. -/
theorem e0TA_cone_facts (v₀ : ℝ × ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) {S : Set (ℝ × ℝ × ℝ)}
    (hSo : IsOpen S) (hSc : Convex ℝ S) (d : ℝ × ℝ × ℝ) (hd : ∀ s : ℝ, 0 < s → v₀ + s • d ∈ S) :
    IsOpen (Metric.ball v₀ ε ∩ S) ∧ Convex ℝ (Metric.ball v₀ ε ∩ S) ∧
      (Metric.ball v₀ ε ∩ S).Nonempty ∧ (𝓝[Metric.ball v₀ ε ∩ S] v₀).NeBot := by
  have hpath : Tendsto (fun s : ℝ => v₀ + s • d) (𝓝[>] 0) (𝓝 v₀) := by
    have hc : Continuous fun s : ℝ => v₀ + s • d :=
      continuous_const.add (continuous_id.smul continuous_const)
    have := hc.continuousAt (x := 0) |>.tendsto
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), v₀ + s • d ∈ Metric.ball v₀ ε ∩ S := by
    filter_upwards [hpath (Metric.ball_mem_nhds _ hε), self_mem_nhdsWithin] with s h1 h2
    exact ⟨h1, hd s h2⟩
  exact ⟨Metric.isOpen_ball.inter hSo, (convex_ball v₀ ε).inter hSc,
    (let ⟨s, hs⟩ := hmem.exists; ⟨_, hs⟩),
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_of_tendsto hpath hmem)⟩

theorem e0TA_isOpen_past (v₀ : ℝ × ℝ × ℝ) : IsOpen {v : ℝ × ℝ × ℝ | e0TACone (v₀ - v)} :=
  e0TA_isOpen_cone.preimage (continuous_const.sub continuous_id)

theorem e0TA_isOpen_future (v₀ : ℝ × ℝ × ℝ) : IsOpen {v : ℝ × ℝ × ℝ | e0TACone (v - v₀)} :=
  e0TA_isOpen_cone.preimage (continuous_id.sub continuous_const)

/-- **Straight timelike segments are chronological**: for a chart map `ι` of `Ω ⊆ ℝ³` (null
coordinates) and a causality `C` of `Y`, two points of a convex open `V ⊆ Ω` with `ι(V) ⊆ O` whose
developments are chronologically related in `𝐌³` are chronologically related in `O`. The only
property of `C` the convergence form of `typeAgreement` uses. -/
def E0TASegLt (C : Causal.Causality E0Y) (ι : ℝ × ℝ × ℝ → E0Y) (Ω : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∀ (O : Opens E0Y) (V : Set (ℝ × ℝ × ℝ)), IsOpen V → Convex ℝ V → V ⊆ Ω →
    (∀ v ∈ V, ι v ∈ O) → ∀ v ∈ V, ∀ w ∈ V,
      (Causal.minkowski 2).lt ⊤ (nullToMink v) (nullToMink w) → C.lt O (ι v) (ι w)

/-- **The cone region in the diamond.** For a chart map `ι` of a neighbourhood `Ω` of the tip `v₀`
(null coordinates) whose straight timelike segments are chronological in `C` (`E0TASegLt`), the
diamond of the field contains, near its tip, `K = B(v₀, ε) ∩ I^∓(v₀)` read through `ι`. -/
theorem e0TA_exists_cone (C : Causal.Causality E0Y) {ι : ℝ × ℝ × ℝ → E0Y}
    {Ω : Set (ℝ × ℝ × ℝ)} (hΩ : IsOpen Ω) (hιc : ContinuousOn ι Ω) (hlt : E0TASegLt C ι Ω)
    {v₀ : ℝ × ℝ × ℝ} (hv₀ : v₀ ∈ Ω) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {U : Set E0Y} {O : Opens E0Y} (hyO : ι v₀ ∈ O) {r : E0Y}
    (hdia : (C.lt O r (ι v₀) ∧ C.Iplus O {r} ∩ C.Iminus O {ι v₀} ⊆ U) ∨
      (C.lt O (ι v₀) r ∧ C.Iplus O {ι v₀} ∩ C.Iminus O {r} ⊆ U)) :
    ∃ K : Set (ℝ × ℝ × ℝ), IsOpen K ∧ Convex ℝ K ∧ K.Nonempty ∧ (𝓝[K] v₀).NeBot ∧ K ⊆ Ω ∧
      K ⊆ Metric.ball v₀ ε₀ ∧ ((∀ v ∈ K, e0TACone (v₀ - v)) ∨
        (∃ ε > 0, ∀ v, dist v v₀ < ε → e0TACone (v - v₀) → v ∈ K)) ∧ ∀ v ∈ K, ι v ∈ U := by
  rcases hdia with ⟨hlt₀, hsub⟩ | ⟨hlt₀, hsub⟩
  · -- past diamond `I⁺_O(r) ∩ I⁻_O(y₀)`: the past cone at the tip
    obtain ⟨ε, hε, hεε, hB⟩ := e0TA_exists_ball hΩ hιc hv₀ hε₀ (W := C.Iplus O {r})
      C.isOpen_Iplus hyO (Causal.Precausality.mem_Iplus_singleton.2 hlt₀)
    obtain ⟨hKo, hKc, hKne, hNe⟩ := e0TA_cone_facts v₀ hε (e0TA_isOpen_past v₀)
      (e0TA_convex_past v₀) (-((1, 1, 0) : ℝ × ℝ × ℝ)) fun s hs => by
        show e0TACone (v₀ - (v₀ + s • -((1, 1, 0) : ℝ × ℝ × ℝ)))
        rw [smul_neg, ← sub_eq_add_neg, sub_sub_cancel]; exact e0TA_cone_e.smul hs
    have hlt' := hlt O (Metric.ball v₀ ε) Metric.isOpen_ball (convex_ball _ _)
      (fun v hv => (hB v hv).1) (fun v hv => (hB v hv).2.1)
    refine ⟨_, hKo, hKc, hKne, hNe, fun v hv => (hB v hv.1).1,
      fun v hv => Metric.ball_subset_ball hεε hv.1, Or.inl fun v hv => hv.2, fun v hv => ?_⟩
    exact hsub ⟨(hB v hv.1).2.2, Causal.Precausality.mem_Iminus_singleton.2
      (hlt' v hv.1 v₀ (Metric.mem_ball_self hε) ((e0TA_minkowski_lt_iff _ _).2 hv.2))⟩
  · -- future diamond `I⁺_O(y₀) ∩ I⁻_O(r)`: the future cone at the tip
    obtain ⟨ε, hε, hεε, hB⟩ := e0TA_exists_ball hΩ hιc hv₀ hε₀ (W := C.Iminus O {r})
      C.isOpen_Iminus hyO (Causal.Precausality.mem_Iminus_singleton.2 hlt₀)
    obtain ⟨hKo, hKc, hKne, hNe⟩ := e0TA_cone_facts v₀ hε (e0TA_isOpen_future v₀)
      (e0TA_convex_future v₀) ((1, 1, 0) : ℝ × ℝ × ℝ) fun s hs => by
        show e0TACone (v₀ + s • ((1, 1, 0) : ℝ × ℝ × ℝ) - v₀)
        rw [add_sub_cancel_left]; exact e0TA_cone_e.smul hs
    have hlt' := hlt O (Metric.ball v₀ ε) Metric.isOpen_ball (convex_ball _ _)
      (fun v hv => (hB v hv).1) (fun v hv => (hB v hv).2.1)
    refine ⟨_, hKo, hKc, hKne, hNe, fun v hv => (hB v hv.1).1,
      fun v hv => Metric.ball_subset_ball hεε hv.1,
      Or.inr ⟨ε, hε, fun v hd hc => ⟨hd, hc⟩⟩, fun v hv => ?_⟩
    exact hsub ⟨Causal.Precausality.mem_Iplus_singleton.2
      (hlt' v₀ (Metric.mem_ball_self hε) v hv.1 ((e0TA_minkowski_lt_iff _ _).2 hv.2)),
      (hB v hv.1).2.2⟩

/-- **`z₀` is regular**, for a chart map `ι` of a neighbourhood `Ω` of the tip `v₀` (null
coordinates) whose straight timelike segments in convex sets are chronological in `C`. The
diamond contains a cone region at the tip (`e0TA_exists_cone`), along which `e0TA_absurd` refutes
a BTZ limit. -/
theorem e0TA_reg_of_chart (C : Causal.Causality E0Y) {ι : ℝ × ℝ × ℝ → E0Y}
    {Ω : Set (ℝ × ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hιc : ContinuousOn ι Ω) (hιreg : ∀ v ∈ Ω, ι v ∈ e0Reg)
    (hchart : ∀ v ∈ Ω, ∃ c ∈ e0Atlas, ι v ∈ c.source ∧ ∃ g₁ : Causal.Flat.isom 2,
      ∀ᶠ v' in 𝓝 v, c (ι v') = g₁ • nullToMink v')
    (hlt : E0TASegLt C ι Ω)
    {v₀ : ℝ × ℝ × ℝ} (hv₀ : v₀ ∈ Ω) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hinj : InjOn ι (Metric.ball v₀ ε₀))
    {U : Set E0Y} (hU : IsOpen U) {O : Opens E0Y} (hyO : ι v₀ ∈ O) {r : E0Y}
    (hdia : (C.lt O r (ι v₀) ∧ C.Iplus O {r} ∩ C.Iminus O {ι v₀} ⊆ U) ∨
      (C.lt O (ι v₀) r ∧ C.Iplus O {ι v₀} ∩ C.Iminus O {r} ⊆ U))
    {z₀ : E0Y} {f : E0Y → E0Y} (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y)
    (hfinj : InjOn f U) (hT : Tendsto f (𝓝[U] (ι v₀)) (𝓝 z₀)) : z₀ ∈ e0Reg := by
  by_contra hz
  obtain ⟨K, hKo, hKc, hKne, hNe, hKΩ, hKb, hcone, hιU⟩ :=
    e0TA_exists_cone C hΩ hιc hlt hv₀ hε₀ hyO hdia
  exact e0TA_absurd hΩ hιc hιreg hchart hv₀ hinj hKo hKc hKne hNe hKΩ hKb hcone hU hιU hf
    hfinj hT hz

/-! #### The two chart maps of a regular tip -/

/-- The chart map at a point of `𝕄`: `v ↦ inl (nullToMink v)`. -/
noncomputable def e0TAInl (v : ℝ × ℝ × ℝ) : E0Y := Sum.inl (nullToMink v)

/-- The chart map at a regular point of `𝔼₀`: `v ↦ inr [D⁻¹ v]` on `{b > 0}`. -/
noncomputable def e0TAInr (v : ℝ × ℝ × ℝ) : E0Y :=
  Sum.inr (orbitMk (GammaA (2 * π)) (btzDevInv v))

theorem e0TAInl_chart (v : ℝ × ℝ × ℝ) : ∃ c ∈ e0Atlas, e0TAInl v ∈ c.source ∧
    ∃ g₁ : Causal.Flat.isom 2, ∀ᶠ v' in 𝓝 v, c (e0TAInl v') = g₁ • nullToMink v' :=
  ⟨e0Inl.symm, e0Inl_symm_mem_e0Atlas, by rw [e0Inl_symm_source]; exact ⟨_, rfl⟩, 1,
    Eventually.of_forall fun v' => by simp [e0TAInl]⟩

theorem e0TA_isOpen_b : IsOpen {v : ℝ × ℝ × ℝ | 0 < v.2.1} :=
  isOpen_lt continuous_const (continuous_fst.comp continuous_snd)

theorem e0TAInr_continuousOn : ContinuousOn e0TAInr {v : ℝ × ℝ × ℝ | 0 < v.2.1} :=
  continuous_inr.comp_continuousOn (continuous_quot_mk.comp_continuousOn continuousOn_btzDevInv)

theorem e0TAInr_reg {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) : e0TAInr v ∈ e0Reg := by
  rw [e0TAInr, inr_mem_e0Reg_iff, btzE0_reg_eq]
  exact ⟨_, e0TA_btzDevInv_mem hv, rfl⟩

theorem e0TAInr_chart {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) : ∃ c ∈ e0Atlas, e0TAInr v ∈ c.source ∧
    ∃ g₁ : Causal.Flat.isom 2, ∀ᶠ v' in 𝓝 v, c (e0TAInr v') = g₁ • nullToMink v' := by
  have hy := e0TA_btzDevInv_mem hv
  have hx : orbitMk (GammaA (2 * π)) (btzDevInv v) ∈
      Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rw [btzE0_reg_eq]; exact ⟨_, hy, rfl⟩
  obtain ⟨c₀, hc₀, hxc₀⟩ := mem_support.1 hx
  obtain ⟨g, hg⟩ := btz_eventually_chart btzV0_pos isBTZStructure_btzE0 hy hc₀ hxc₀
  refine ⟨_, e0InrChart_mem_e0Atlas hc₀, mem_e0InrChart_source.2 ⟨_, hxc₀, rfl⟩, g⁻¹, ?_⟩
  have hci : ContinuousAt btzDevInv v := continuousOn_btzDevInv.continuousAt (e0TA_isOpen_b.mem_nhds hv)
  filter_upwards [hci.eventually hg, e0TA_isOpen_b.mem_nhds hv] with v' h1 h2
  rw [btzDevM, btzDev_btzDevInv (Or.inl h2)] at h1
  rw [e0TAInr, e0InrChart_inr, h1, inv_smul_smul]

/-- `ι = inr ∘ [·] ∘ D⁻¹` is injective on the ball of radius `b(v₀)/2`: two points with one
image differ by `Pᵏ`, which moves the `c`-coordinate by `2πk·b`. -/
theorem e0TAInr_injOn {v₀ : ℝ × ℝ × ℝ} (hv₀ : 0 < v₀.2.1) :
    InjOn e0TAInr (Metric.ball v₀ (v₀.2.1 / 2)) := by
  have hb : ∀ u ∈ Metric.ball v₀ (v₀.2.1 / 2), v₀.2.1 / 2 < u.2.1 ∧
      |u.2.2 - v₀.2.2| < v₀.2.1 / 2 := fun u hu => by
    have hd := Metric.mem_ball.1 hu
    have hd2 : dist u.2 v₀.2 ≤ dist u v₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hd21 : dist u.2.1 v₀.2.1 ≤ dist u.2 v₀.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd22 : dist u.2.2 v₀.2.2 ≤ dist u.2 v₀.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
    rw [Real.dist_eq] at hd21 hd22
    have h1 : |u.2.1 - v₀.2.1| < v₀.2.1 / 2 := by linarith
    exact ⟨by linarith [abs_lt.1 h1], by linarith⟩
  have hpos : ∀ u ∈ Metric.ball v₀ (v₀.2.1 / 2), 0 < u.2.1 := fun u hu => by
    linarith [(hb u hu).1]
  intro v hv w hw h
  have h' : orbitMk (GammaA (2 * π)) (btzDevInv v) = orbitMk (GammaA (2 * π)) (btzDevInv w) :=
    Sum.inr_injective h
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_orbitMk_eq h'
  have hw' : w = parab (γ.toInt * (2 * π)) v := by
    rw [← btzDev_btzDevInv (Or.inl (hpos w hw)), ← hγ, btzDev_smul_all,
      btzDev_btzDevInv (Or.inl (hpos v hv))]
    exact btzParab_zpow_smul _ _
  have hk : γ.toInt = 0 := by
    by_contra hk
    have hc : w.2.2 - v.2.2 = γ.toInt * (2 * π) * v.2.1 := by rw [hw', parab_apply]; ring
    have h1 : (1 : ℝ) ≤ |(γ.toInt : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have h2 : |w.2.2 - v.2.2| < v₀.2.1 := by
      have := (hb w hw).2; have := (hb v hv).2
      rw [abs_lt] at *; constructor <;> linarith
    have h3 : |w.2.2 - v.2.2| = |(γ.toInt : ℝ)| * (2 * π) * v.2.1 := by
      rw [hc, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
        abs_of_pos (hpos v hv)]
    have hπ : (3 : ℝ) < π := Real.pi_gt_three
    have h4 := (hb v hv).1
    have h5 : 1 * (2 * π * v.2.1) ≤ |(γ.toInt : ℝ)| * (2 * π * v.2.1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity [hpos v hv])
    have h6 : 0 < v.2.1 * (π - 3) := mul_pos (hpos v hv) (by linarith)
    nlinarith
  rw [hw', hk, Int.cast_zero, zero_mul, parab_zero]

/-! #### Assembly -/

/-- **`typeAgreement` for `𝕄 ⊕ 𝔼₀`, convergence form** (the field with `MapClusterPt z₀ (𝓝[U] y₀) f`
strengthened to `Tendsto f (𝓝[U] y₀) (𝓝 z₀)`), for every causality `C` of `Y` in which straight
timelike segments of the two chart maps are chronological (`E0TASegLt`; for the model causality
`GX.E0.causalityYBTZ` both are a segment argument, `campaign/WP-41c/TypeAgreementD.lean`): a limit
at a regular tip of an injective local `G`-structomorphism is regular. -/
theorem e0_typeAgreementTendsto_of (C : Causal.Causality E0Y) (hinl : E0TASegLt C e0TAInl univ)
    (hinr : E0TASegLt C e0TAInr {v | 0 < v.2.1}) : E0TypeAgreementTendsto C := by
  intro U hU _ y₀ hy₀ hdia z₀ f hf hinj hT
  have hy₀r : y₀ ∈ e0Reg := by by_contra h; exact hy₀ ⟨rfl, h⟩
  have hz₀r : z₀ ∈ e0Reg := by
    obtain ⟨O, hyO, r, -, hd⟩ := hdia
    rcases y₀ with m | x
    · have hι : e0TAInl (nullToMink.symm m) = Sum.inl m := by
        simp [e0TAInl]
      rw [← hι] at hyO hd hT
      exact e0TA_reg_of_chart C isOpen_univ (continuous_inl.comp
        nullToMinkHomeomorph.continuous).continuousOn (fun v _ => inl_mem_e0Reg _)
        (fun v _ => e0TAInl_chart v) hinl
        (mem_univ _) one_pos (fun a _ b _ h => nullToMink.injective (Sum.inl_injective h))
        hU hyO hd hf hinj hT
    · obtain ⟨yt, hyt, rfl⟩ : x ∈ orbitMk (GammaA (2 * π)) '' cylPos ℝ := by
        rw [← btzE0_reg_eq]; exact inr_mem_e0Reg_iff.1 hy₀r
      set v₀ := btzDev 0 btzV0 yt
      have hb₀ : 0 < v₀.2.1 := by rw [btzDev_e0_b]; exact hyt
      have hι : e0TAInr v₀ = Sum.inr (orbitMk (GammaA (2 * π)) yt) := by
        rw [e0TAInr, btzDevInv_btzDev]
      rw [← hι] at hyO hd hT
      exact e0TA_reg_of_chart C e0TA_isOpen_b e0TAInr_continuousOn (fun v hv => e0TAInr_reg hv)
        (fun v hv => e0TAInr_chart hv) hinr hb₀ (half_pos hb₀) (e0TAInr_injOn hb₀) hU hyO hd hf
        hinj hT
  refine ⟨fun α _ => ?_, fun ⟨α, _, h⟩ => absurd h.2 (not_not.2 hy₀r)⟩
  simp only [e0SingY, mem_setOf_eq, not_not.2 hy₀r, not_not.2 hz₀r, and_false]


/-! #### The original field at the tips in `𝕄` (no domain holonomy) -/

/-- The developed image under `g`, in null coordinates: `Φ_g v = nullToMink⁻¹ (g · nullToMink v)`. -/
noncomputable def e0TAPhi (g : Causal.Flat.isom 2) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  nullToMink.symm (g • nullToMink v)

theorem continuous_e0TAPhi (g : Causal.Flat.isom 2) : Continuous (e0TAPhi g) :=
  nullToMinkHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp nullToMinkHomeomorph.continuous)

theorem nullToMink_e0TAPhi (g : Causal.Flat.isom 2) (v : ℝ × ℝ × ℝ) :
    nullToMink (e0TAPhi g v) = g • nullToMink v := LinearEquiv.apply_symm_apply _ _

/-- `Φ_{Pᵏ g} = parab (2πk) ∘ Φ_g`. -/
theorem e0TAPhi_zpow_mul (k : ℤ) (g : Causal.Flat.isom 2) (v : ℝ × ℝ × ℝ) :
    e0TAPhi (btzHol 0 (2 * π) ^ k * g) v = parab (k * (2 * π)) (e0TAPhi g v) := by
  apply nullToMink.injective
  rw [nullToMink_e0TAPhi, mul_smul, ← nullToMink_e0TAPhi g v, btzHol_zpow_smul,
    ← btzParab_zpow_smul]

/-- The chart map `[D⁻¹ ·]` is invariant under the holonomy. -/
theorem e0TAInr_parab {w : ℝ × ℝ × ℝ} (hw : 0 < w.2.1) (k : ℤ) :
    e0TAInr (parab (k * (2 * π)) w) = e0TAInr w := by
  have hb' : 0 < (parab (k * (2 * π)) w).2.1 := by simpa [parab_apply] using hw
  have h : btzDevInv (parab (k * (2 * π)) w) =
      (GammaA.ofInt k : GammaA (2 * π)) • btzDevInv w := by
    apply btzDev_injective 0 btzV0_pos
    rw [btzDev_btzDevInv (Or.inl hb'), btzDev_smul_all, GammaA.toInt_ofInt,
      btzDev_btzDevInv (Or.inl hw)]
    exact (btzParab_zpow_smul k w).symm
  rw [e0TAInr, e0TAInr, h, orbitMk_smul]

/-- **A local representation** of `f` near a point of `𝕄` sent into `𝔼₀`: `f ∘ inl ∘ nullToMink`
is `[D⁻¹ Φ_g]` on a neighbourhood (lift and Liouville on a ball, `e0TA_lift`). -/
theorem e0TA_local_rep_inl {U : Set E0Y} (hU : IsOpen U) {f : E0Y → E0Y}
    (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y)
    (hfr : ∀ y ∈ U, f y ∈ range Sum.inr) {v : ℝ × ℝ × ℝ} (hv : e0TAInl v ∈ U) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ v' in 𝓝 v,
      0 < (e0TAPhi g v').2.1 ∧ f (e0TAInl v') = e0TAInr (e0TAPhi g v') := by
  have hιc : Continuous e0TAInl := continuous_inl.comp nullToMinkHomeomorph.continuous
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hιc) v hv
  obtain ⟨L, g, hL⟩ := e0TA_lift Metric.isOpen_ball (convex_ball v δ) ⟨v, Metric.mem_ball_self hδ⟩
    hιc.continuousOn (fun v' _ => e0TAInl_chart v') hU (fun v' hv' => hball hv')
    (fun v' _ => inl_mem_e0Reg _) hf (fun v' hv' => hfr _ (hball hv'))
  refine ⟨g, Filter.eventually_of_mem (Metric.ball_mem_nhds v hδ) fun v' hv' => ?_⟩
  obtain ⟨hP, hq, hD⟩ := hL v' hv'
  have hdev : btzDev 0 btzV0 (L v') = e0TAPhi g v' := by
    apply nullToMink.injective; rw [nullToMink_e0TAPhi]; exact hD
  refine ⟨by rw [← hdev, btzDev_e0_b]; exact hP, ?_⟩
  rw [hq, e0TAInr, ← hdev, btzDevInv_btzDev]

/-- **Two representations on a preconnected open set differ by the holonomy**: if `[D⁻¹ Φ_g]` and
`[D⁻¹ Φ_{g'}]` agree on `W`, then `g' = Pᵏ g` (the integer `k = (c' − c)/(2πb)` is continuous on
`W`, hence constant; rigidity of `Isom(𝐌³)`). -/
theorem e0TA_rep_unique {W : Set (ℝ × ℝ × ℝ)} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hWne : W.Nonempty) {g g' : Causal.Flat.isom 2}
    (hb : ∀ v ∈ W, 0 < (e0TAPhi g v).2.1)
    (heq : ∀ v ∈ W, e0TAInr (e0TAPhi g v) = e0TAInr (e0TAPhi g' v)) :
    ∃ k : ℤ, g' = btzHol 0 (2 * π) ^ k * g := by
  -- pointwise: `Φ_{g'} v = parab (2πk(v)) (Φ_g v)`
  have hpt : ∀ v ∈ W, ∃ k : ℤ, e0TAPhi g' v = parab (k * (2 * π)) (e0TAPhi g v) := by
    intro v hv
    have h' := Sum.inr_injective (heq v hv)
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_orbitMk_eq h'
    have hb' : 0 < (e0TAPhi g' v).2.1 := by
      by_contra hn
      have hr : (btzDevInv (e0TAPhi g' v)).1.r = (e0TAPhi g v).2.1 := by
        rw [← hγ, gammaA_smul_r, ← btzDev_e0_b, btzDev_btzDevInv (Or.inl (hb v hv))]
      have h0 : (btzDevInv (e0TAPhi g' v)).1.r = 0 := by
        rw [btzDevInv, dif_neg hn]; exact DInfty.apex_r
      linarith [hb v hv]
    refine ⟨γ.toInt, ?_⟩
    rw [← btzDev_btzDevInv (Or.inl hb'), ← hγ, btzDev_smul_all,
      btzDev_btzDevInv (Or.inl (hb v hv))]
    exact btzParab_zpow_smul _ _
  -- the integer is a continuous function of `v`
  set κ : ℝ × ℝ × ℝ → ℝ := fun v =>
    ((e0TAPhi g' v).2.2 - (e0TAPhi g v).2.2) / ((2 * π) * (e0TAPhi g v).2.1) with hκdef
  have hκ : ∀ v ∈ W, ∀ k : ℤ, e0TAPhi g' v = parab (k * (2 * π)) (e0TAPhi g v) → κ v = k := by
    intro v hv k hk
    simp only [hκdef, hk, parab_apply]
    have : (2 * π) * (e0TAPhi g v).2.1 ≠ 0 := by have := hb v hv; positivity
    rw [div_eq_iff this]
    ring
  have hκc : ContinuousOn κ W := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_
    · exact (continuous_snd.comp (continuous_snd.comp (continuous_e0TAPhi g'))).sub
        (continuous_snd.comp (continuous_snd.comp (continuous_e0TAPhi g)))
    · exact continuous_const.mul (continuous_fst.comp (continuous_snd.comp (continuous_e0TAPhi g)))
    · intro v hv; have := hb v hv; positivity
  obtain ⟨v₁, hv₁⟩ := hWne
  obtain ⟨k₁, hk₁⟩ := hpt v₁ hv₁
  have hall : ∀ v ∈ W, e0TAPhi g' v = parab (k₁ * (2 * π)) (e0TAPhi g v) := by
    intro v hv
    obtain ⟨k, hk⟩ := hpt v hv
    suffices hkk : k = k₁ by rw [← hkk]; exact hk
    by_contra hne
    -- an intermediate value of `κ` between `k₁` and `k` is a half-integer
    have hκ₁ := hκ v₁ hv₁ k₁ hk₁
    have hκv := hκ v hv k hk
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hmem : ((k : ℝ) + 1 / 2) ∈ Icc (κ v) (κ v₁) := by
        rw [hκv, hκ₁]
        have : (k : ℝ) + 1 ≤ k₁ := by exact_mod_cast hlt
        constructor <;> linarith
      obtain ⟨w, hw, hκw⟩ := hWc.intermediate_value hv hv₁ hκc hmem
      obtain ⟨j, hj⟩ := hpt w hw
      rw [hκ w hw j hj] at hκw
      have h1 : (k : ℝ) < j := by linarith
      have h2 : (j : ℝ) < k + 1 := by linarith
      have h1' : k < j := by exact_mod_cast h1
      have h2' : j < k + 1 := by exact_mod_cast h2
      omega
    · have hmem : ((k₁ : ℝ) + 1 / 2) ∈ Icc (κ v₁) (κ v) := by
        rw [hκv, hκ₁]
        have : (k₁ : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        constructor <;> linarith
      obtain ⟨w, hw, hκw⟩ := hWc.intermediate_value hv₁ hv hκc hmem
      obtain ⟨j, hj⟩ := hpt w hw
      rw [hκ w hw j hj] at hκw
      have h1 : (k₁ : ℝ) < j := by linarith
      have h2 : (j : ℝ) < k₁ + 1 := by linarith
      have h1' : k₁ < j := by exact_mod_cast h1
      have h2' : j < k₁ + 1 := by exact_mod_cast h2
      omega
  -- rigidity of `Isom(𝐌³)` on the open set `nullToMink '' W`
  refine ⟨k₁, ?_⟩
  have hopen : IsOpen (nullToMink '' W) := by
    rw [← coe_nullToMinkHomeomorph]; exact nullToMinkHomeomorph.isOpenMap W hWo
  have hrig := IsRigidAction.smul_eq_of_eqOn (G := Causal.Flat.isom 2) hopen ⟨_, v₁, hv₁, rfl⟩
    (g := g') (h := btzHol 0 (2 * π) ^ k₁ * g) (by
      rintro _ ⟨v, hv, rfl⟩
      show g' • nullToMink v = (btzHol 0 (2 * π) ^ k₁ * g) • nullToMink v
      rw [← nullToMink_e0TAPhi, ← nullToMink_e0TAPhi, hall v hv, e0TAPhi_zpow_mul])
  exact Subtype.ext (AffineEquiv.ext fun z => hrig z)


/-- **The global representation** on a preconnected open `U ⊆ 𝕄` sent into `𝔼₀`: one `g` with
`f ∘ inl ∘ nullToMink = [D⁻¹ Φ_g]` on all of `U` (the class of the local `g` modulo `⟨P⟩` is
locally constant, `e0TA_rep_unique`, and `[D⁻¹ ·]` is `P`-invariant, `e0TAInr_parab`). -/
theorem e0TA_global_rep_inl {U : Set E0Y} (hU : IsOpen U) {f : E0Y → E0Y}
    (hf : ∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y)
    (hfr : ∀ y ∈ U, f y ∈ range Sum.inr) (hUc : IsPreconnected {v | e0TAInl v ∈ U})
    {v₁ : ℝ × ℝ × ℝ} (hv₁ : e0TAInl v₁ ∈ U) :
    ∃ g : Causal.Flat.isom 2, ∀ v, e0TAInl v ∈ U →
      0 < (e0TAPhi g v).2.1 ∧ f (e0TAInl v) = e0TAInr (e0TAPhi g v) := by
  set P : Causal.Flat.isom 2 := btzHol 0 (2 * π)
  obtain ⟨g₀, hg₀⟩ := e0TA_local_rep_inl hU hf hfr hv₁
  set Rep : Causal.Flat.isom 2 → ℝ × ℝ × ℝ → Prop := fun g v => ∀ᶠ v' in 𝓝 v,
    0 < (e0TAPhi g v').2.1 ∧ f (e0TAInl v') = e0TAInr (e0TAPhi g v') with hRep
  set u : Set (ℝ × ℝ × ℝ) := {v | ∃ k : ℤ, Rep (P ^ k * g₀) v} with hudef
  have hu : IsOpen u := by
    have : u = ⋃ k : ℤ, {v | Rep (P ^ k * g₀) v} := by ext v; simp [hudef]
    rw [this]; exact isOpen_iUnion fun k => isOpen_setOf_eventually_nhds
  have hsub : {v | e0TAInl v ∈ U} ⊆ u := by
    refine hUc.subset_of_closure_inter_subset hu ⟨v₁, hv₁, 0, by simpa [hRep] using hg₀⟩ ?_
    rintro v ⟨hvcl, hvU⟩
    obtain ⟨g, hg⟩ := e0TA_local_rep_inl hU hf hfr hvU
    obtain ⟨δ, hδ, hδg⟩ := Metric.eventually_nhds_iff.1 hg
    obtain ⟨v', hv'B, k, hk⟩ := mem_closure_iff_nhds.1 hvcl _ (Metric.ball_mem_nhds v hδ)
    obtain ⟨δ', hδ', hδk⟩ := Metric.eventually_nhds_iff.1 hk
    have hd : dist v' v < δ := hv'B
    set ρ := min δ' (δ - dist v' v)
    have hρ : 0 < ρ := lt_min hδ' (by linarith)
    have hW : ∀ w ∈ Metric.ball v' ρ, dist w v < δ ∧ dist w v' < δ' := fun w hw => by
      have hw' : dist w v' < ρ := hw
      refine ⟨?_, hw'.trans_le (min_le_left _ _)⟩
      calc dist w v ≤ dist w v' + dist v' v := dist_triangle _ _ _
        _ < (δ - dist v' v) + dist v' v := by
          have := hw'.trans_le (min_le_right _ _); linarith
        _ = δ := by ring
    obtain ⟨m, hm⟩ := e0TA_rep_unique (g := P ^ k * g₀) (g' := g) Metric.isOpen_ball
      (convex_ball v' ρ).isPreconnected ⟨v', Metric.mem_ball_self hρ⟩
      (fun w hw => (hδk (hW w hw).2).1)
      (fun w hw => (hδk (hW w hw).2).2.symm.trans (hδg (hW w hw).1).2)
    refine ⟨m + k, ?_⟩
    have : P ^ (m + k) * g₀ = g := by rw [hm, zpow_add, mul_assoc]
    rw [this]; exact hg
  refine ⟨g₀, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := hsub hv
  obtain ⟨h1, h2⟩ := hk.self_of_nhds
  rw [e0TAPhi_zpow_mul] at h1 h2
  have hb : 0 < (e0TAPhi g₀ v).2.1 := by simpa [parab_apply] using h1
  exact ⟨hb, by rw [h2, e0TAInr_parab hb]⟩

/-- **`typeAgreement` at the tips in `𝕄`**: the field's statement verbatim, `y₀ = inl m`. -/
def E0TypeAgreementInl (C : Causal.Causality E0Y) : Prop :=
    ∀ U : Set E0Y, IsOpen U → IsConnected U → ∀ m : Causal.Minkowski 2,
    (∃ O : Opens E0Y, (Sum.inl m : E0Y) ∈ O ∧ ∃ r ∈ O,
      (C.lt O r (Sum.inl m) ∧ C.Iplus O {r} ∩ C.Iminus O {Sum.inl m} ⊆ U) ∨
      (C.lt O (Sum.inl m) r ∧ C.Iplus O {Sum.inl m} ∩ C.Iminus O {r} ⊆ U)) →
    ∀ z₀ : E0Y, ∀ f : E0Y → E0Y, (∀ y ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U y) →
    InjOn f U → MapClusterPt z₀ (𝓝[U] (Sum.inl m)) f →
    (∀ α : ℝ, 0 ≤ α → ((Sum.inl m : E0Y) ∈ e0SingY α ↔ z₀ ∈ e0SingY α)) ∧
      ((∃ α : ℝ, 0 ≤ α ∧ (Sum.inl m : E0Y) ∈ e0SingY α) →
        z₀ ∈ connectedComponent (Sum.inl m : E0Y))

/-- `E0TypeAgreementInl` is the restriction of the verbatim field to the tips in `𝕄`. -/
theorem E0TypeAgreement.inl {C : Causal.Causality E0Y} (h : E0TypeAgreement C) :
    E0TypeAgreementInl C := fun U hU hUc m hdia z₀ f hf hinj hcl =>
  h U hU hUc (Sum.inl m) (fun h0 => h0.2 (inl_mem_e0Reg m)) hdia z₀ f hf hinj hcl

/-- **`typeAgreement` verbatim at the tips in `𝕄`** (the field's own statement, `MapClusterPt`, for
`y₀ = inl m`), for every causality `C` whose straight timelike segments of `𝕄` are chronological:
`U ⊆ 𝕄` carries no holonomy, so `f` has one global development (`e0TA_global_rep_inl`), and a BTZ
cluster value puts the tip's image on `ℝu` (`e0TA_tip` along an ultrafilter), against the cone in
the diamond (`e0TA_absurd_rep`). -/
theorem e0_typeAgreement_inl_of (C : Causal.Causality E0Y) (hinl : E0TASegLt C e0TAInl univ) :
    E0TypeAgreementInl C := by
  intro U hU hUc m hdia z₀ f hf hinj hcl
  have hιc : Continuous e0TAInl := continuous_inl.comp nullToMinkHomeomorph.continuous
  have hz : z₀ ∈ e0Reg := by
    by_contra hz
    obtain ⟨x₁, rfl, hx₁⟩ : ∃ x₁ : BTZE0, z₀ = Sum.inr x₁ ∧
        x₁ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
      rcases z₀ with m' | x
      · exact absurd (inl_mem_e0Reg m') hz
      · exact ⟨x, rfl, fun h => hz (inr_mem_e0Reg_iff.2 h)⟩
    obtain ⟨O, hyO, r, -, hd⟩ := hdia
    set v₀ := nullToMink.symm m
    have hι : e0TAInl v₀ = Sum.inl m := by simp [e0TAInl, v₀]
    rw [← hι] at hyO hd hcl
    obtain ⟨K, -, -, hKne, -, -, hKb, hcone, hιU⟩ :=
      e0TA_exists_cone C isOpen_univ hιc.continuousOn hinl (mem_univ v₀) one_pos hyO hd
    obtain ⟨w₁, hw₁⟩ := hKne
    -- `U ⊆ 𝕄`, and `f(U) ⊆ 𝔼₀`
    have hUl : U ⊆ range Sum.inl :=
      hUc.isPreconnected.subset_isClopen isClopen_range_inl ⟨_, hιU w₁ hw₁, nullToMink w₁, rfl⟩
    have hfc : ContinuousOn f U := fun y hy => (e0TA_continuousAt hU hf hy).continuousWithinAt
    have hcl' : Sum.inr x₁ ∈ closure (f '' U) :=
      hcl.clusterPt.mem_closure_of_mem _ (image_mem_map self_mem_nhdsWithin)
    obtain ⟨_, hy₁r, hy₁⟩ := mem_closure_iff.1 hcl' _ isOpen_range_inr ⟨x₁, rfl⟩
    have hfr' := (hUc.isPreconnected.image f hfc).subset_isClopen isClopen_range_inr
      ⟨_, hy₁, hy₁r⟩
    have hfr : ∀ y ∈ U, f y ∈ range Sum.inr := fun y hy => hfr' ⟨y, hy, rfl⟩
    -- the domain in null coordinates
    set U' : Set (ℝ × ℝ × ℝ) := {v | e0TAInl v ∈ U} with hU'def
    have hUim : U = e0TAInl '' U' := by
      ext y; constructor
      · intro hy
        obtain ⟨m', rfl⟩ := hUl hy
        exact ⟨nullToMink.symm m', by simpa [hU'def, e0TAInl] using hy, by simp [e0TAInl]⟩
      · rintro ⟨v, hv, rfl⟩; exact hv
    have hU'c : IsPreconnected U' := by
      have hcont : Continuous fun y : E0Y =>
          nullToMink.symm (Sum.elim id (fun _ => (0 : Causal.Minkowski 2)) y) :=
        nullToMinkHomeomorph.symm.continuous.comp (Continuous.sumElim continuous_id continuous_const)
      have : U' = (fun y : E0Y =>
          nullToMink.symm (Sum.elim id (fun _ => (0 : Causal.Minkowski 2)) y)) '' U := by
        rw [hUim, ← image_comp]
        ext v; simp [e0TAInl]
      rw [this]; exact hUc.isPreconnected.image _ hcont.continuousOn
    obtain ⟨g, hg⟩ := e0TA_global_rep_inl hU hf hfr hU'c (hιU w₁ hw₁)
    -- the cluster value along an ultrafilter at the tip
    have hemb : IsEmbedding e0TAInl := IsEmbedding.inl.comp nullToMinkHomeomorph.isEmbedding
    have hmap : 𝓝[U] (e0TAInl v₀) = map e0TAInl (𝓝[U'] v₀) := by
      rw [hemb.map_nhdsWithin_eq, ← hUim]
    rw [hmap] at hcl
    have hcl2 : MapClusterPt (Sum.inr x₁) (𝓝[U'] v₀) (f ∘ e0TAInl) := by
      show ClusterPt _ _
      rw [← Filter.map_map]; exact hcl
    obtain ⟨𝒰, h𝒰, hT⟩ := mapClusterPt_iff_ultrafilter.1 hcl2
    set L : ℝ × ℝ × ℝ → DInfty × ℝ := fun v => btzDevInv (e0TAPhi g v) with hLdef
    have hev : ∀ᶠ v in (𝒰 : Filter (ℝ × ℝ × ℝ)), v ∈ U' := h𝒰 self_mem_nhdsWithin
    have hLM : ∀ v ∈ U', btzDevM 0 btzV0 (L v) = g • nullToMink v := fun v hv => by
      rw [hLdef, btzDevM, btzDev_btzDevInv (Or.inl (hg v hv).1), nullToMink_e0TAPhi]
    have hTq : Tendsto (fun v => orbitMk (GammaA (2 * π)) (L v)) (𝒰 : Filter (ℝ × ℝ × ℝ))
        (𝓝 x₁) := by
      rw [(IsEmbedding.inr : IsEmbedding (Sum.inr : BTZE0 → E0Y)).tendsto_nhds_iff]
      refine hT.congr' (hev.mono fun v hv => ?_)
      exact (hg v hv).2
    obtain ⟨a, ha⟩ := e0TA_tip (F := (𝒰 : Filter (ℝ × ℝ × ℝ))) (h𝒰.trans nhdsWithin_le_nhds)
      (hev.mono hLM) hx₁ hTq
    exact e0TA_absurd_rep (ι := e0TAInl) (ε₀ := 1)
      (fun a _ b _ h => nullToMink.injective (Sum.inl_injective h)) ⟨w₁, hw₁⟩ hKb hcone hιU
      hinj (L := L) (g := g)
      (fun v hv => ⟨e0TA_btzDevInv_mem (hg v (hιU v hv)).1, (hg v (hιU v hv)).2,
        hLM v (hιU v hv)⟩) ha
  have hy₀r : (Sum.inl m : E0Y) ∈ e0Reg := inl_mem_e0Reg m
  refine ⟨fun α _ => ?_, fun ⟨α, _, h⟩ => absurd h.2 (not_not.2 hy₀r)⟩
  simp only [e0SingY, mem_setOf_eq, not_not.2 hy₀r, not_not.2 hz, and_false]

end TypeAgreementTendsto

/-! ### The counterexample to `typeAgreement` (DEC-27) -/

section Counterexample

open TopologicalSpace

/-! ### Data of the counterexample (null coordinates) -/

/-- The tip `v₀ = (0, 1, 0) = D(1, 0, 1)`. -/
def e0CEv : ℝ × ℝ × ℝ := (0, 1, 0)

/-- `P v₀ = (4π², 1, 2π)`. -/
noncomputable def e0CEp : ℝ × ℝ × ℝ := (4 * π ^ 2, 1, 2 * π)

/-- The base point `d = v₀ − (1/10)(1, 1, 0)` of the tube. -/
noncomputable def e0CEd : ℝ × ℝ × ℝ := (-(1 / 10), 9 / 10, 0)

/-- The axis of the tube, `c(s) = (1 − s) P v₀ + s d`. -/
noncomputable def e0CEc (s : ℝ) : ℝ × ℝ × ℝ := (1 - s) • e0CEp + s • e0CEd

/-- The past cone region at the tip. -/
def e0CEA : Set (ℝ × ℝ × ℝ) := {w | dist w e0CEv < 1 / 5 ∧ e0TACone (e0CEv - w)}

/-- The tube, from the cone region to `P v₀`. -/
noncomputable def e0CET : Set (ℝ × ℝ × ℝ) :=
  ⋃ s ∈ Ioo (0 : ℝ) 1, Metric.ball (e0CEc s) (s / 100)

/-- The domain, in null coordinates. -/
noncomputable def e0CEUt : Set (ℝ × ℝ × ℝ) := e0CEA ∪ e0CET

theorem e0CEc_apply (s : ℝ) :
    e0CEc s = ((1 - s) * (4 * π ^ 2) - s / 10, 1 - s / 10, (1 - s) * (2 * π)) := by
  simp only [e0CEc, e0CEp, e0CEd, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
  ext <;> simp <;> ring

/-- Coordinates of a point of a ball, in the sup metric. -/
theorem e0CE_abs_lt_of_dist {w z : ℝ × ℝ × ℝ} {r : ℝ} (h : dist w z < r) :
    |w.1 - z.1| < r ∧ |w.2.1 - z.2.1| < r ∧ |w.2.2 - z.2.2| < r := by
  have h1 : dist w.1 z.1 ≤ dist w z := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist w.2 z.2 ≤ dist w z := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h21 : dist w.2.1 z.2.1 ≤ dist w.2 z.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h22 : dist w.2.2 z.2.2 ≤ dist w.2 z.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [Real.dist_eq] at h1 h21 h22
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A point of the tube: `w = c(s) + x`, `s ∈ (0, 1)`, `|xᵢ| < s/100`. -/
theorem e0CET_mem {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CET) : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    |w.1 - ((1 - s) * (4 * π ^ 2) - s / 10)| < s / 100 ∧ |w.2.1 - (1 - s / 10)| < s / 100 ∧
    |w.2.2 - (1 - s) * (2 * π)| < s / 100 := by
  simp only [e0CET, mem_iUnion, Metric.mem_ball] at hw
  obtain ⟨s, ⟨hs0, hs1⟩, hd⟩ := hw
  have := e0CE_abs_lt_of_dist hd
  rw [e0CEc_apply] at this
  exact ⟨s, hs0, hs1, this⟩

theorem e0CEA_mem {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEA) :
    |w.1| < 1 / 5 ∧ |w.2.1 - 1| < 1 / 5 ∧ |w.2.2| < 1 / 5 ∧ w.1 < 0 := by
  obtain ⟨hd, hc⟩ := hw
  have := e0CE_abs_lt_of_dist hd
  simp only [e0CEv, sub_zero] at this
  obtain ⟨hb, hq⟩ := hc
  simp only [e0CEv, Prod.fst_sub, Prod.snd_sub] at hb hq
  refine ⟨this.1, this.2.1, this.2.2, ?_⟩
  nlinarith [sq_nonneg (0 - w.2.2)]

theorem e0CEUt_b_pos {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) : 0 < w.2.1 := by
  rcases hw with hA | hT
  · have := (e0CEA_mem hA).2.1; rw [abs_lt] at this; linarith
  · obtain ⟨s, hs0, hs1, -, hb, -⟩ := e0CET_mem hT
    rw [abs_lt] at hb; linarith

theorem isOpen_e0CEA : IsOpen e0CEA :=
  Metric.isOpen_ball.inter (e0TA_isOpen_past e0CEv)

theorem isOpen_e0CET : IsOpen e0CET :=
  isOpen_biUnion fun _ _ => Metric.isOpen_ball

theorem isOpen_e0CEUt : IsOpen e0CEUt := isOpen_e0CEA.union isOpen_e0CET

theorem continuous_e0CEc : Continuous e0CEc := by
  unfold e0CEc; fun_prop

theorem e0CEc_mem {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : e0CEc s ∈ e0CET :=
  mem_biUnion hs (Metric.mem_ball_self (by linarith [hs.1]))

theorem isPreconnected_e0CET : IsPreconnected e0CET := by
  refine isPreconnected_of_forall (e0CEc (1 / 2)) fun y hy => ?_
  simp only [e0CET, mem_iUnion] at hy
  obtain ⟨s, hs, hy⟩ := hy
  set I : Set ℝ := uIcc s (1 / 2)
  have hI : I ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    rcases (mem_uIcc.1 ht) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hs.1], by linarith⟩
    · exact ⟨by linarith, by linarith [hs.2]⟩
  refine ⟨Metric.ball (e0CEc s) (s / 100) ∪ e0CEc '' I, ?_, ?_, Or.inl hy, ?_⟩
  · refine union_subset (subset_biUnion_of_mem (u := fun s => Metric.ball (e0CEc s) (s / 100)) hs) ?_
    rintro _ ⟨t, ht, rfl⟩; exact e0CEc_mem (hI ht)
  · exact Or.inr ⟨1 / 2, right_mem_uIcc, rfl⟩
  · refine (convex_ball _ _).isPreconnected.union (e0CEc s)
      (Metric.mem_ball_self (by linarith [hs.1])) ⟨s, left_mem_uIcc, rfl⟩
      (isPreconnected_uIcc.image _ continuous_e0CEc.continuousOn)

/-- A point of both pieces: `c(999/1000)`. -/
theorem e0CEc_mem_A : e0CEc (999 / 1000) ∈ e0CEA := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hπsq : π ^ 2 < 10 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [Prod.dist_eq, Prod.dist_eq, e0CEc_apply]
    simp only [e0CEv, Real.dist_eq]
    refine max_lt ?_ (max_lt ?_ ?_)
    · rw [abs_lt]; constructor <;> nlinarith
    · rw [abs_lt]; constructor <;> norm_num
    · rw [abs_lt]; constructor <;> nlinarith
  · rw [e0CEc_apply]
    simp only [e0TACone, e0CEv, Prod.mk_sub_mk]
    constructor
    · norm_num
    · nlinarith

theorem isPreconnected_e0CEUt : IsPreconnected e0CEUt := by
  have hA : IsPreconnected e0CEA :=
    ((convex_ball e0CEv _).inter (e0TA_convex_past e0CEv)).isPreconnected
  exact hA.union (e0CEc (999 / 1000)) e0CEc_mem_A (e0CEc_mem ⟨by norm_num, by norm_num⟩)
    isPreconnected_e0CET

/-! ### Injectivity of `[D⁻¹ ·]` on the domain -/

/-- Two points of `{b > 0}` with one image under `[D⁻¹ ·]` differ by a power of `P`. -/
theorem e0TAInr_eq_parab {w w' : ℝ × ℝ × ℝ} (hw : 0 < w.2.1) (hw' : 0 < w'.2.1)
    (h : e0TAInr w = e0TAInr w') : ∃ k : ℤ, w' = parab (k * (2 * π)) w := by
  have h' : orbitMk (GammaA (2 * π)) (btzDevInv w) = orbitMk (GammaA (2 * π)) (btzDevInv w') :=
    Sum.inr_injective h
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_orbitMk_eq h'
  refine ⟨γ.toInt, ?_⟩
  rw [← btzDev_btzDevInv (Or.inl hw'), ← hγ, btzDev_smul_all, btzDev_btzDevInv (Or.inl hw)]
  exact btzParab_zpow_smul _ _

theorem nullQ_parab (φ : ℝ) (w : ℝ × ℝ × ℝ) : nullQ (parab φ w) = nullQ w := by
  simp only [nullQ, parab_apply]; ring

theorem parab_neg_parab (φ : ℝ) (w : ℝ × ℝ × ℝ) : parab (-φ) (parab φ w) = w := by
  simp only [parab_apply]; ext <;> simp; ring

theorem e0CE_noAA {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEA) {k : ℤ} (hk : k ≠ 0)
    (hw' : parab (k * (2 * π)) w ∈ e0CEA) : False := by
  have h1 := e0CEA_mem hw
  have h2 := e0CEA_mem hw'
  simp only [parab_apply] at h2
  have hπ := Real.pi_gt_three
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hb : 4 / 5 < w.2.1 := by have := h1.2.1; rw [abs_lt] at this; linarith
  have hc : |(k : ℝ) * (2 * π) * w.2.1| < 2 / 5 := by
    have e : (k : ℝ) * (2 * π) * w.2.1 = (w.2.2 + k * (2 * π) * w.2.1) - w.2.2 := by ring
    rw [e]; have := h2.2.2.1; have := h1.2.2.1
    rw [abs_lt] at *; constructor <;> linarith
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
    abs_of_pos (by linarith : (0 : ℝ) < w.2.1)] at hc
  have hpos : 0 < 2 * π * w.2.1 := by positivity
  have h3 := mul_le_mul_of_nonneg_right hk1 hpos.le
  have h4 : 2 * π * w.2.1 > 24 / 5 := by nlinarith
  rw [one_mul, ← mul_assoc] at h3
  linarith

theorem e0CE_noTT {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CET) {k : ℤ} (hk : k ≠ 0)
    (hw' : parab (k * (2 * π)) w ∈ e0CET) : False := by
  obtain ⟨s, hs0, hs1, -, hb, hc⟩ := e0CET_mem hw
  obtain ⟨s', hs0', hs1', -, hb', hc'⟩ := e0CET_mem hw'
  simp only [parab_apply] at hb' hc'
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  rw [abs_lt] at hb hc hb' hc'
  have hbpos : 89 / 100 < w.2.1 := by linarith
  -- `|s − s'| ≤ (s + s')/10`
  have hss : |s - s'| ≤ 1 / 5 := by rw [abs_le]; constructor <;> linarith
  have hcc : |(k : ℝ) * (2 * π) * w.2.1| < 2 := by
    have e : (k : ℝ) * (2 * π) * w.2.1 = (w.2.2 + k * (2 * π) * w.2.1) - w.2.2 := by ring
    rw [e, abs_lt]; rw [abs_le] at hss
    constructor <;> nlinarith
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
    abs_of_pos (by linarith : (0 : ℝ) < w.2.1)] at hcc
  have hpos : 0 < 2 * π * w.2.1 := by positivity
  have h3 := mul_le_mul_of_nonneg_right hk1 hpos.le
  have h4 : 2 * π * w.2.1 > 5 := by nlinarith
  rw [one_mul, ← mul_assoc] at h3
  linarith


theorem e0CE_pi_sq : 9 < π ^ 2 := by
  have hπ := Real.pi_gt_three
  calc (9 : ℝ) = 3 * 3 := by norm_num
    _ < π * π := mul_lt_mul'' hπ hπ (by norm_num) (by norm_num)
    _ = π ^ 2 := (sq π).symm

/-- `nullQ` near the apex of the tube, in the form `s · (negative)`. -/
theorem e0CE_Q_neg {s η₁ η₂ η₃ : ℝ} (hs0 : 0 < s) (hs : s < 1 / 25) (h1 : |η₁| < s / 100)
    (h2 : |η₂| < s / 100) (h3 : |η₃| < s / 100) :
    -(4 * π ^ 2) * (1 - s) * (9 / 10 * s + η₂) + 4 * π * (1 - s) * η₃ + η₃ ^ 2 +
      (s / 10 - η₁) * (1 - s / 10 + η₂) < 0 := by
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hπ2 := e0CE_pi_sq
  rw [abs_lt] at h1 h2 h3
  have hu : 24 / 25 < 1 - s := by linarith
  have t1 : 36 * (24 / 25) * (89 / 100 * s) < 4 * π ^ 2 * (1 - s) * (9 / 10 * s + η₂) := by
    have hZ : 89 / 100 * s < 9 / 10 * s + η₂ := by linarith
    have hXY : 36 * (24 / 25) < 4 * π ^ 2 * (1 - s) :=
      mul_lt_mul'' (by linarith) hu (by norm_num) (by norm_num)
    exact mul_lt_mul'' hXY hZ (by norm_num) (by positivity)
  have hP : 0 < 4 * π * (1 - s) := by
    have : 0 < 1 - s := by linarith
    positivity
  have t2 : 4 * π * (1 - s) * η₃ < 13 * (s / 100) := by
    have e1 : 4 * π * (1 - s) * η₃ ≤ 4 * π * (1 - s) * (s / 100) :=
      mul_le_mul_of_nonneg_left h3.2.le hP.le
    have e2 : 4 * π * (1 - s) < 13 := by nlinarith
    have e3 : 4 * π * (1 - s) * (s / 100) < 13 * (s / 100) :=
      mul_lt_mul_of_pos_right e2 (by positivity)
    linarith
  have t3 : η₃ ^ 2 < s / 100 := by
    have : |η₃| < 1 := by rw [abs_lt]; constructor <;> linarith
    have h' : η₃ ^ 2 < 1 * (s / 100) := by
      rw [sq]
      calc η₃ * η₃ ≤ |η₃| * |η₃| := by rw [← abs_mul]; exact le_abs_self _
        _ < 1 * (s / 100) := mul_lt_mul'' this (by rw [abs_lt]; exact h3) (abs_nonneg _)
            (abs_nonneg _)
    linarith
  have t4 : (s / 10 - η₁) * (1 - s / 10 + η₂) < (s / 10 + s / 100) * 2 :=
    mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- **The cone region and the tube are not `P`-related**: a translate of a point of `A` in the
tube would have angle near `2π`, hence lie near the apex of the tube, where `nullQ < 0`, while
`nullQ > 0` on `A`. -/
theorem e0CE_noAT {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEA) {k : ℤ} (hk : k ≠ 0)
    (hw' : parab (k * (2 * π)) w ∈ e0CET) : False := by
  obtain ⟨ha, hb, hc, ha0⟩ := e0CEA_mem hw
  have hcone := hw.2
  obtain ⟨s, hs0, hs1, ha', hb', hc'⟩ := e0CET_mem hw'
  simp only [parab_apply] at ha' hb' hc'
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hb1 : w.2.1 < 1 := by
    have := hcone.1; simp only [e0CEv, Prod.snd_sub, Prod.fst_sub] at this; linarith
  rw [abs_lt] at ha hb hc ha' hb' hc'
  -- the winding is `1`
  have hk1 : k = 1 := by
    by_contra hne
    have hpos : 0 < 2 * π * w.2.1 := by nlinarith
    have hbig : 2 * π * w.2.1 > 24 / 5 := by nlinarith
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hlt
      have h5 : (k : ℝ) * (2 * π) * w.2.1 ≤ -(2 * π * w.2.1) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -1 - k) hpos.le]
      have h6 : 0 ≤ (1 - s) * (2 * π) := by
        have : 0 ≤ 1 - s := by linarith
        positivity
      linarith [hc'.1]
    · have : (2 : ℝ) ≤ k := by
        have : 2 ≤ k := by omega
        exact_mod_cast this
      have h5 : 2 * (2 * π * w.2.1) ≤ (k : ℝ) * (2 * π) * w.2.1 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - 2) hpos.le]
      have h6 : (1 - s) * (2 * π) < 2 * π := by nlinarith
      linarith [hc'.2]
  subst hk1
  simp only [Int.cast_one, one_mul] at ha' hb' hc'
  -- the tube parameter is small
  have hs : s < 1 / 25 := by
    have hπs : 3 * s < π * s := mul_lt_mul_of_pos_right hπ hs0
    have hbb : 1 - 11 / 100 * s < w.2.1 := by linarith [hb'.1]
    have e1 : 2 * π * (1 - 11 / 100 * s) < 2 * π * w.2.1 :=
      mul_lt_mul_of_pos_left hbb (by positivity)
    have e2 : w.2.2 + 2 * π * w.2.1 - (1 - s) * (2 * π) < s / 100 := hc'.2
    nlinarith
  -- `nullQ` is positive on `A` and negative near the apex of the tube
  have hQ : nullQ w = nullQ (parab (2 * π) w) := (nullQ_parab _ _).symm
  have hQA : 0 < nullQ w := by
    simp only [nullQ]; nlinarith [sq_nonneg w.2.2]
  set a' := (parab (2 * π) w).1
  set b' := (parab (2 * π) w).2.1
  set c' := (parab (2 * π) w).2.2
  have hQT : nullQ (parab (2 * π) w) = c' ^ 2 - a' * b' := rfl
  set η₁ := a' - ((1 - s) * (4 * π ^ 2) - s / 10)
  set η₂ := b' - (1 - s / 10)
  set η₃ := c' - (1 - s) * (2 * π)
  have h1 : |η₁| < s / 100 := by
    simp only [η₁, a', parab_apply]; rw [abs_lt]; constructor <;> linarith
  have h2 : |η₂| < s / 100 := by
    simp only [η₂, b', parab_apply]; rw [abs_lt]; constructor <;> linarith
  have h3 : |η₃| < s / 100 := by
    simp only [η₃, c', parab_apply]; rw [abs_lt]; constructor <;> linarith
  rw [abs_lt] at h1 h2 h3
  have hexp : c' ^ 2 - a' * b' = -(4 * π ^ 2) * (1 - s) * (9 / 10 * s + η₂) +
      4 * π * (1 - s) * η₃ + η₃ ^ 2 + (s / 10 - η₁) * (1 - s / 10 + η₂) := by
    simp only [η₁, η₂, η₃]; ring
  have hneg : c' ^ 2 - a' * b' < 0 := by
    rw [hexp]
    exact e0CE_Q_neg hs0 hs (by rw [abs_lt]; exact h1) (by rw [abs_lt]; exact h2)
      (by rw [abs_lt]; exact h3)
  linarith [hQ, hQT]

theorem e0CE_injOn : InjOn e0TAInr e0CEUt := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := e0TAInr_eq_parab (e0CEUt_b_pos hw) (e0CEUt_b_pos hw') h
  by_cases hk0 : k = 0
  · rw [hk, hk0, Int.cast_zero, zero_mul, parab_zero]
  exfalso
  rcases hw with hA | hT <;> rcases hw' with hA' | hT'
  · exact e0CE_noAA hA hk0 (hk ▸ hA')
  · exact e0CE_noAT hA hk0 (hk ▸ hT')
  · have hw : w = parab ((-k : ℤ) * (2 * π)) w' := by
      rw [hk, Int.cast_neg, neg_mul, parab_neg_parab]
    exact e0CE_noAT hA' (neg_ne_zero.2 hk0) (hw ▸ hT)
  · exact e0CE_noTT hT hk0 (hk ▸ hT')

/-! ### The isometry `H` and injectivity on the image -/

/-- `H = parab' (−1/2π) ∘ (· − P v₀)`: an orthochronous isometry with `H(P v₀) = 0 ∈ ℝu`. -/
noncomputable def e0CEH : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ) :=
  (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-e0CEp)).trans (parab' (-(1 / (2 * π)))).toAffineEquiv

theorem e0CEH_apply (w : ℝ × ℝ × ℝ) :
    e0CEH w = (w.1 - 4 * π ^ 2, w.2.1 - w.2.2 / π + w.1 / (4 * π ^ 2),
      w.2.2 - w.1 / (2 * π)) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [e0CEH, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add,
    LinearEquiv.coe_toAffineEquiv, parab'_apply, e0CEp]
  ext <;> simp <;> field_simp <;> ring

theorem e0CEH_mem : e0CEH ∈ NullIsom0 := by
  have hlin : e0CEH.linear = (parab' (-(1 / (2 * π)))).toAffineEquiv.linear := by
    ext v <;> rfl
  obtain ⟨h1, h2, h3⟩ := parab'_mem (-(1 / (2 * π)))
  refine ⟨fun v => ?_, ?_, fun v hv hτ => ?_⟩
  · rw [hlin]; exact h1 v
  · rw [hlin]; exact h2
  · rw [hlin]; exact h3 v hv hτ

/-- `H` as an element of `Isom(𝐌³)`. -/
noncomputable def e0CEHM : Causal.Flat.isom 2 := nullIsom0EquivIsom ⟨e0CEH, e0CEH_mem⟩

theorem nullToMink_e0CEH (w : ℝ × ℝ × ℝ) : nullToMink (e0CEH w) = e0CEHM • nullToMink w :=
  nullToMink_smul ⟨e0CEH, e0CEH_mem⟩ w

theorem continuous_e0CEH : Continuous e0CEH := e0CEH.toAffineMap.continuous_of_finiteDimensional

theorem continuous_e0CEH_symm : Continuous e0CEH.symm :=
  e0CEH.symm.toAffineMap.continuous_of_finiteDimensional

/-- On the image of the domain, `b > 0` and the angle `c/b` lies in `(−1, 1)`. -/
theorem e0CE_H_window {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) :
    0 < (e0CEH w).2.1 ∧ |(e0CEH w).2.2| < (e0CEH w).2.1 := by
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hπ2 := e0CE_pi_sq
  have hπ0 : 0 < π := Real.pi_pos
  rw [e0CEH_apply]
  simp only
  rcases hw with hA | hT
  · obtain ⟨ha, hb, hc, -⟩ := e0CEA_mem hA
    rw [abs_lt] at ha hb hc
    have e1 : |w.2.2 / π| < 1 / 15 := by
      rw [abs_div, abs_of_pos hπ0, div_lt_iff₀ hπ0, abs_lt]; constructor <;> nlinarith
    have e2 : |w.1 / (4 * π ^ 2)| < 1 / 150 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2), div_lt_iff₀ (by positivity),
        abs_lt]; constructor <;> nlinarith
    have e3 : |w.1 / (2 * π)| < 1 / 25 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_lt_iff₀ (by positivity),
        abs_lt]; constructor <;> nlinarith
    rw [abs_lt] at e1 e2 e3 ⊢
    refine ⟨by linarith, by constructor <;> linarith⟩
  · obtain ⟨s, hs0, hs1, ha, hb, hc⟩ := e0CET_mem hT
    set η₁ := w.1 - ((1 - s) * (4 * π ^ 2) - s / 10)
    set η₂ := w.2.1 - (1 - s / 10)
    set η₃ := w.2.2 - (1 - s) * (2 * π)
    have hb' : w.2.1 - w.2.2 / π + w.1 / (4 * π ^ 2) =
        s * (9 / 10 - 1 / (40 * π ^ 2)) + η₂ - η₃ / π + η₁ / (4 * π ^ 2) := by
      simp only [η₁, η₂, η₃]; field_simp; ring
    have hc' : w.2.2 - w.1 / (2 * π) = η₃ + s / (20 * π) - η₁ / (2 * π) := by
      simp only [η₁, η₃]; field_simp; ring
    rw [hb', hc']
    rw [abs_lt] at ha hb hc
    have e1 : |η₃ / π| < s / 300 := by
      rw [abs_div, abs_of_pos hπ0, div_lt_iff₀ hπ0, abs_lt]; constructor <;> nlinarith
    have e2 : |η₁ / (4 * π ^ 2)| < s / 3600 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2), div_lt_iff₀ (by positivity),
        abs_lt]; constructor <;> nlinarith
    have e3 : |η₁ / (2 * π)| < s / 600 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_lt_iff₀ (by positivity),
        abs_lt]; constructor <;> nlinarith
    have e4 : s / (20 * π) < s / 60 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have e5 : 0 < s / (20 * π) := by positivity
    have e6 : 1 / (40 * π ^ 2) < 1 / 360 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have e7 : s * (9 / 10 - 1 / 360) < s * (9 / 10 - 1 / (40 * π ^ 2)) := by
      apply mul_lt_mul_of_pos_left _ hs0; linarith
    rw [abs_lt] at e1 e2 e3 ⊢
    refine ⟨by linarith, by constructor <;> linarith⟩

/-- `[D⁻¹ ·]` is injective on a set where `b > 0` and `|c| < b`. -/
theorem e0TAInr_injOn_of_window {S : Set (ℝ × ℝ × ℝ)}
    (hS : ∀ w ∈ S, 0 < w.2.1 ∧ |w.2.2| < w.2.1) : InjOn e0TAInr S := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := e0TAInr_eq_parab (hS w hw).1 (hS w' hw').1 h
  by_cases hk0 : k = 0
  · rw [hk, hk0, Int.cast_zero, zero_mul, parab_zero]
  exfalso
  have h1 := hS w hw
  have h2 := hS w' hw'
  rw [hk] at h2
  simp only [parab_apply] at h2
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  have hπ := Real.pi_gt_three
  have hlt : |(k : ℝ) * (2 * π) * w.2.1| < 2 * w.2.1 := by
    have e : (k : ℝ) * (2 * π) * w.2.1 = (w.2.2 + k * (2 * π) * w.2.1) - w.2.2 := by ring
    rw [e]
    calc |(w.2.2 + k * (2 * π) * w.2.1) - w.2.2| ≤ |w.2.2 + k * (2 * π) * w.2.1| + |w.2.2| :=
          abs_sub _ _
      _ < w.2.1 + w.2.1 := add_lt_add h2.2 h1.2
      _ = 2 * w.2.1 := by ring
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos h1.1] at hlt
  have hpos : 0 < 2 * π * w.2.1 := by have := h1.1; positivity
  have h3 := mul_le_mul_of_nonneg_right hk1 hpos.le
  rw [one_mul, ← mul_assoc] at h3
  nlinarith

/-! ### `[D⁻¹ ·]` is open, with continuous inverses on injectivity sets -/

theorem e0TAInr_isOpen_image {S : Set (ℝ × ℝ × ℝ)} (hS : IsOpen S) (hSb : ∀ w ∈ S, 0 < w.2.1) :
    IsOpen (e0TAInr '' S) := by
  have hcyl : IsOpen (cylPos ℝ) :=
    isOpen_lt continuous_const (DInfty.continuous_r'.comp continuous_fst)
  have hD : ContinuousOn (btzDev 0 btzV0) (cylPos ℝ) := by
    have h := (isLocalHomeomorphOn_btzDevM 0 btzV0_pos).continuousOn
    have : btzDev 0 btzV0 = nullToMink.symm ∘ btzDevM 0 btzV0 := by
      funext y; simp [btzDevM]
    rw [this]; exact nullToMinkHomeomorph.symm.continuous.comp_continuousOn h
  have himg : btzDevInv '' S = cylPos ℝ ∩ btzDev 0 btzV0 ⁻¹' S := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e0TA_btzDevInv_mem (hSb w hw), by
        rw [mem_preimage, btzDev_btzDevInv (Or.inl (hSb w hw))]; exact hw⟩
    · rintro ⟨hy, hyS⟩
      exact ⟨_, hyS, btzDevInv_btzDev y⟩
  have h1 : IsOpen (btzDevInv '' S) := by rw [himg]; exact hD.isOpen_inter_preimage hcyl hS
  have h2 : IsOpen (orbitMk (GammaA (2 * π)) '' (btzDevInv '' S)) :=
    isOpenMap_quotient_mk'_mul _ h1
  have h3 := (IsOpenEmbedding.inr : IsOpenEmbedding (Sum.inr : BTZE0 → E0Y)).isOpenMap _ h2
  have : e0TAInr '' S = Sum.inr '' (orbitMk (GammaA (2 * π)) '' (btzDevInv '' S)) := by
    rw [image_image, image_image]; rfl
  rw [this]; exact h3

theorem e0TAInr_invFunOn_tendsto {S : Set (ℝ × ℝ × ℝ)} (hS : IsOpen S)
    (hSb : ∀ w ∈ S, 0 < w.2.1) (hinj : InjOn e0TAInr S) {w : ℝ × ℝ × ℝ} (hw : w ∈ S) :
    Tendsto (invFunOn e0TAInr S) (𝓝 (e0TAInr w)) (𝓝 w) := by
  intro N hN
  obtain ⟨N', hN'N, hN'o, hwN'⟩ := mem_nhds_iff.1 (inter_mem hN (hS.mem_nhds hw))
  have hopen := e0TAInr_isOpen_image hN'o fun v hv => hSb v (hN'N hv).2
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds ⟨w, hwN', rfl⟩) ?_)
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_preimage, hinj.leftInvOn_invFunOn (hN'N hv).2]
  exact (hN'N hv).1

/-! ### The map `f` and its partial homeomorphism -/

theorem e0CEUt_window_b {x : ℝ × ℝ × ℝ} (hx : x ∈ e0CEH '' e0CEUt) : 0 < x.2.1 := by
  obtain ⟨w, hw, rfl⟩ := hx; exact (e0CE_H_window hw).1

theorem e0CE_injOn_H : InjOn e0TAInr (e0CEH '' e0CEUt) :=
  e0TAInr_injOn_of_window fun _ ⟨_, hw, h⟩ => h ▸ e0CE_H_window hw

theorem isOpen_e0CEHUt : IsOpen (e0CEH '' e0CEUt) := by
  have : e0CEH '' e0CEUt = e0CEH.symm ⁻¹' e0CEUt := by
    ext x; constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hx; exact ⟨_, hx, by simp⟩
  rw [this]; exact isOpen_e0CEUt.preimage continuous_e0CEH_symm

/-- The domain `U = [D⁻¹ Ũ]`. -/
noncomputable def e0CEU : Set E0Y := e0TAInr '' e0CEUt

/-- The image `V = [D⁻¹ H Ũ]`. -/
noncomputable def e0CEV : Set E0Y := e0TAInr '' (e0CEH '' e0CEUt)

/-- **The map** `f [D⁻¹ w] = [D⁻¹ H w]` on `U`. -/
noncomputable def e0CEf (y : E0Y) : E0Y := e0TAInr (e0CEH (invFunOn e0TAInr e0CEUt y))

/-- Its inverse on `V`. -/
noncomputable def e0CEg (y : E0Y) : E0Y :=
  e0TAInr (e0CEH.symm (invFunOn e0TAInr (e0CEH '' e0CEUt) y))

theorem e0CEf_apply {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) : e0CEf (e0TAInr w) = e0TAInr (e0CEH w) := by
  rw [e0CEf, e0CE_injOn.leftInvOn_invFunOn hw]

theorem e0CEg_apply {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) :
    e0CEg (e0TAInr (e0CEH w)) = e0TAInr w := by
  rw [e0CEg, e0CE_injOn_H.leftInvOn_invFunOn ⟨w, hw, rfl⟩, AffineEquiv.symm_apply_apply]

theorem isOpen_e0CEU : IsOpen e0CEU :=
  e0TAInr_isOpen_image isOpen_e0CEUt fun _ hw => e0CEUt_b_pos hw

theorem isOpen_e0CEV : IsOpen e0CEV :=
  e0TAInr_isOpen_image isOpen_e0CEHUt fun _ hx => e0CEUt_window_b hx

theorem e0CEf_continuousAt {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) : ContinuousAt e0CEf (e0TAInr w) := by
  have ht := e0TAInr_invFunOn_tendsto isOpen_e0CEUt (fun _ h => e0CEUt_b_pos h) e0CE_injOn hw
  have hb := (e0CE_H_window hw).1
  have hc : ContinuousAt e0TAInr (e0CEH w) :=
    e0TAInr_continuousOn.continuousAt (e0TA_isOpen_b.mem_nhds hb)
  show Tendsto e0CEf (𝓝 (e0TAInr w)) (𝓝 (e0CEf (e0TAInr w)))
  rw [e0CEf_apply hw]
  exact hc.tendsto.comp (continuous_e0CEH.continuousAt.tendsto.comp ht)

theorem e0CEg_continuousAt {w : ℝ × ℝ × ℝ} (hw : w ∈ e0CEUt) :
    ContinuousAt e0CEg (e0TAInr (e0CEH w)) := by
  have ht := e0TAInr_invFunOn_tendsto isOpen_e0CEHUt (fun _ h => e0CEUt_window_b h) e0CE_injOn_H
    ⟨w, hw, rfl⟩
  have hc : ContinuousAt e0TAInr w :=
    e0TAInr_continuousOn.continuousAt (e0TA_isOpen_b.mem_nhds (e0CEUt_b_pos hw))
  show Tendsto e0CEg (𝓝 (e0TAInr (e0CEH w))) (𝓝 (e0CEg (e0TAInr (e0CEH w))))
  rw [e0CEg_apply hw]
  have h2 : Tendsto (fun x => e0CEH.symm x) (𝓝 (e0CEH w)) (𝓝 w) := by
    have := continuous_e0CEH_symm.continuousAt.tendsto (x := e0CEH w)
    rwa [AffineEquiv.symm_apply_apply] at this
  exact hc.tendsto.comp (h2.comp ht)

/-- **The partial homeomorphism** `U → V` carrying `f`. -/
noncomputable def e0CEe : OpenPartialHomeomorph E0Y E0Y where
  toFun := e0CEf
  invFun := e0CEg
  source := e0CEU
  target := e0CEV
  map_source' := by
    rintro _ ⟨w, hw, rfl⟩; rw [e0CEf_apply hw]; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  map_target' := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩; rw [e0CEg_apply hw]; exact ⟨w, hw, rfl⟩
  left_inv' := by
    rintro _ ⟨w, hw, rfl⟩; rw [e0CEf_apply hw, e0CEg_apply hw]
  right_inv' := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩; rw [e0CEg_apply hw, e0CEf_apply hw]
  open_source := isOpen_e0CEU
  open_target := isOpen_e0CEV
  continuousOn_toFun := by
    rintro _ ⟨w, hw, rfl⟩; exact (e0CEf_continuousAt hw).continuousWithinAt
  continuousOn_invFun := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩; exact (e0CEg_continuousAt hw).continuousWithinAt

theorem nullToMink_e0CEH_symm (u : ℝ × ℝ × ℝ) :
    nullToMink (e0CEH.symm u) = e0CEHM⁻¹ • nullToMink u := by
  rw [eq_inv_smul_iff, ← nullToMink_e0CEH, AffineEquiv.apply_symm_apply]

/-- The chart condition for `ι ∘ F ∘ ι⁻¹` at `ι w`, `F` a continuous map developing as `h`. -/
theorem e0CE_regAt {S S' : Set (ℝ × ℝ × ℝ)} (hS : IsOpen S) (hSb : ∀ w ∈ S, 0 < w.2.1)
    (hinj : InjOn e0TAInr S) {F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hF : Continuous F)
    (hFS : ∀ w ∈ S, F w ∈ S') (hS'b : ∀ w ∈ S', 0 < w.2.1)
    {h : Causal.Flat.isom 2} (hFh : ∀ w, nullToMink (F w) = h • nullToMink w)
    {φ : E0Y → E0Y} (hφ : ∀ w ∈ S, φ (e0TAInr w) = e0TAInr (F w))
    (hφc : ContinuousAt φ (e0TAInr w₀)) (hw₀ : w₀ ∈ S) : E0RegAt φ (e0TAInr w₀) := by
  refine e0RegAt_of_exists hφc ?_
  obtain ⟨c, hc, hwc, g₁, hg₁⟩ := e0TAInr_chart (hSb w₀ hw₀)
  obtain ⟨c', hc', hwc', g₂, hg₂⟩ := e0TAInr_chart (hS'b _ (hFS w₀ hw₀))
  refine ⟨c, hc, c', hc', hwc, by rw [hφ w₀ hw₀]; exact hwc', g₂ * h * g₁⁻¹, ?_⟩
  have ht := e0TAInr_invFunOn_tendsto hS hSb hinj hw₀
  have hU : e0TAInr '' S ∈ 𝓝 (e0TAInr w₀) :=
    (e0TAInr_isOpen_image hS hSb).mem_nhds ⟨w₀, hw₀, rfl⟩
  have hFt : Tendsto (fun y => F (invFunOn e0TAInr S y)) (𝓝 (e0TAInr w₀)) (𝓝 (F w₀)) :=
    hF.continuousAt.tendsto.comp ht
  filter_upwards [hU, ht.eventually hg₁, hFt.eventually hg₂] with y hy e1 e2
  obtain ⟨v, hv, rfl⟩ := hy
  rw [hinj.leftInvOn_invFunOn hv] at e1 e2
  rw [hφ v hv, e2, e1, hFh, mul_smul, mul_smul, inv_smul_smul]

theorem e0CEe_mem : e0CEe ∈ e0Groupoid := by
  rw [mem_e0Groupoid_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact e0CE_regAt (S' := e0CEH '' e0CEUt) isOpen_e0CEUt (fun _ h => e0CEUt_b_pos h)
      e0CE_injOn continuous_e0CEH (fun v hv => ⟨v, hv, rfl⟩) (fun _ h => e0CEUt_window_b h) nullToMink_e0CEH
      (fun v hv => e0CEf_apply hv) (e0CEf_continuousAt hw) hw
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact e0CE_regAt (S' := e0CEUt) isOpen_e0CEHUt (fun _ h => e0CEUt_window_b h) e0CE_injOn_H
      continuous_e0CEH_symm (fun u ⟨v, hv, he⟩ => by rw [← he, AffineEquiv.symm_apply_apply]; exact hv)
      (fun _ h => e0CEUt_b_pos h) nullToMink_e0CEH_symm
      (fun u ⟨v, hv, he⟩ => by
        show e0CEg (e0TAInr u) = _
        rw [← he, e0CEg_apply hv, AffineEquiv.symm_apply_apply])
      (e0CEg_continuousAt hw) ⟨w, hw, rfl⟩

theorem e0CEf_isLocalStructomorph :
    ∀ y ∈ e0CEU, e0Groupoid.IsLocalStructomorphWithinAt e0CEf e0CEU y :=
  fun _ hy _ => ⟨e0CEe, e0CEe_mem, fun _ _ => rfl, hy⟩

theorem e0CEf_injOn : InjOn e0CEf e0CEU := by
  rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ h
  rw [e0CEf_apply hw, e0CEf_apply hw'] at h
  rw [e0CEH.injective (e0CE_injOn_H ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩ h)]

/-! ### The BTZ cluster value along the apex end of the tube -/

theorem e0CEp_eq : e0CEp = parab ((1 : ℤ) * (2 * π)) e0CEv := by
  simp only [e0CEp, e0CEv, parab_apply, Int.cast_one, one_mul]
  ext <;> simp; ring

theorem e0TAInr_e0CEp : e0TAInr e0CEp = e0TAInr e0CEv := by
  rw [e0CEp_eq]; exact e0TAInr_parab (by simp [e0CEv]) 1

/-- `H` maps the axis of the tube to the ray `s q₀`. -/
noncomputable def e0CEq : ℝ × ℝ × ℝ :=
  (-(4 * π ^ 2) - 1 / 10, 9 / 10 - 1 / (40 * π ^ 2), 1 / (20 * π))

theorem e0CEH_c (s : ℝ) : e0CEH (e0CEc s) = s • e0CEq := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [e0CEH_apply, e0CEc_apply]
  simp only [e0CEq, Prod.smul_mk, smul_eq_mul]
  ext <;> simp only <;> field_simp <;> ring

theorem e0CEq_b : 0 < e0CEq.2.1 := by
  have hπ2 := e0CE_pi_sq
  simp only [e0CEq]
  have : 1 / (40 * π ^ 2) < 1 / 360 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- The BTZ point `[apex, 0]` of `Y`. -/
noncomputable def e0CEz : E0Y := Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, 0))

theorem e0CEz_not_reg : e0CEz ∉ e0Reg := by
  rw [e0CEz, inr_mem_e0Reg_iff, btzE0_reg_eq]
  rintro ⟨y, hy, he⟩
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_orbitMk_eq he
  have := gammaA_smul_r γ y
  rw [hγ] at this
  simp only [DInfty.apex_r] at this
  have hy' : 0 < y.1.r := hy
  linarith

theorem btzDevInv_r {x : ℝ × ℝ × ℝ} (hx : 0 < x.2.1) : (btzDevInv x).1.r = x.2.1 := by
  have h := btzDev_e0_b (btzDevInv x)
  rw [btzDev_btzDevInv (Or.inl hx)] at h
  exact h.symm

theorem btzDevInv_t {x : ℝ × ℝ × ℝ} (hx : 0 < x.2.1) :
    (btzDevInv x).2 = x.1 + x.2.1 - x.2.2 ^ 2 / x.2.1 := by
  rw [btzDevInv, dif_pos hx]

theorem e0CE_tendsto_z :
    Tendsto (fun s : ℝ => e0TAInr (s • e0CEq)) (𝓝[>] 0) (𝓝 e0CEz) := by
  have hb := e0CEq_b
  set F : ℝ → DInfty × ℝ := fun s => btzDevInv (s • e0CEq) with hFdef
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < (s • e0CEq).2.1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    show 0 < s * e0CEq.2.1
    exact mul_pos hs hb
  have h1 : Tendsto (fun s => (F s).1) (𝓝[>] (0 : ℝ)) (𝓝 DInfty.apex) := by
    rw [DInfty.hasBasis_nhds_apex.tendsto_right_iff]
    intro ε hε
    have hlim : Tendsto (fun s : ℝ => s * e0CEq.2.1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0))).mul_const e0CEq.2.1
    filter_upwards [hpos, hlim (Iio_mem_nhds hε)] with s hs h2
    show (btzDevInv (s • e0CEq)).1.r < ε
    rw [btzDevInv_r hs]; exact h2
  have h2 : Tendsto (fun s => (F s).2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    set K := e0CEq.1 + e0CEq.2.1 - e0CEq.2.2 ^ 2 / e0CEq.2.1
    have hlim : Tendsto (fun s : ℝ => s * K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0))).mul_const K
    refine hlim.congr' ?_
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs hs0
    show s * K = (btzDevInv (s • e0CEq)).2
    rw [btzDevInv_t hs]
    have : (s : ℝ) ≠ 0 := ne_of_gt hs0
    simp only [K, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 ((DInfty.apex, 0) : DInfty × ℝ)) := h1.prodMk_nhds h2
  exact ((continuous_inr.comp continuous_quot_mk).tendsto _).comp hF

/-- The tip `y₀ = [D⁻¹ v₀]`. -/
noncomputable def e0CEy : E0Y := e0TAInr e0CEv

theorem e0CE_mapClusterPt : MapClusterPt e0CEz (𝓝[e0CEU] e0CEy) e0CEf := by
  have hp : Tendsto e0CEc (𝓝[>] (0 : ℝ)) (𝓝 e0CEp) := by
    have := continuous_e0CEc.tendsto (0 : ℝ)
    have h0 : e0CEc 0 = e0CEp := by simp [e0CEc]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), e0CEc s ∈ e0CEUt := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact Or.inr (e0CEc_mem hs)
  have hcont : ContinuousAt e0TAInr e0CEp :=
    e0TAInr_continuousOn.continuousAt (e0TA_isOpen_b.mem_nhds (by simp [e0CEp]))
  have hy : Tendsto (fun s => e0TAInr (e0CEc s)) (𝓝[>] (0 : ℝ)) (𝓝[e0CEU] e0CEy) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hmem.mono fun s hs => ⟨_, hs, rfl⟩⟩
    have := hcont.tendsto.comp hp
    rwa [Function.comp_def, e0TAInr_e0CEp] at this
  have hf : Tendsto (fun s => e0CEf (e0TAInr (e0CEc s))) (𝓝[>] (0 : ℝ)) (𝓝 e0CEz) := by
    refine e0CE_tendsto_z.congr' ?_
    filter_upwards [hmem] with s hs
    rw [e0CEf_apply hs, e0CEH_c]
  have hcl : MapClusterPt e0CEz (map (fun s => e0TAInr (e0CEc s)) (𝓝[>] (0 : ℝ))) e0CEf := by
    show ClusterPt _ _
    rw [Filter.map_map]
    exact hf.mapClusterPt
  exact ClusterPt.mono hcl (Filter.map_mono hy)

/-! ### The counterexample -/

theorem e0CE_ball_b {w : ℝ × ℝ × ℝ} (hw : w ∈ Metric.ball e0CEv (1 / 5)) : 0 < w.2.1 := by
  have := (e0CE_abs_lt_of_dist hw).2.1
  simp only [e0CEv] at this
  rw [abs_lt] at this; linarith

/-- The neighbourhood `O = [D⁻¹ B(v₀, 1/5)]` of the tip. -/
noncomputable def e0CEO : Opens E0Y :=
  ⟨e0TAInr '' Metric.ball e0CEv (1 / 5),
    e0TAInr_isOpen_image Metric.isOpen_ball fun _ hw => e0CE_ball_b hw⟩

/-- **`typeAgreement` fails for `𝕄 ⊕ 𝔼₀`** (finding, `SCOPE (c)`), for every causality `C` in which
straight timelike segments of `[D⁻¹ ·]` are chronological (`E0TASegLt`) and whose chronological past
of the tip `y₀ = [D⁻¹(0, 1, 0)]` inside `O = [D⁻¹ B(v₀, 1/5)]` is read in the past cone of `v₀`
(`hdiam`; for the model causality both are proved in `campaign/WP-41c/TypeAgreementD.lean`). The
domain `U = [D⁻¹ Ũ]` winds once around the axis; `f [D⁻¹ w] = [D⁻¹ H w]` is an injective local
`G`-structomorphism on it, regular at `y₀`, with the BTZ cluster value `[apex, 0]` at `y₀`. -/
theorem e0_not_typeAgreement_of (C : Causal.Causality E0Y)
    (hinr : E0TASegLt C e0TAInr {v | 0 < v.2.1})
    (hdiam : ∀ x : E0Y, C.lt e0CEO x e0CEy → x ∈ e0TAInr '' e0CEA) : ¬ E0TypeAgreement C := by
  intro h
  have hUc : IsConnected e0CEU :=
    ⟨⟨_, _, Or.inl e0CEc_mem_A, rfl⟩, isPreconnected_e0CEUt.image _
      (e0TAInr_continuousOn.mono fun _ hw => e0CEUt_b_pos hw)⟩
  have hy₀ : e0CEy ∉ e0SingY 0 := fun h0 => h0.2 (e0TAInr_reg (by simp [e0CEv]))
  have hdv : dist e0CEd e0CEv < 1 / 5 := by
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [e0CEd, e0CEv, Real.dist_eq]
    refine max_lt ?_ (max_lt ?_ ?_) <;> norm_num [abs_lt]
  have hlt : C.lt e0CEO (e0TAInr e0CEd) e0CEy :=
    hinr e0CEO (Metric.ball e0CEv (1 / 5)) Metric.isOpen_ball (convex_ball _ _)
      (fun _ hw => e0CE_ball_b hw) (fun v hv => ⟨v, hv, rfl⟩) e0CEd hdv e0CEv
      (Metric.mem_ball_self (by norm_num))
      ((e0TA_minkowski_lt_iff _ _).2 (by
        simp only [e0TACone, e0CEv, e0CEd, Prod.mk_sub_mk]; norm_num))
  have hd : ∃ O : Opens E0Y, e0CEy ∈ O ∧ ∃ r ∈ O,
      (C.lt O r e0CEy ∧ C.Iplus O {r} ∩ C.Iminus O {e0CEy} ⊆ e0CEU) ∨
      (C.lt O e0CEy r ∧ C.Iplus O {e0CEy} ∩ C.Iminus O {r} ⊆ e0CEU) := by
    refine ⟨e0CEO, ⟨e0CEv, Metric.mem_ball_self (by norm_num), rfl⟩, e0TAInr e0CEd,
      ⟨e0CEd, hdv, rfl⟩, Or.inl ⟨hlt, fun x hx => ?_⟩⟩
    obtain ⟨w, hw, rfl⟩ := hdiam x (Causal.Precausality.mem_Iminus_singleton.1 hx.2)
    exact ⟨w, Or.inl hw, rfl⟩
  obtain ⟨hty, -⟩ := h e0CEU isOpen_e0CEU hUc e0CEy hy₀ hd e0CEz e0CEf
    e0CEf_isLocalStructomorph e0CEf_injOn e0CE_mapClusterPt
  exact hy₀ ((hty 0 le_rfl).2 ⟨rfl, e0CEz_not_reg⟩)

end Counterexample

end GX
