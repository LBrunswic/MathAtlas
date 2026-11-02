import GXScaffold.BTZ.Model

/-!
# `GXScaffold.BTZ.Rigid` — the rigidity fields of the local model `𝕄 ⊕ 𝔼₀`

Package WP-41c (WAVE5-PLAN.md, WP-39c). The model data of the CBG local model
(`Causal.CBG.LocalModel`, `lean-causal` pinned `731ed99`, `Causal/CBG/Geometry.lean`) for gx's
Section 4: `Y = 𝕄 ⊕ 𝔼₀` (`GX.E0Y`), the a.e.-isomorphism groupoid `G` (`GX.e0Groupoid`), the
singular loci `sing_0 = Sing(𝔼₀)`, `sing_α = ∅` for `α ≠ 0` (`GX.e0SingY`), and the fields of
`LocalModel` that are about `Y`, `G` and `singY` alone, each a standalone theorem with the field's
statement verbatim (`Y`, `G`, `singY` substituted). **0 `sorry`.**

No ledger label of `RamcovGX.tex` is certified here: the fields are CBG-interface obligations
(`BARBOT-INTERFACE.md`, "gx's E₀ obligations"), not rows of the paper. Cited, unmarked:
B21 `lem:liouville` (`BTZ_1.tex:361`), B21 `prop:isom_strong` (`BTZ_1.tex:468–475`).

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
* `localUnique_sing_adherent`, `typeAgreement` — stated verbatim as `GX.E0LocalUniqueSingAdherent C`
  and `GX.E0TypeAgreement C` over a causality `C` of `Y` (SCOPE (b)), **partial**: reduced, for
  every `C`, to a property of `C`'s diamonds alone (`GX.e0_localUniqueSingAdherent_of_region`, via
  `GX.e0_localUniqueSingAdherent_of_local`) and to "`z₀` regular" (`GX.e0_typeAgreement_of_reg`).
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

## Hypothesis checklist

| interface | here |
|---|---|
| `Y = 𝕄 ⊕ Σ_α 𝔼_α` | `𝕄 ⊕ 𝔼₀` (the dispatch's `Y`): `Causal.Minkowski 2 ⊕ GX.BTZE0` |
| `G`: on the regular part the `(G,X)`-morphisms, near a singular point the restrictions of `Aut(𝔼₀)` | `G` = the a.e.-isomorphisms (BARBOT-INTERFACE, "Instance: `Y = 𝕄 ⊕ E₀`, `G` = a.e.-isomorphisms"): open partial homeomorphisms which, with their inverse, map `Reg` into `Reg` and are there, in the charts of `𝕄` and of the maximal a.e. atlas of `𝔼₀`, locally translations by `Isom(𝐌³)` |
| `sing_α(Y)` | `sing_0 = Sing(Y) = inr '' Sing(𝔼₀)` (`= inr '' {r = 0}` by `GX.btz_sing`), `sing_α = ∅` for `α ≠ 0` |
| `localUnique_sing`: `U` connected, `0 ≤ α₀` | carried verbatim; the local core uses neither (connectedness enters only through rigidity) |

## SCOPE (disclosed)

* (a) `rigid` is proved directly (`GX.e0_rigid`, by propagation along the preconnected dense
  `reg(U)`) rather than through the strict `IsAEMorphismOf.eq_of_eqOn` (DEC-42): that lemma is
  about global maps of a preconnected singular manifold, and an element of `G` is a partial
  homeomorphism of the sum `Y`; the bridge would need `Y`'s a.e. atlas as a singular structure on
  each source, which is longer than the direct proof.
* (b) `typeAgreement` and `localUnique_sing_adherent` mention the model causality `causalityY`,
  which is WP-39e's (`GXScaffold.BTZ.Causality`, WP-41e, not imported: it is another package's
  file in progress). They are stated as propositions over a causality `C`. Pending obligations
  for the assembly (WP-39f), once `C` is fixed: **(b1)** every regular chronological diamond with
  a BTZ tip contains a circle-swept region (the hypothesis of
  `GX.e0_localUniqueSingAdherent_of_region`; for `𝔼₀`'s causality, `I⁺(p) = {r > 0, f > τ_p}`
  makes the region `{τ > τ_p + r/2 + η, τ < τ_r − η', r < δ}`, convex in `log r` since `e^ρ` is
  convex); **(b2)** the hypothesis `hreg` of `GX.e0_typeAgreement_of_reg` (`z₀` regular when `y₀`
  is), the θ-loop holonomy argument in the diamond. For a causality whose chronological diamonds
  are empty the inclusion hypotheses hold trivially and we expect both statements to fail; this is
  not proved here, so no theorem over all `C` is claimed.

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

end GX
