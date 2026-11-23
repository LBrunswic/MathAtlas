import GX.BBS.IPm

/-!
# BBS § 3.3–3.4: the suspension `𝔢(L)` of a `(Γ_p, ℓ(p))`-circle, and singular HS-surfaces

Target `T-bbs-hs-suspension` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx, DEC-192; wave W2
of `papers/bbs/REVIEW.md` §E). `papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`; imports only
the strict `GX.BBS.IPm`.

* `bbsdef:singular_hs_surface_oriented_surface` — `colI_v1.tex:948` — partial (unmarked: « surface »
  is OQ-104's reading, and « oriented », « HS-isomorphic » and the choice of developing data are
  readings, SCOPE (b)–(e)): `GX.IsSingularHSSurface`, on a `GX.SingularHSStructure` (`𝒮` and an
  HS-atlas of `Σ ∖ 𝒮`), with HS-isomorphisms `GX.SingularHSStructure.IsIso`; witnessed by every
  HS-surface (`GX.isSingularHSSurface_ofHSSurface`, `𝒮 = ∅`) and by every `𝔢(L)`
  (`GX.GammaLinkCircle.DevData.isSingularHSSurface`, `𝒮 = {p̄, −p̄}`).
* The suspension `𝔢(L)` (l.775–781, prose, no label), every assertion proved: `GX.BiSusp L`
  (`L × [0, π]`, each end collapsed), `𝔢(v)` is `GX.suspSeg p v`, the cone charts `GX.suspChart`,
  the HS-atlas `GX.GammaLinkCircle.DevData.suspAtlas` (chart changes in `Γ_p`), « topologically a
  sphere » (`GX.GammaLinkCircle.suspHomeomorph : 𝔢(L) ≃ₜ HS²`), « locally modeled on `HS²` in the
  complement of two singular points » (`GX.GammaLinkCircle.DevData.isHSSurface_reg`), and
  `𝔢(ℓ(p)) = HS²` for the regular link (`GX.GammaLinkCircle.DevData.regular_susp`).

> Given a $(\Gamma_p, \ell(p))$-circle $L$, we construct a singular HS-surface $\mathfrak{e}(L)$:
> for every element $v$ in the link of $p$, define $\mathfrak{e}(v)$ as the closed segment
> $[-p, p]$ contained in the projective ray defined by $v$, where $-p$ is the antipodal point of
> $p$ in $\HS^2$, and then operate as we did for defining the AdS space $e(\Sigma)$ associated to
> a HS-surface. The resulting space $\mathfrak{e}(L)$ is topologically a sphere, locally modeled on
> $\HS^2$ in the complement of two singular points corresponding to $p$ and $-p$. (l.775–781)
>
> Define $e(\Sigma)$ as the disjoint union of the $e(U_i)$, quotiented by the relation
> identifying $q$ in $e(U_{ij})$ with $g_{ij}(q)$ in $e(U_{ji})$. (l.649–651)
>
> A singular HS-surface $\Sigma$ is an oriented surface containing a discrete subset
> $\mathcal{S}$ such that $\Sigma \setminus \mathcal{S}$ is a regular HS-surface, and such that
> every $p$ in $\mathcal{S}$ admits a neighborhood HS-isomorphic to an open subset of the
> suspension $\mathfrak{e}(L)$ of a $(\Gamma_p, \ell(p))$-circle $L$. (l.949–952)

## Main declarations

* **The two-apex suspension** `GX.BiSusp S = S × [0, π]/∼` (quotient topology), apices
  `GX.BiSusp.north`, `GX.BiSusp.south` (`GX.BiSusp.poles`); for `φ : S ≃ₜ 𝕊¹`,
  `GX.BiSusp.homeomorphSph2 : BiSusp S ≃ₜ 𝕊²`, `[σ, t] ↦ (cos t, sin t · φ(σ))`.
* **The segments.** `GX.arcPt p w t = [cos t · p + sin t · w]`; `GX.suspSeg p v` is the closed
  segment from `p` (`t = 0`) to `−p` (`t = π`) through `v`: `GX.mem_suspSeg_iff` (`p`, `−p`, and
  the points of direction `v` from `p`), independent of the lift (`GX.image_arcPt_eq_suspSeg`), and
  they cover `HS²` (`GX.iUnion_suspSeg`). `GX.arcAngle` inverts `t` (`GX.arcPt_arcAngle`,
  `GX.arcAngle_arcPt`); `Γ_p` maps segments onto segments (`GX.smul_arcPt`).
* **Cone charts.** For a chart `c` of `L` and a continuous lift `W`, `[W σ] = c σ`
  (`GX.IsConeLift`): `GX.suspChart c W`, `[σ, t] ↦ [cos t p + sin t W(σ)]`, an open partial
  homeomorphism onto `(⋃_{v ∈ c(U)} 𝔢(v)) ∖ {±p}` (`GX.suspChart_target_eq`, the paper's
  `e(U) ∖ {p}`), the segment over `σ` onto `𝔢(c σ)` (`GX.range_suspMap_mk`).
* **Developing data** `GX.GammaLinkCircle.DevData`: a periodic covering `E : ℝ → L`, a developing
  map `d` with holonomy `ρ ∈ Γ_p`, and a continuous lift `w` of `d` with `w(s + 1) = ρ w(s)`;
  it exists (`GX.GammaLinkCircle.nonempty_devData`; `w` is a tent average, `GX.tentAvg`).
* **`𝔢(L)`.** `…DevData.suspAtlas`: the cone charts whose lifts are locally `Γ_p`-translates of
  `w` along `E`; chart changes in `Γ_p` (`…suspAtlas_eventually_eq_smul`), over charts of `L`'s
  maximal atlas (`…mem_maximalAtlas_of_mem_suspAtlas`), support `𝔢(L) ∖ {p̄, −p̄}`
  (`…support_suspAtlas`); `…DevData.suspStructure`.
* **Singular HS-surfaces.** `GX.SingularHSStructure`, `…regChartedSpace` and `…isHSSurface_reg`
  (`Σ ∖ 𝒮` is a `GX.IsHSSurface`), `…IsIso`, `GX.IsSingularHSSurface`.

## Hypothesis checklist

| BBS | here |
|---|---|
| « oriented surface » (l.949) | ⚠ reading: `GX.IsTopologicalSurface` (OQ-104); « oriented » not a field (SCOPE (d)) |
| « a discrete subset `𝒮` » (l.949) | ✓ `DiscreteTopology A.sing`; `𝒮` is then closed (`SingularHSStructure.isClosed_sing`) |
| « `Σ ∖ 𝒮` is a regular HS-surface » (l.950) | ✓ an HS-atlas of `Σ` with support `Σ ∖ 𝒮`; `isHSSurface_reg`: a `GX.IsHSSurface` |
| « a neighborhood HS-isomorphic to an open subset of `𝔢(L)` » (l.951–952) | ⚠ reading `SingularHSStructure.IsIso` (SCOPE (e)) |
| « a `(Γ_p, ℓ(p))`-circle `L` » (l.952) | ✓ `GX.GammaLinkCircle`, at any point of `HS²` (SCOPE (f)); `L : Type` |
| `𝔢(v)`, « the closed segment `[−p, p]` » (l.777–778) | ✓ `suspSeg`, `range_suspMap_mk` |
| « operate as we did for `e(Σ)` » (l.779; l.641–651) | ✓ cone charts glued by elements of `Γ_p` (SCOPE (a)); for developing data `Δ` (SCOPE (b)) |
| « topologically a sphere » (l.780) | ✓ `suspHomeomorph` |
| « locally modeled on `HS²` off two singular points » (l.780–781) | ✓ `isHSSurface_reg`; `suspMap_north`, `suspMap_south` |
| (the target) `𝔢(ℓ(p)) = HS²` | ✓ `regular_susp` (the analogue of `e(HS²) = E(p)`, l.658–659) |

## SCOPE (disclosed)

* **(a) The construction.** The paper glues the subsets `𝔢(U_i) ⊂ HS²` by the chart changes
  `g_ij ∈ Γ_p`. `Γ_p` maps `𝔢(v)` onto `𝔢(g v)`, but it preserves no parametrisation of the
  segments: at a space-like or light-like `p` it fixes the light-like directions and moves the
  points of their segments (`[a p + b n] ↦ [a p + b e^ζ n]` for a boost fixing `p`). So at such
  `p` no `Γ_p`-equivariant trivialisation `ℓ(p) × ]0, π[ ≅ HS² ∖ {±p}` exists, and charts `c × id`
  are not an HS-atlas (argued, not formalized). Here `𝔢(L)` is `L × [0, π]/∼` with the charts `[σ, t] ↦ [cos t p + sin t W(σ)]`,
  `W` a lift over a chart of `L` which is locally a `Γ_p`-translate of one lift `w` of the
  developing map, `w(s + 1) = ρ w(s)` (it exists: the lifts of a direction form an open
  half-plane, convex, and the tent average of `ρⁿ w₀(s − n)` is equivariant). Its chart changes
  are elements of `Γ_p` (the `g_ij`), and the inverse charts identify each `𝔢(U) ∖ {±p}` with an
  open set of `𝔢(L)`: the paper's quotient `⊔ 𝔢(U_i)/∼`, written in coordinates (that the two are
  the same space is argued, not formalized). The paper's atlases have one `g_ij` per overlap; the
  chart changes here are local (gx's convention, DEC-16), as a circle with holonomy needs.
* **(b) Developing data.** `Δ` (covering, developing map, lift) is a choice; `𝔢(L)` depends on it
  only up to HS-isomorphism (argued: two developing maps differ by an element of `Γ_p` after a
  lift of the covering, two equivariant lifts by a periodic positive factor and a multiple of
  `p`; not formalized). `GX.IsSingularHSSurface` quantifies over `Δ`. A question.
* **(c) « Surface »** is `GX.IsTopologicalSurface` (Hausdorff, locally `ℝ²`), OQ-104's most
  inclusive reading: the mark waits on OQ-104, as `bbsdef:hs_surface_topological_surface_endowed`'s.
* **(d) « Oriented »** adds no field: the orientation is the one the HS-structure induces on
  `Σ ∖ 𝒮` (l.621–623; `SO₀(1,2)` preserves it), which extends over a discrete `𝒮`. Orientations of
  topological surfaces are not available at this pin. A question.
* **(e) « HS-isomorphic »** at a point of `𝒮`: `SingularHSStructure.IsIso`, a homeomorphism of
  open sets which matches `𝒮` with `{p̄, −p̄}` and reads, near every regular point and in any
  charts, as an element of `SO₀(1,2)`. So the point of `𝒮` goes to an apex; a regular point may
  lie in `𝒮`, modelled on `𝔢(ℓ(q)) = HS²` (`regular_susp`). A question.
* **(f) Notation.** l.951–952 uses `p` both for the point of `𝒮 ⊂ Σ` and for the point of `HS²`
  of `Γ_p`, `ℓ(p)`; read: a `(Γ_q, ℓ(q))`-circle for some `q ∈ HS²` (`C.pt`), existentially.
* **(g) Topology.** The quotient topology of `L × [0, π]`; `L` is compact, so it is the cone
  topology at the apices (argued as gx's `GX.Susp.eq_quotTop_of_compactSpace` for one apex; not
  formalized here); `𝔢(L) ≃ₜ 𝕊²` is proved.
  The « two singular points » (l.781) are the apices; for `L = ℓ(p)` they are regular.
* **(h) Not formalized:** the `Δ`-independence (b); `bbsrem:p_p` (the types of `p̄`, `−p̄`); that
  the apices are singular when `L ≇ ℓ(p)`; l.782–783; the AdS suspension `e(Σ)` (l.627–660) and
  `bbsdef:singular_ads_spacetime_manifold` (layer L3b).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The two-apex suspension `S × [0, π] / ∼` -/

section BiSuspDef

variable (S : Type*)

/-- The relation of the two-apex suspension: `(σ, t) ∼ (σ', t')` iff they are equal, or
`t = t' = 0`, or `t = t' = π`. -/
def biSuspSetoid : Setoid (S × Icc (0 : ℝ) Real.pi) where
  r a b := a = b ∨ ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = 0) ∨
    ((a.2 : ℝ) = Real.pi ∧ (b.2 : ℝ) = Real.pi)
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, fun h => ?_, fun h1 h2 => ?_⟩
    · rcases h with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨h2, h1⟩)
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · rcases h1 with rfl | ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, h2'⟩ | ⟨h2, _⟩
        · exact Or.inr (Or.inl ⟨h1, h1'⟩)
        · exact Or.inr (Or.inl ⟨h1, h2'⟩)
        · exact absurd (h1'.symm.trans h2) Real.pi_pos.ne
      · rcases h2 with rfl | ⟨h2, _⟩ | ⟨_, h2'⟩
        · exact Or.inr (Or.inr ⟨h1, h1'⟩)
        · exact absurd (h1'.symm.trans h2) Real.pi_pos.ne'
        · exact Or.inr (Or.inr ⟨h1, h2'⟩)

/-- **The two-apex suspension** `S × [0, π] / ∼` of a space `S`, each end collapsed to a point,
with the quotient topology. For `S = L` a `(Γ_p, ℓ(p))`-circle it is the space of `𝔢(L)`
(`colI_v1.tex:774–780`): the segment `{σ} × [0, π]` is `𝔢(v)`, from `p` (`t = 0`) to `−p`
(`t = π`). -/
abbrev BiSusp : Type _ := Quotient (biSuspSetoid S)

end BiSuspDef

namespace BiSusp

variable {S : Type*} [TopologicalSpace S]

/-- The projection `S × [0, π] → BiSusp S`. -/
def mk' : S × Icc (0 : ℝ) Real.pi → BiSusp S := Quotient.mk _

/-- The point `[σ, t]`. -/
def mk (σ : S) (t : Icc (0 : ℝ) Real.pi) : BiSusp S := mk' (σ, t)

theorem mk'_eq_mk (q : S × Icc (0 : ℝ) Real.pi) : mk' q = mk q.1 q.2 := rfl

theorem mk_eq_mk {σ σ' : S} {t t' : Icc (0 : ℝ) Real.pi} :
    mk σ t = mk σ' t' ↔ (σ = σ' ∧ t = t') ∨ ((t : ℝ) = 0 ∧ (t' : ℝ) = 0) ∨
      ((t : ℝ) = Real.pi ∧ (t' : ℝ) = Real.pi) := by
  constructor
  · intro h
    rcases (Quotient.exact h : (biSuspSetoid S).r (σ, t) (σ', t')) with h | h | h
    · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨rfl, rfl⟩ | h | h)
    · rfl
    · exact Quotient.sound (Or.inr (Or.inl h))
    · exact Quotient.sound (Or.inr (Or.inr h))

theorem mk_surjective (x : BiSusp S) : ∃ σ t, mk σ t = x := by
  induction x using Quotient.inductionOn with
  | h q => exact ⟨q.1, q.2, rfl⟩

theorem continuous_mk' : Continuous (mk' : S × Icc (0 : ℝ) Real.pi → BiSusp S) :=
  continuous_quotient_mk'

/-- The height `t ∈ [0, π]` of a point. -/
def ht : BiSusp S → ℝ :=
  Quotient.lift (fun q : S × Icc (0 : ℝ) Real.pi => (q.2 : ℝ)) fun a b h => by
    rcases h with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rfl
    · exact h1.trans h2.symm
    · exact h1.trans h2.symm

@[simp] theorem ht_mk (σ : S) (t : Icc (0 : ℝ) Real.pi) : ht (mk σ t) = t := rfl

theorem continuous_ht : Continuous (ht : BiSusp S → ℝ) :=
  (continuous_subtype_val.comp continuous_snd).quotient_lift _

theorem ht_mem (x : BiSusp S) : ht x ∈ Icc (0 : ℝ) Real.pi := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  exact t.2

variable (S) in
/-- **The two apices** `{t = 0}` and `{t = π}` (`p̄` and `−p̄` of `𝔢(L)`). -/
def poles : Set (BiSusp S) := {x | ht x = 0 ∨ ht x = Real.pi}

variable (S) in
/-- The apex `{t = 0}` (`p̄`). -/
def north [Nonempty S] : BiSusp S := mk (Classical.arbitrary S) ⟨0, le_rfl, Real.pi_pos.le⟩

variable (S) in
/-- The apex `{t = π}` (`−p̄`). -/
def south [Nonempty S] : BiSusp S := mk (Classical.arbitrary S) ⟨Real.pi, Real.pi_pos.le, le_rfl⟩

theorem poles_eq [Nonempty S] : poles S = {north S, south S} := by
  ext x
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  show (t : ℝ) = 0 ∨ (t : ℝ) = Real.pi ↔ mk σ t = north S ∨ mk σ t = south S
  rw [north, south, mk_eq_mk, mk_eq_mk]
  constructor
  · rintro (h | h)
    · exact Or.inl (Or.inr (Or.inl ⟨h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))
  · rintro ((⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩) | (⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩))
    · exact Or.inl rfl
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr rfl
    · exact Or.inl h
    · exact Or.inr h

theorem north_ne_south [Nonempty S] : north S ≠ south S := by
  intro h
  have h' : (0 : ℝ) = Real.pi := congrArg ht h
  exact Real.pi_pos.ne h'

theorem isClosed_poles : IsClosed (poles S) :=
  (isClosed_eq continuous_ht continuous_const).union (isClosed_eq continuous_ht continuous_const)

theorem notMem_poles_iff {x : BiSusp S} : x ∉ poles S ↔ 0 < ht x ∧ ht x < Real.pi := by
  obtain ⟨h0, hπ⟩ := ht_mem x
  simp only [poles, mem_setOf_eq, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_le_of_ne h0 (Ne.symm h1), lt_of_le_of_ne hπ h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.ne', h2.ne⟩

/-- A function on `S × ℝ` constant on each end descends to `BiSusp S`. -/
def lift {X : Type*} (f : S → ℝ → X) (h0 : ∀ σ σ', f σ 0 = f σ' 0)
    (hπ : ∀ σ σ', f σ Real.pi = f σ' Real.pi) : BiSusp S → X :=
  Quotient.lift (fun q : S × Icc (0 : ℝ) Real.pi => f q.1 q.2) fun a b h => by
    rcases h with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rfl
    · show f a.1 a.2 = f b.1 b.2
      rw [h1, h2]; exact h0 _ _
    · show f a.1 a.2 = f b.1 b.2
      rw [h1, h2]; exact hπ _ _

@[simp] theorem lift_mk {X : Type*} (f : S → ℝ → X) (h0 : ∀ σ σ', f σ 0 = f σ' 0)
    (hπ : ∀ σ σ', f σ Real.pi = f σ' Real.pi) (σ : S) (t : Icc (0 : ℝ) Real.pi) :
    lift f h0 hπ (mk σ t) = f σ t := rfl

theorem continuous_lift {X : Type*} [TopologicalSpace X] {f : S → ℝ → X}
    (h0 : ∀ σ σ', f σ 0 = f σ' 0) (hπ : ∀ σ σ', f σ Real.pi = f σ' Real.pi)
    (hf : Continuous fun q : S × Icc (0 : ℝ) Real.pi => f q.1 q.2) : Continuous (lift f h0 hπ) :=
  hf.quotient_lift _

/-- The regular part of `S × [0, π]` over `U ⊆ S`. -/
def regSet (U : Set S) : Set (S × Icc (0 : ℝ) Real.pi) :=
  {q | q.1 ∈ U ∧ 0 < (q.2 : ℝ) ∧ (q.2 : ℝ) < Real.pi}

theorem isOpen_regSet {U : Set S} (hU : IsOpen U) : IsOpen (regSet U) := by
  exact (hU.preimage continuous_fst).inter
    ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const))

/-- A set of regular points is saturated. -/
theorem preimage_image_mk' {A : Set (S × Icc (0 : ℝ) Real.pi)} (hA : A ⊆ regSet univ) :
    mk' ⁻¹' (mk' '' A) = A := by
  ext q
  constructor
  · rintro ⟨q', hq', hqq'⟩
    rcases (Quotient.exact hqq' : (biSuspSetoid S).r q' q) with rfl | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hq'
    · exact absurd h1 (hA hq').2.1.ne'
    · exact absurd h1 (hA hq').2.2.ne
  · intro hq
    exact ⟨q, hq, rfl⟩

theorem isOpen_image_mk' {A : Set (S × Icc (0 : ℝ) Real.pi)} (hA : IsOpen A)
    (hA' : A ⊆ regSet univ) : IsOpen (mk' '' A) := by
  refine isOpen_coinduced.2 ?_
  show IsOpen (mk' ⁻¹' (mk' '' A))
  rw [preimage_image_mk' hA']
  exact hA

/-- Near a regular point, the quotient map is open: `𝓝 [σ, t] = map mk' (𝓝 (σ, t))`. -/
theorem nhds_mk {q : S × Icc (0 : ℝ) Real.pi} (hq : q ∈ regSet univ) :
    𝓝 (mk' q) = map mk' (𝓝 q) := by
  refine le_antisymm (fun U hU => ?_) continuous_mk'.continuousAt
  have hU' : mk' ⁻¹' U ∈ 𝓝 q := hU
  set B := interior (mk' ⁻¹' U) ∩ regSet univ
  have hB : IsOpen B := isOpen_interior.inter (isOpen_regSet isOpen_univ)
  have hqB : q ∈ B := ⟨mem_interior_iff_mem_nhds.2 hU', hq⟩
  refine mem_of_superset ((isOpen_image_mk' hB inter_subset_right).mem_nhds ⟨q, hqB, rfl⟩) ?_
  rintro _ ⟨q', hq', rfl⟩
  exact (interior_subset hq'.1 : q' ∈ mk' ⁻¹' U)

theorem mk'_injOn_regSet : InjOn (mk' : S × Icc (0 : ℝ) Real.pi → BiSusp S) (regSet univ) := by
  intro a ha b _ h
  rcases (Quotient.exact h : (biSuspSetoid S).r a b) with h | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h
  · exact absurd h1 ha.2.1.ne'
  · exact absurd h1 ha.2.2.ne

theorem image_mk'_regSet_univ : mk' '' regSet (univ : Set S) = (poles S)ᶜ := by
  ext x
  rw [mem_compl_iff, notMem_poles_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.2.1, hq.2.2⟩
  · intro h
    obtain ⟨σ, t, rfl⟩ := mk_surjective x
    exact ⟨(σ, t), ⟨trivial, h⟩, rfl⟩

end BiSusp

/-! ## 2. `BiSusp L` is the sphere when `L` is a circle -/

section Sphere

variable {S : Type*} [TopologicalSpace S]

theorem norm_cos_sin_mul (t : ℝ) (z : Circle) :
    ‖(WithLp.toLp 2 (Real.cos t, (Real.sin t : ℂ) * (z : ℂ)) : Euc3)‖ = 1 := by
  have h := norm_toLp_sq (W := ℂ) (Real.cos t) ((Real.sin t : ℂ) * (z : ℂ))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one, sq_abs,
    Real.cos_sq_add_sin_sq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The point `(cos t, sin t · φ(σ))` of `𝕊² ⊂ ℝ ⊕ ℂ`. -/
def sphPt (φ : S ≃ₜ Circle) (σ : S) (t : ℝ) : Sph2 :=
  ⟨WithLp.toLp 2 (Real.cos t, (Real.sin t : ℂ) * (φ σ : ℂ)),
    mem_sphere_zero_iff_norm.2 (norm_cos_sin_mul t (φ σ))⟩

theorem coe_sphPt (φ : S ≃ₜ Circle) (σ : S) (t : ℝ) :
    (sphPt φ σ t : Euc3) = WithLp.toLp 2 (Real.cos t, (Real.sin t : ℂ) * (φ σ : ℂ)) := rfl

/-- `BiSusp S → 𝕊²`, `[σ, t] ↦ (cos t, sin t · φ(σ))`. -/
def BiSusp.toSph2 (φ : S ≃ₜ Circle) : BiSusp S → Sph2 :=
  BiSusp.lift (sphPt φ) (fun _ _ => Subtype.ext (by simp [coe_sphPt]))
    (fun _ _ => Subtype.ext (by simp [coe_sphPt]))

theorem BiSusp.toSph2_mk (φ : S ≃ₜ Circle) (σ : S) (t : Icc (0 : ℝ) Real.pi) :
    BiSusp.toSph2 φ (BiSusp.mk σ t) = sphPt φ σ t := rfl

theorem BiSusp.continuous_toSph2 (φ : S ≃ₜ Circle) : Continuous (BiSusp.toSph2 φ) := by
  refine BiSusp.continuous_lift _ _ ?_
  refine Continuous.subtype_mk ?_ _
  refine (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp (Continuous.prodMk ?_ ?_)
  · exact Real.continuous_cos.comp (continuous_subtype_val.comp continuous_snd)
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_subtype_val.comp continuous_snd))).mul
      (RP1.continuous_coe.comp (φ.continuous.comp continuous_fst))

/-- On `[0, π]`, `sin t = 0` only at the ends. -/
theorem eq_zero_or_eq_pi_of_sin_eq_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi)
    (h : Real.sin t = 0) : t = 0 ∨ t = Real.pi := by
  rcases eq_or_lt_of_le ht.2 with hπ | hπ
  · exact Or.inr hπ
  · rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact Or.inl h0.symm
    · exact absurd h (Real.sin_pos_of_pos_of_lt_pi h0 hπ).ne'

theorem BiSusp.toSph2_bijective (φ : S ≃ₜ Circle) : Function.Bijective (BiSusp.toSph2 φ) := by
  refine ⟨fun x x' h => ?_, fun y => ?_⟩
  · obtain ⟨σ, t, rfl⟩ := BiSusp.mk_surjective x
    obtain ⟨σ', t', rfl⟩ := BiSusp.mk_surjective x'
    have h1 : Real.cos t = Real.cos t' := congrArg (fun y : Sph2 => (y : Euc3).fst) h
    have h2 : (Real.sin t : ℂ) * (φ σ : ℂ) = (Real.sin t' : ℂ) * (φ σ' : ℂ) :=
      congrArg (fun y : Sph2 => (y : Euc3).snd) h
    have htt : (t : ℝ) = t' := Real.injOn_cos t.2 t'.2 h1
    rw [BiSusp.mk_eq_mk]
    by_cases hs : Real.sin t = 0
    · rcases eq_zero_or_eq_pi_of_sin_eq_zero t.2 hs with h0 | hπ
      · exact Or.inr (Or.inl ⟨h0, htt ▸ h0⟩)
      · exact Or.inr (Or.inr ⟨hπ, htt ▸ hπ⟩)
    · rw [← htt] at h2
      refine Or.inl ⟨φ.injective (Circle.ext ?_), Subtype.ext htt⟩
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hs) h2
  · set a := (y : Euc3).fst
    set z := (y : Euc3).snd
    have hn : a ^ 2 + ‖z‖ ^ 2 = 1 := by
      have h := WithLp.prod_norm_eq_of_L2 (y : Euc3)
      rw [norm_raySphere] at h
      have h' := Real.sqrt_eq_one.1 h.symm
      rwa [Real.norm_eq_abs, sq_abs] at h'
    have ha1 : -1 ≤ a := by nlinarith [norm_nonneg z]
    have ha2 : a ≤ 1 := by nlinarith [norm_nonneg z]
    refine ⟨BiSusp.mk (φ.symm (Circle.exp (Complex.arg z)))
      ⟨Real.arccos a, Real.arccos_nonneg a, Real.arccos_le_pi a⟩, Subtype.ext ?_⟩
    rw [BiSusp.toSph2_mk, coe_sphPt]
    show WithLp.toLp 2 (Real.cos (Real.arccos a), (Real.sin (Real.arccos a) : ℂ) *
      (φ (φ.symm (Circle.exp (Complex.arg z))) : ℂ)) = WithLp.toLp 2 (a, z)
    have hsin : Real.sin (Real.arccos a) = ‖z‖ := by
      rw [Real.sin_arccos, show 1 - a ^ 2 = ‖z‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg z)]
    rw [Real.cos_arccos ha1 ha2, hsin, Homeomorph.apply_symm_apply, Circle.coe_exp,
      Complex.norm_mul_exp_arg_mul_I]

/-- **The two-apex suspension of a circle is the sphere `𝕊²`** (`colI_v1.tex:779`, « the resulting
space `𝔢(L)` is topologically a sphere »). -/
def BiSusp.homeomorphSph2 (φ : S ≃ₜ Circle) : BiSusp S ≃ₜ Sph2 :=
  haveI : CompactSpace S := φ.symm.compactSpace
  (BiSusp.continuous_toSph2 φ).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (BiSusp.toSph2_bijective φ))

/-- `BiSusp L ≃ₜ HS²` for a circle `L`. -/
def BiSusp.homeomorphHS (φ : S ≃ₜ Circle) : BiSusp S ≃ₜ HS 2 :=
  (BiSusp.homeomorphSph2 φ).trans hs2HomeomorphSph2.symm

/-- A space homeomorphic to a topological surface is one. -/
theorem IsTopologicalSurface.of_homeomorph {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (hN : IsTopologicalSurface N) (h : M ≃ₜ N) : IsTopologicalSurface M := by
  haveI := hN.t2Space
  refine ⟨h.symm.t2Space, fun x => ?_⟩
  obtain ⟨e, he⟩ := hN.exists_chart (h x)
  refine ⟨h.toOpenPartialHomeomorph.trans e, ?_⟩
  rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
  exact ⟨trivial, he⟩

theorem BiSusp.t2Space_of_homeomorph (φ : S ≃ₜ Circle) : T2Space (BiSusp S) :=
  (BiSusp.homeomorphHS φ).symm.t2Space

theorem BiSusp.isTopologicalSurface (φ : S ≃ₜ Circle) : IsTopologicalSurface (BiSusp S) :=
  isTopologicalSurface_hs2.of_homeomorph (BiSusp.homeomorphHS φ)

end Sphere

/-! ## 3. The segments `𝔢(v) = [−p, p]` of `HS²` -/

section Arc

variable (p : HS 2)

/-- `cos t · p + sin t · w`. -/
def arcVec (w : 𝕄) (t : ℝ) : 𝕄 := Real.cos t • (p : 𝕄) + Real.sin t • w

/-- **The point at angle `t` on the half projective line from `p` through `w` to `−p`**:
the ray of `cos t · p + sin t · w`, `t ∈ [0, π]` (`p` at `t = 0`, `−p` at `t = π`). -/
def arcPt (w : 𝕄) (t : ℝ) : HS 2 := rayNormalize p (arcVec p w t)

theorem tpMk_self : tpMk p (p : 𝕄) = 0 :=
  (tpMk_eq_zero_iff p).2 ⟨1, (one_smul ℝ _).symm⟩

theorem tpMk_arcVec (w : 𝕄) (t : ℝ) : tpMk p (arcVec p w t) = Real.sin t • tpMk p w := by
  show Submodule.Quotient.mk _ = _
  rw [arcVec, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
  rw [show (Submodule.Quotient.mk (p : 𝕄) : TpHS p) = 0 from tpMk_self p, smul_zero, zero_add]

theorem arcVec_ne_zero {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) : arcVec p w t ≠ 0 := by
  intro h
  by_cases hs : Real.sin t = 0
  · have hc : Real.cos t ≠ 0 := by
      intro hc
      have := Real.sin_sq_add_cos_sq t
      rw [hs, hc] at this
      norm_num at this
    rw [arcVec, hs, zero_smul, add_zero] at h
    exact (smul_ne_zero hc (raySphere_ne_zero p)) h
  · have h' := tpMk_arcVec p w t
    rw [h] at h'
    exact (smul_ne_zero hs hw) (h'.symm.trans (Submodule.Quotient.mk_zero _))

theorem arcPt_zero (w : 𝕄) : arcPt p w 0 = p := by
  rw [arcPt, arcVec, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero,
    rayNormalize_raySphere]

theorem arcPt_pi (w : 𝕄) : arcPt p w Real.pi = -p := by
  rw [arcPt, arcVec, Real.cos_pi, Real.sin_pi, neg_one_smul, zero_smul, add_zero,
    ← coe_neg_sphere, rayNormalize_raySphere]

theorem tpMk_ne_zero_iff {y : HS 2} : tpMk p (y : 𝕄) ≠ 0 ↔ y ≠ p ∧ y ≠ -p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hyp
      rw [hyp] at h
      exact h (tpMk_self p)
    · intro hyp
      apply h
      rw [hyp, coe_neg_sphere]
      exact (tpMk_eq_zero_iff p).2 ⟨-1, by rw [neg_one_smul]⟩
  · rintro ⟨h1, h2⟩ h
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h
    have hn : |c| = 1 := by
      have := norm_raySphere y
      rw [hc, norm_smul, norm_raySphere, mul_one, Real.norm_eq_abs] at this
      exact this
    rcases (abs_eq zero_le_one).1 hn with rfl | rfl
    · exact h1 (Subtype.ext (by rw [hc, one_smul]))
    · exact h2 (Subtype.ext (by rw [hc, coe_neg_sphere, neg_one_smul]))

theorem neg_ne_self_hs : -p ≠ p := by
  intro h
  have h' : -(p : 𝕄) = p := by rw [← coe_neg_sphere, h]
  have h2 : (2 : ℝ) • (p : 𝕄) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h']
    exact neg_add_cancel _
  exact raySphere_ne_zero p ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

theorem tpMk_arcPt {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) :
    tpMk p (arcPt p w t : 𝕄) = (‖arcVec p w t‖⁻¹ * Real.sin t) • tpMk p w := by
  rw [arcPt, coe_rayNormalize _ (arcVec_ne_zero p hw t)]
  show Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.mk_smul]
  change ‖arcVec p w t‖⁻¹ • tpMk p (arcVec p w t) = _
  rw [tpMk_arcVec, smul_smul]

theorem tpMk_arcPt_ne_zero {w : 𝕄} (hw : tpMk p w ≠ 0) {t : ℝ} (ht : 0 < t) (ht' : t < Real.pi) :
    tpMk p (arcPt p w t : 𝕄) ≠ 0 := by
  rw [tpMk_arcPt p hw]
  exact smul_ne_zero (mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 (arcVec_ne_zero p hw t)))
    (Real.sin_pos_of_pos_of_lt_pi ht ht').ne') hw

theorem dirOf_arcPt {w : 𝕄} (hw : tpMk p w ≠ 0) {t : ℝ} (ht : 0 < t) (ht' : t < Real.pi) :
    dirOf p (arcPt p w t : 𝕄) = dirOf p w := by
  rw [dirOf_congr p (v := (arcPt p w t : 𝕄)) (w := (‖arcVec p w t‖⁻¹ * Real.sin t) • w)
    (by rw [tpMk_arcPt p hw]; exact (Submodule.Quotient.mk_smul _ _ _).symm),
    dirOf_smul_of_pos p hw (mul_pos (inv_pos.2 (norm_pos_iff.2 (arcVec_ne_zero p hw t)))
      (Real.sin_pos_of_pos_of_lt_pi ht ht'))]

theorem continuousAt_arcPt {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) :
    ContinuousAt (fun q : 𝕄 × ℝ => arcPt p q.1 q.2) (w, t) := by
  have hc : Continuous (fun q : 𝕄 × ℝ => arcVec p q.1 q.2) :=
    ((Real.continuous_cos.comp continuous_snd).smul continuous_const).add
      ((Real.continuous_sin.comp continuous_snd).smul continuous_fst)
  exact (continuousAt_rayNormalize p (arcVec_ne_zero p hw t)).comp (x := (w, t)) hc.continuousAt

/-- `Γ_p` moves the segments: `A · [cos t p + sin t w] = [cos t p + sin t A w]`. -/
theorem smul_arcPt (A : GammaP p) {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) :
    (A : Causal.Flat.lorentz 2) • arcPt p w t =
      arcPt p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) t := by
  set B : 𝕄 ≃ₗ[ℝ] 𝕄 := ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
  have hBp : B p = p := A.2
  have hv := arcVec_ne_zero p hw t
  have hBv : B (arcVec p w t) = arcVec p (B w) t := by
    simp only [arcVec, map_add, map_smul, hBp]
  have hBv0 : arcVec p (B w) t ≠ 0 := hBv ▸ (LinearEquiv.map_ne_zero_iff B).2 hv
  apply Subtype.ext
  rw [coe_hs_smul, arcPt, arcPt, coe_rayNormalize _ hv, coe_rayNormalize _ hBv0]
  change ‖B (‖arcVec p w t‖⁻¹ • arcVec p w t)‖⁻¹ • B (‖arcVec p w t‖⁻¹ • arcVec p w t) = _
  rw [map_smul, hBv, norm_smul, norm_inv, norm_norm, smul_smul]
  congr 1
  have h1 : ‖arcVec p w t‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have h2 : ‖arcVec p (B w) t‖ ≠ 0 := norm_ne_zero_iff.2 hBv0
  field_simp

theorem tpMk_gammaP (A : GammaP p) (w : 𝕄) :
    tpMk p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) = GammaP.tangent A (tpMk p w) := rfl

theorem dirOf_gammaP (A : GammaP p) {w : 𝕄} (hw : tpMk p w ≠ 0) :
    dirOf p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) = A • dirOf p w := by
  have hw' : tpMk p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) ≠ 0 := by
    rw [tpMk_gammaP]
    exact (LinearEquiv.map_ne_zero_iff _).2 hw
  apply Subtype.ext
  rw [coe_dirOf p hw', gammaP_smul_def, coe_linRaySmul, coe_dirOf p hw, tpMk_gammaP, map_smul,
    norm_smul, norm_inv, norm_norm, smul_smul]
  congr 1
  have h1 : ‖tpMk p w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have h2 : ‖GammaP.tangent A (tpMk p w)‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((LinearEquiv.map_ne_zero_iff _).2 hw)
  field_simp

/-- A continuous linear form with `λ(p) = 1` (Hahn–Banach; any one does). -/
def hsDual : 𝕄 →L[ℝ] ℝ :=
  (exists_dual_vector ℝ (p : 𝕄) (by rw [norm_raySphere]; exact one_ne_zero)).choose

theorem hsDual_self : hsDual p (p : 𝕄) = 1 := by
  have h := (exists_dual_vector ℝ (p : 𝕄)
    (by rw [norm_raySphere]; exact one_ne_zero)).choose_spec.2
  exact h.trans (by rw [norm_raySphere]; simp)

/-- The ratio `b` with `[y] = b [w]` in `T_p HS²`. -/
def arcRatio (y w : 𝕄) : ℝ := ‖tpMk p y‖ / ‖tpMk p w‖

/-- **The angle of `y` on the segment through `w`**: writing `y = a p + b w` (`b > 0`),
`arg (a + b i) ∈ ]0, π[`. -/
def arcAngle (y w : 𝕄) : ℝ :=
  Complex.arg (((hsDual p y - arcRatio p y w * hsDual p w : ℝ) : ℂ) +
    ((arcRatio p y w : ℝ) : ℂ) * Complex.I)

theorem continuousAt_arcAngle {y w : 𝕄} (hy : tpMk p y ≠ 0) (hw : tpMk p w ≠ 0) :
    ContinuousAt (fun q : 𝕄 × 𝕄 => arcAngle p q.1 q.2) (y, w) := by
  have hr : ContinuousAt (fun q : 𝕄 × 𝕄 => arcRatio p q.1 q.2) (y, w) :=
    ((continuous_tpMk p).comp continuous_fst).norm.continuousAt.div
      ((continuous_tpMk p).comp continuous_snd).norm.continuousAt (norm_ne_zero_iff.2 hw)
  have hz : ContinuousAt (fun q : 𝕄 × 𝕄 => ((hsDual p q.1 - arcRatio p q.1 q.2 * hsDual p q.2 : ℝ) : ℂ) +
      ((arcRatio p q.1 q.2 : ℝ) : ℂ) * Complex.I) (y, w) := by
    refine (Complex.continuous_ofReal.continuousAt.comp ?_).add
      ((Complex.continuous_ofReal.continuousAt.comp hr).mul continuousAt_const)
    exact ((hsDual p).continuous.comp continuous_fst).continuousAt.sub
      (hr.mul ((hsDual p).continuous.comp continuous_snd).continuousAt)
  refine (Complex.continuousAt_arg ?_).comp hz
  rw [Complex.mem_slitPlane_iff]
  right
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  exact (div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hw)).ne'

theorem arcAngle_mem {y w : 𝕄} (hy : tpMk p y ≠ 0) (hw : tpMk p w ≠ 0) :
    0 < arcAngle p y w ∧ arcAngle p y w < Real.pi := by
  have hr : 0 < arcRatio p y w := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hw)
  unfold arcAngle
  set z : ℂ := ((hsDual p y - arcRatio p y w * hsDual p w : ℝ) : ℂ) +
    ((arcRatio p y w : ℝ) : ℂ) * Complex.I
  have him : z.im = arcRatio p y w := by simp [z]
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 (him ▸ hr.le)) (fun h => ?_),
    Complex.arg_lt_pi_iff.2 (Or.inr (him ▸ hr.ne'))⟩
  have := (Complex.arg_eq_zero_iff.1 h.symm).2
  rw [him] at this
  exact hr.ne' this

theorem arcPt_arcAngle {y : HS 2} {w : 𝕄} (hy : tpMk p (y : 𝕄) ≠ 0) (hw : tpMk p w ≠ 0)
    (hd : dirOf p (y : 𝕄) = dirOf p w) : arcPt p w (arcAngle p y w) = y := by
  have hr : 0 < arcRatio p y w := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hw)
  have h1 : ‖tpMk p (y : 𝕄)‖⁻¹ • tpMk p (y : 𝕄) = ‖tpMk p w‖⁻¹ • tpMk p w := by
    have := congrArg (fun σ : Link p => (σ : TpHS p)) hd
    simpa only [coe_dirOf p hy, coe_dirOf p hw] using this
  have h2 : tpMk p (y : 𝕄) = arcRatio p y w • tpMk p w := by
    have := congrArg (‖tpMk p (y : 𝕄)‖ • ·) h1
    simp only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hy), one_smul] at this
    rw [this, arcRatio, div_eq_mul_inv]
  obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 (show tpMk p ((y : 𝕄) - arcRatio p y w • w) = 0 by
    show Submodule.Quotient.mk _ = _
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
    change tpMk p (y : 𝕄) - arcRatio p y w • tpMk p w = 0
    rw [h2, sub_self])
  have ha : hsDual p y - arcRatio p y w * hsDual p w = c := by
    have := congrArg (hsDual p) hc
    rw [map_sub, map_smul, map_smul, hsDual_self, smul_eq_mul, smul_eq_mul, mul_one] at this
    exact this
  have hy' : (y : 𝕄) = c • (p : 𝕄) + arcRatio p y w • w := by
    rw [← hc]
    abel
  unfold arcPt arcAngle
  rw [ha]
  set z : ℂ := (c : ℂ) + ((arcRatio p y w : ℝ) : ℂ) * Complex.I
  have hzre : z.re = c := by simp [z]
  have hzim : z.im = arcRatio p y w := by simp [z]
  have hz : z ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hzim
    exact hr.ne' hzim.symm
  have hv : arcVec p w (Complex.arg z) = ‖z‖⁻¹ • (y : 𝕄) := by
    rw [arcVec, Complex.cos_arg hz, Complex.sin_arg, hzre, hzim]
    conv_rhs => rw [hy']
    rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  rw [hv, rayNormalize_smul_of_pos p (raySphere_ne_zero y) (inv_pos.2 (norm_pos_iff.2 hz)),
    rayNormalize_raySphere]

theorem arcAngle_arcPt {w : 𝕄} (hw : tpMk p w ≠ 0) {t : ℝ} (ht : 0 < t) (ht' : t < Real.pi) :
    arcAngle p (arcPt p w t) w = t := by
  have hv := arcVec_ne_zero p hw t
  have hs := Real.sin_pos_of_pos_of_lt_pi ht ht'
  set k := ‖arcVec p w t‖⁻¹ with hk_def
  have hk : 0 < k := inv_pos.2 (norm_pos_iff.2 hv)
  have hy : (arcPt p w t : 𝕄) = k • arcVec p w t := coe_rayNormalize _ hv
  have hr : arcRatio p (arcPt p w t) w = k * Real.sin t := by
    rw [arcRatio, tpMk_arcPt p hw, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hk hs),
      mul_div_assoc, div_self (norm_ne_zero_iff.2 hw), mul_one]
  have ha : hsDual p (arcPt p w t) - arcRatio p (arcPt p w t) w * hsDual p w =
      k * Real.cos t := by
    rw [hr, hy, map_smul, arcVec, map_add, map_smul, map_smul, hsDual_self]
    simp only [smul_eq_mul]
    ring
  unfold arcAngle
  rw [ha, hr]
  rw [show ((k * Real.cos t : ℝ) : ℂ) + ((k * Real.sin t : ℝ) : ℂ) * Complex.I =
      (k : ℂ) * (Complex.cos t + Complex.sin t * Complex.I) by push_cast; ring]
  rw [Complex.arg_real_mul _ hk, Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], ht'.le⟩]

theorem mem_image_arcPt_iff {w : 𝕄} (hw : tpMk p w ≠ 0) {y : HS 2} :
    y ∈ arcPt p w '' Icc 0 Real.pi ↔
      y = p ∨ y = -p ∨ (tpMk p (y : 𝕄) ≠ 0 ∧ dirOf p (y : 𝕄) = dirOf p w) := by
  constructor
  · rintro ⟨t, ⟨ht0, htπ⟩, rfl⟩
    rcases eq_or_lt_of_le ht0 with rfl | ht0
    · exact Or.inl (arcPt_zero p w)
    rcases eq_or_lt_of_le htπ with rfl | htπ
    · exact Or.inr (Or.inl (arcPt_pi p w))
    exact Or.inr (Or.inr ⟨tpMk_arcPt_ne_zero p hw ht0 htπ, dirOf_arcPt p hw ht0 htπ⟩)
  · rintro (h | h | ⟨hy, hd⟩)
    · exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, (arcPt_zero p w).trans h.symm⟩
    · exact ⟨Real.pi, ⟨Real.pi_pos.le, le_rfl⟩, (arcPt_pi p w).trans h.symm⟩
    · obtain ⟨h0, hπ⟩ := arcAngle_mem p hy hw
      exact ⟨arcAngle p y w, ⟨h0.le, hπ.le⟩, arcPt_arcAngle p hy hw hd⟩

/-- **`𝔢(v)`, the closed segment `[−p, p]` of the projective ray defined by `v`**
(`colI_v1.tex:776–777`): the points `[cos t p + sin t w]`, `t ∈ [0, π]`, `w` a lift of `v`. -/
def suspSeg (v : Link p) : Set (HS 2) := arcPt p (liftT p v) '' Icc 0 Real.pi

theorem mem_suspSeg_iff {v : Link p} {y : HS 2} :
    y ∈ suspSeg p v ↔ y = p ∨ y = -p ∨ (tpMk p (y : 𝕄) ≠ 0 ∧ dirOf p (y : 𝕄) = v) := by
  rw [suspSeg, mem_image_arcPt_iff p (tpMk_liftT_ne_zero p v), dirOf_eq p (tpMk_liftT p v)]

/-- The segment does not depend on the lift: any `w` with `[w] = v` traces it. -/
theorem image_arcPt_eq_suspSeg {w : 𝕄} (hw : tpMk p w ≠ 0) :
    arcPt p w '' Icc 0 Real.pi = suspSeg p (dirOf p w) := by
  ext y
  rw [mem_image_arcPt_iff p hw, mem_suspSeg_iff]

/-- `𝔢(ℓ(p))` covers `HS²`: every point lies on a segment. -/
theorem iUnion_suspSeg : ⋃ v : Link p, suspSeg p v = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
  by_cases h1 : y = p
  · exact ⟨Classical.arbitrary _, (mem_suspSeg_iff p).2 (Or.inl h1)⟩
  by_cases h2 : y = -p
  · exact ⟨Classical.arbitrary _, (mem_suspSeg_iff p).2 (Or.inr (Or.inl h2))⟩
  exact ⟨dirOf p (y : 𝕄), (mem_suspSeg_iff p).2
    (Or.inr (Or.inr ⟨(tpMk_ne_zero_iff p).2 ⟨h1, h2⟩, rfl⟩))⟩

end Arc

/-! ## 4. Cone charts -/

section ConeChart

variable {p : HS 2} {L : Type*} [TopologicalSpace L]

/-- `W` is a lift over the chart `c` of `L`: `[W σ] = c σ` in `ℓ(p)`, `W` continuous. -/
structure IsConeLift (c : OpenPartialHomeomorph L (Link p)) (W : L → 𝕄) : Prop where
  continuousOn : ContinuousOn W c.source
  tpMk_ne : ∀ σ ∈ c.source, tpMk p (W σ) ≠ 0
  dirOf_eq : ∀ σ ∈ c.source, dirOf p (W σ) = c σ

theorem coe_projIcc_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    (projIcc 0 Real.pi Real.pi_pos.le x : ℝ) = x := by
  rw [projIcc_of_mem _ hx]

variable (p) in
/-- `[σ, t] ↦ [cos t p + sin t W(σ)]`, constant on the ends. -/
def suspMap (W : L → 𝕄) : BiSusp L → HS 2 :=
  BiSusp.lift (fun σ t => arcPt p (W σ) t) (fun _ _ => by rw [arcPt_zero, arcPt_zero])
    (fun _ _ => by rw [arcPt_pi, arcPt_pi])

theorem suspMap_mk (W : L → 𝕄) (σ : L) (t : Icc (0 : ℝ) Real.pi) :
    suspMap p W (BiSusp.mk σ t) = arcPt p (W σ) t := rfl

/-- **The cone chart over a chart `c` of `L`** with lift `W`: `[σ, t] ↦ [cos t p + sin t W(σ)]`
on the regular points over `c.source`, onto the union of the open segments `𝔢(v) ∖ {±p}`,
`v ∈ c.target` (the paper's `e(U) ∖ {p}`, `colI_v1.tex:636`). -/
def suspChart (c : OpenPartialHomeomorph L (Link p)) (W : L → 𝕄) (hW : IsConeLift c W) :
    OpenPartialHomeomorph (BiSusp L) (HS 2) where
  toFun := suspMap p W
  invFun y := BiSusp.mk (c.symm (dirOf p (y : 𝕄)))
    (projIcc 0 Real.pi Real.pi_pos.le (arcAngle p y (W (c.symm (dirOf p (y : 𝕄))))))
  source := BiSusp.mk' '' BiSusp.regSet c.source
  target := {y | tpMk p (y : 𝕄) ≠ 0 ∧ dirOf p (y : 𝕄) ∈ c.target}
  map_source' := by
    rintro _ ⟨⟨σ, t⟩, ⟨hσ, ht0, htπ⟩, rfl⟩
    show tpMk p (arcPt p (W σ) t : 𝕄) ≠ 0 ∧ dirOf p (arcPt p (W σ) t : 𝕄) ∈ c.target
    refine ⟨tpMk_arcPt_ne_zero p (hW.tpMk_ne σ hσ) ht0 htπ, ?_⟩
    rw [dirOf_arcPt p (hW.tpMk_ne σ hσ) ht0 htπ, hW.dirOf_eq σ hσ]
    exact c.map_source hσ
  map_target' := by
    rintro y ⟨hy, hyc⟩
    have hσ := c.map_target hyc
    obtain ⟨h0, hπ⟩ := arcAngle_mem p hy (hW.tpMk_ne _ hσ)
    refine ⟨(c.symm (dirOf p (y : 𝕄)), projIcc 0 Real.pi Real.pi_pos.le
      (arcAngle p y (W (c.symm (dirOf p (y : 𝕄)))))), ⟨hσ, ?_, ?_⟩, rfl⟩
    · rw [coe_projIcc_of_mem ⟨h0.le, hπ.le⟩]
      exact h0
    · rw [coe_projIcc_of_mem ⟨h0.le, hπ.le⟩]
      exact hπ
  left_inv' := by
    rintro _ ⟨⟨σ, t⟩, ⟨hσ, ht0, htπ⟩, rfl⟩
    have hW0 := hW.tpMk_ne σ hσ
    show BiSusp.mk (c.symm (dirOf p (arcPt p (W σ) t : 𝕄))) (projIcc 0 Real.pi Real.pi_pos.le
      (arcAngle p (arcPt p (W σ) t) (W (c.symm (dirOf p (arcPt p (W σ) t : 𝕄)))))) =
        BiSusp.mk' (σ, t)
    rw [dirOf_arcPt p hW0 ht0 htπ, hW.dirOf_eq σ hσ, c.left_inv hσ, arcAngle_arcPt p hW0 ht0 htπ,
      projIcc_of_mem _ t.2]
    rfl
  right_inv' := by
    rintro y ⟨hy, hyc⟩
    have hσ := c.map_target hyc
    have hW0 := hW.tpMk_ne _ hσ
    have hd : dirOf p (y : 𝕄) = dirOf p (W (c.symm (dirOf p (y : 𝕄)))) := by
      rw [hW.dirOf_eq _ hσ, c.right_inv hyc]
    obtain ⟨h0, hπ⟩ := arcAngle_mem p hy hW0
    show arcPt p (W (c.symm (dirOf p (y : 𝕄)))) (projIcc 0 Real.pi Real.pi_pos.le
      (arcAngle p y (W (c.symm (dirOf p (y : 𝕄))))) : ℝ) = y
    rw [coe_projIcc_of_mem ⟨h0.le, hπ.le⟩]
    exact arcPt_arcAngle p hy hW0 hd
  open_source := by
    exact BiSusp.isOpen_image_mk' (BiSusp.isOpen_regSet c.open_source) fun q hq => ⟨trivial, hq.2⟩
  open_target := by
    have hO : IsOpen {y : HS 2 | tpMk p (y : 𝕄) ≠ 0} :=
      isOpen_ne_fun ((continuous_tpMk p).comp continuous_subtype_val) continuous_const
    have hdc : ContinuousOn (fun y : HS 2 => dirOf p (y : 𝕄)) {y : HS 2 | tpMk p (y : 𝕄) ≠ 0} :=
      (continuousOn_dirOf p).comp continuous_subtype_val.continuousOn fun y hy => hy
    exact hdc.isOpen_inter_preimage hO c.open_target
  continuousOn_toFun := by
    rintro _ ⟨q, hq, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hq' : q ∈ BiSusp.regSet univ := ⟨trivial, hq.2⟩
    show Tendsto (suspMap p W) (𝓝 (BiSusp.mk' q)) _
    rw [BiSusp.nhds_mk hq', tendsto_map'_iff]
    have hWc : ContinuousAt W q.1 := hW.continuousOn.continuousAt (c.open_source.mem_nhds hq.1)
    exact (continuousAt_arcPt p (hW.tpMk_ne _ hq.1) q.2).comp
      (f := fun q : L × Icc (0 : ℝ) Real.pi => (W q.1, (q.2 : ℝ)))
      ((hWc.comp continuousAt_fst).prodMk (continuous_subtype_val.comp continuous_snd).continuousAt)
  continuousOn_invFun := by
    rintro y ⟨hy, hyc⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hd : ContinuousAt (fun y : HS 2 => dirOf p (y : 𝕄)) y :=
      ((continuousOn_dirOf p).continuousAt
        ((isOpen_ne_fun (continuous_tpMk p) continuous_const).mem_nhds hy)).comp
        continuous_subtype_val.continuousAt
    have hσ : ContinuousAt (fun y : HS 2 => c.symm (dirOf p (y : 𝕄))) y :=
      (c.continuousAt_symm hyc).comp (f := fun y : HS 2 => dirOf p (y : 𝕄)) hd
    have hσ' := c.map_target hyc
    have hW' : ContinuousAt (fun y : HS 2 => W (c.symm (dirOf p (y : 𝕄)))) y :=
      (hW.continuousOn.continuousAt (c.open_source.mem_nhds hσ')).comp
        (f := fun y : HS 2 => c.symm (dirOf p (y : 𝕄))) hσ
    have hA : ContinuousAt (fun y : HS 2 => arcAngle p y (W (c.symm (dirOf p (y : 𝕄))))) y :=
      (continuousAt_arcAngle p hy (hW.tpMk_ne _ hσ')).comp
        (f := fun y : HS 2 => ((y : 𝕄), W (c.symm (dirOf p (y : 𝕄)))))
        (continuous_subtype_val.continuousAt.prodMk hW')
    exact BiSusp.continuous_mk'.continuousAt.comp
      (f := fun y : HS 2 => (c.symm (dirOf p (y : 𝕄)), projIcc 0 Real.pi Real.pi_pos.le
        (arcAngle p y (W (c.symm (dirOf p (y : 𝕄)))))))
      (hσ.prodMk ((continuous_projIcc).continuousAt.comp hA))

theorem suspChart_apply {c : OpenPartialHomeomorph L (Link p)} {W : L → 𝕄} (hW : IsConeLift c W)
    (x : BiSusp L) : suspChart c W hW x = suspMap p W x := rfl

theorem suspChart_source {c : OpenPartialHomeomorph L (Link p)} {W : L → 𝕄}
    (hW : IsConeLift c W) : (suspChart c W hW).source = BiSusp.mk' '' BiSusp.regSet c.source :=
  rfl

/-- **The segment over `σ` is `𝔢(c σ)`**: `t ↦ [σ, t]` followed by the cone chart traces the
segment `[−p, p]` of `c σ` (`colI_v1.tex:776–777`). -/
theorem range_suspMap_mk {c : OpenPartialHomeomorph L (Link p)} {W : L → 𝕄} (hW : IsConeLift c W)
    {σ : L} (hσ : σ ∈ c.source) :
    range (fun t => suspMap p W (BiSusp.mk σ t)) = suspSeg p (c σ) := by
  have : range (fun t : Icc (0 : ℝ) Real.pi => suspMap p W (BiSusp.mk σ t)) =
      arcPt p (W σ) '' Icc 0 Real.pi := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [this, image_arcPt_eq_suspSeg p (hW.tpMk_ne σ hσ), hW.dirOf_eq σ hσ]

/-- The cone maps send the apices to `p` and `−p` (`p̄ ↦ p`, `−p̄ ↦ −p`). -/
theorem suspMap_north [Nonempty L] (W : L → 𝕄) : suspMap p W (BiSusp.north L) = p :=
  arcPt_zero p _

theorem suspMap_south [Nonempty L] (W : L → 𝕄) : suspMap p W (BiSusp.south L) = -p :=
  arcPt_pi p _

/-- **The target of a cone chart is the paper's `e(U) ∖ {p}`** (`colI_v1.tex:636`, here with both
apices): the union of the segments `𝔢(v)`, `v ∈ c.target`, without `±p`; it is open. -/
theorem suspChart_target_eq {c : OpenPartialHomeomorph L (Link p)} {W : L → 𝕄}
    (hW : IsConeLift c W) :
    (suspChart c W hW).target = (⋃ v ∈ c.target, suspSeg p v) \ {p, -p} := by
  ext y
  simp only [Set.mem_sdiff, mem_iUnion, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hy, hyc⟩
    have hy' := (tpMk_ne_zero_iff p).1 hy
    exact ⟨⟨dirOf p (y : 𝕄), hyc, (mem_suspSeg_iff p).2 (Or.inr (Or.inr ⟨hy, rfl⟩))⟩, hy'⟩
  · rintro ⟨⟨v, hv, hyv⟩, h1, h2⟩
    have hy : tpMk p (y : 𝕄) ≠ 0 := (tpMk_ne_zero_iff p).2 ⟨h1, h2⟩
    rcases (mem_suspSeg_iff p).1 hyv with h | h | ⟨-, hd⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact ⟨hy, hd ▸ hv⟩

end ConeChart

/-! ## 5. Singular HS-structures and singular HS-surfaces -/

section Singular

/-- **A singular HS-structure** on `Σ`: a set `S` and an `(SO₀(1,2), HS²)`-atlas of charts of
`Σ` whose sources cover exactly `Σ ∖ S`, i.e. an HS-structure on the open set `Σ ∖ S`. -/
structure SingularHSStructure (M : Type*) [TopologicalSpace M] where
  /-- the singular set `𝒮` -/
  sing : Set M
  /-- the charts of `Σ ∖ 𝒮` -/
  atlas : Set (OpenPartialHomeomorph M (HS 2))
  /-- the chart changes lie in `SO₀(1,2)` -/
  compatible : ∀ e ∈ atlas, ∀ e' ∈ atlas,
    e.symm.trans e' ∈ gxGroupoid (Causal.Flat.lorentz 2) (HS 2)
  /-- the charts cover exactly `Σ ∖ 𝒮` -/
  support_eq : support atlas = singᶜ

namespace SingularHSStructure

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- **An HS-isomorphism** between the open sets `φ.source ⊆ Σ` and `φ.target ⊆ M`: a
homeomorphism matching the singular sets, which reads, in the charts of the two HS-structures,
near every regular point, as an element of `SO₀(1,2)`. -/
def IsIso (A : SingularHSStructure M) (B : SingularHSStructure N)
    (φ : OpenPartialHomeomorph M N) : Prop :=
  (∀ x ∈ φ.source, φ x ∈ B.sing ↔ x ∈ A.sing) ∧
    ∀ x ∈ φ.source, x ∉ A.sing → ∀ e ∈ A.atlas, x ∈ e.source → ∀ e' ∈ B.atlas, φ x ∈ e'.source →
      ∃ g : Causal.Flat.lorentz 2, ∀ᶠ y in 𝓝 x, e' (φ y) = g • e y

theorem isOpen_compl_sing (A : SingularHSStructure M) : IsOpen A.singᶜ := by
  rw [← A.support_eq]
  exact isOpen_biUnion fun e _ => e.open_source

/-- The singular set is closed. -/
theorem isClosed_sing (A : SingularHSStructure M) : IsClosed A.sing :=
  isOpen_compl_iff.1 A.isOpen_compl_sing

/-- The regular part `Σ ∖ 𝒮`, an open set. -/
def regOpens (A : SingularHSStructure M) : TopologicalSpace.Opens M :=
  ⟨A.singᶜ, A.isOpen_compl_sing⟩

theorem exists_chart (A : SingularHSStructure M) {x : M} (hx : x ∉ A.sing) :
    ∃ e ∈ A.atlas, x ∈ e.source :=
  mem_support.1 (by rw [A.support_eq]; exact hx)

/-- A chart of `A` at a regular point (a choice). -/
def chartFor (A : SingularHSStructure M) (x : A.regOpens) : OpenPartialHomeomorph M (HS 2) :=
  (A.exists_chart x.2).choose

theorem chartFor_mem (A : SingularHSStructure M) (x : A.regOpens) : A.chartFor x ∈ A.atlas :=
  (A.exists_chart x.2).choose_spec.1

theorem mem_chartFor_source (A : SingularHSStructure M) (x : A.regOpens) :
    (x : M) ∈ (A.chartFor x).source :=
  (A.exists_chart x.2).choose_spec.2

/-- The charted space structure of `Σ ∖ 𝒮` over `HS²`: the charts of `A`, restricted. -/
@[reducible] def regChartedSpace (A : SingularHSStructure M) : ChartedSpace (HS 2) A.regOpens where
  atlas := {f | ∃ e ∈ A.atlas, ∃ h : Nonempty A.regOpens, f = e.subtypeRestr h}
  chartAt x := (A.chartFor x).subtypeRestr ⟨x⟩
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact A.mem_chartFor_source x
  chart_mem_atlas x := ⟨A.chartFor x, A.chartFor_mem x, ⟨x⟩, rfl⟩

/-- **`Σ ∖ 𝒮` is an HS-surface** in the sense of `bbsdef:hs_surface_topological_surface_endowed`
(`GX.IsHSSurface`), when `Σ` is Hausdorff. -/
theorem isHSSurface_reg [T2Space M] (A : SingularHSStructure M) :
    letI := A.regChartedSpace
    IsHSSurface A.regOpens := by
  letI := A.regChartedSpace
  refine isHSSurface_iff.2 ⟨inferInstance, ⟨fun {f f'} hf hf' => ?_⟩⟩
  obtain ⟨e, he, h, rfl⟩ := hf
  obtain ⟨e', he', h', rfl⟩ := hf'
  refine symm_trans_mem_gxGroupoid fun x hx => ?_
  have hx1 : (x : M) ∈ e.source := by
    have := hx.1
    rwa [OpenPartialHomeomorph.subtypeRestr_source] at this
  have hx2 : (x : M) ∈ e'.source := by
    have := hx.2
    rwa [OpenPartialHomeomorph.subtypeRestr_source] at this
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (A.compatible e he e' he') hx1 hx2
  exact ⟨g, continuous_subtype_val.continuousAt.eventually hg⟩

/-- The identity is an HS-isomorphism of a singular HS-structure. -/
theorem isIso_refl (A : SingularHSStructure M) :
    A.IsIso A (OpenPartialHomeomorph.refl M) := by
  refine ⟨fun x _ => Iff.rfl, fun x _ _ e he hxe e' he' hxe' => ?_⟩
  exact eventually_smul_eq_of_mem_gxGroupoid (A.compatible e he e' he') hxe hxe'

/-- The singular HS-structure of an HS-surface: no singular point. -/
def ofHSSurface (M : Type*) [TopologicalSpace M] [ChartedSpace (HS 2) M] [IsHSSurface M] :
    SingularHSStructure M where
  sing := ∅
  atlas := ChartedSpace.atlas
  compatible e he e' he' := HasGroupoid.compatible he he'
  support_eq := by
    rw [compl_empty]
    exact eq_univ_of_forall fun x =>
      mem_support.2 ⟨chartAt (HS 2) x, chart_mem_atlas _ x, mem_chart_source _ x⟩

end SingularHSStructure

end Singular

/-! ## 6. The developing data of a `(Γ_p, ℓ(p))`-circle and an equivariant lift -/

section TentAvg

/-- The tent function `max 0 (1 − |x|)`. -/
def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

theorem continuous_tent : Continuous tent :=
  continuous_const.max (continuous_const.sub continuous_abs)

theorem tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _

theorem abs_lt_of_tent_ne_zero {x : ℝ} (h : tent x ≠ 0) : |x| < 1 := by
  by_contra h'
  exact h (max_eq_left (by linarith [not_lt.1 h']))

theorem tent_pos_of_abs_lt {x : ℝ} (h : |x| < 1) : 0 < tent x :=
  lt_max_of_lt_right (by linarith)

theorem finite_int_near (s r : ℝ) : {n : ℤ | |(n : ℝ) - s| < r}.Finite := by
  refine (Set.finite_Icc ⌊s - r⌋ ⌈s + r⌉).subset fun n hn => ?_
  have h := abs_lt.1 (show |(n : ℝ) - s| < r from hn)
  exact ⟨Int.floor_le_iff.2 (by linarith), Int.le_ceil_iff.2 (by linarith)⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The tent average** `∑ₙ tent(s − n) Rⁿ f(s − n)` of `f` along a linear automorphism `R`:
continuous when `f` is, and `R`-equivariant, `tentAvg (s + 1) = R (tentAvg s)`. -/
def tentAvg (R : V ≃ₗ[ℝ] V) (f : ℝ → V) (s : ℝ) : V :=
  ∑ᶠ n : ℤ, tent (s - n) • (R ^ n) (f (s - n))

theorem support_tentAvg_subset (R : V ≃ₗ[ℝ] V) (f : ℝ → V) (s : ℝ) :
    (Function.support fun n : ℤ => tent (s - n) • (R ^ n) (f (s - n))) ⊆
      {n : ℤ | |(n : ℝ) - s| < 1} := by
  intro n hn
  have h : tent (s - n) ≠ 0 := fun h0 => hn (by simp only [h0, zero_smul])
  have := abs_lt_of_tent_ne_zero h
  rwa [abs_sub_comm] at this

theorem hasFiniteSupport_tentAvg (R : V ≃ₗ[ℝ] V) (f : ℝ → V) (s : ℝ) :
    Function.HasFiniteSupport (fun n : ℤ => tent (s - n) • (R ^ n) (f (s - n))) :=
  (finite_int_near s 1).subset (support_tentAvg_subset R f s)

theorem continuous_tentAvg (R : V ≃ₗ[ℝ] V) {f : ℝ → V} (hf : Continuous f) :
    Continuous (tentAvg R f) := by
  refine continuous_finsum (fun n => ?_) ?_
  · exact (continuous_tent.comp (continuous_id.sub continuous_const)).smul
      ((LinearMap.continuous_of_finiteDimensional ((R ^ n : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V)).comp
        (hf.comp (continuous_id.sub continuous_const)))
  · intro s
    refine ⟨Ioo (s - 1) (s + 1), Ioo_mem_nhds (by linarith) (by linarith),
      (finite_int_near s 2).subset ?_⟩
    rintro n ⟨x, hx, hxU⟩
    have h1 : |(n : ℝ) - x| < 1 := support_tentAvg_subset R f x hx
    have h2 := abs_lt.1 h1
    show |(n : ℝ) - s| < 2
    rw [abs_lt]
    constructor <;> linarith [hxU.1, hxU.2]

theorem tentAvg_add_one (R : V ≃ₗ[ℝ] V) (f : ℝ → V) (s : ℝ) :
    tentAvg R f (s + 1) = R (tentAvg R f s) := by
  unfold tentAvg
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ)), map_finsum R (hasFiniteSupport_tentAvg R f s)]
  refine finsum_congr fun m => ?_
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  rw [show s + 1 - ((m : ℝ) + 1) = s - m by ring, add_comm m 1, zpow_one_add,
    LinearEquiv.mul_apply, map_smul]

end TentAvg


section DevData

variable {L : Type*} [TopologicalSpace L]

/-- **Developing data of a `(Γ_p, ℓ(p))`-circle**: the universal covering `E : ℝ → L` (a periodic
covering), a developing map `d : ℝ → ℓ(p)` with holonomy `ρ ∈ Γ_p`, and a continuous lift
`w : ℝ → ℝ^{1,2}` of `d` (`[w(s)] = d(s)` in `ℓ(p)`) which is `ρ`-equivariant,
`w (s + 1) = ρ w(s)`. -/
structure GammaLinkCircle.DevData (C : GammaLinkCircle L) where
  /-- the universal covering `ℝ → L` -/
  E : ℝ → L
  periodic : IsPeriodicCover E
  /-- the developing map -/
  d : ℝ → Link C.pt
  dev : C.IsDevAlong E d
  /-- the holonomy -/
  hol : GammaP C.pt
  d_add_one : ∀ s, d (s + 1) = hol • d s
  /-- the lift of `d` to `ℝ^{1,2}` -/
  vlift : ℝ → 𝕄
  continuous_vlift : Continuous vlift
  tpMk_vlift_ne : ∀ s, tpMk C.pt (vlift s) ≠ 0
  dirOf_vlift : ∀ s, dirOf C.pt (vlift s) = d s
  vlift_add_one : ∀ s, vlift (s + 1) = ((hol : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (vlift s)

/-- **Every `(Γ_p, ℓ(p))`-circle has developing data**: the developing map of
`GX.GammaLinkCircle.exists_isDevAlong`, and an equivariant lift obtained by averaging
`ρⁿ ℓ(d(s − n))` with the tent weights `max 0 (1 − |s − n|)` (the fibres of the lift are convex
half-planes). -/
theorem GammaLinkCircle.nonempty_devData (C : GammaLinkCircle L) : Nonempty C.DevData := by
  letI := C.atlas
  obtain ⟨E, hE, d, hd, ρ, hρ⟩ := C.exists_isDevAlong
  have hdc : Continuous d := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    obtain ⟨A, hA⟩ := hd s
    have hch : ContinuousAt (fun s' => chartAt (Link C.pt) (E s) (E s')) s :=
      ((chartAt (Link C.pt) (E s)).continuousAt (mem_chart_source _ (E s))).comp
        (f := E) hE.isCoveringMap.continuous.continuousAt
    exact ((continuous_const_smul A).continuousAt.comp
      (f := fun s' => chartAt (Link C.pt) (E s) (E s')) hch).congr (hA.mono fun _ h => h.symm)
  obtain ⟨ℓ, hℓ⟩ :=
    (ℝ ∙ (C.pt : 𝕄)).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _)
  obtain ⟨w₀, hw₀c, hw₀⟩ : ∃ w₀ : ℝ → 𝕄, Continuous w₀ ∧ ∀ s, tpMk C.pt (w₀ s) = d s :=
    ⟨fun s => ℓ (d s), (LinearMap.continuous_of_finiteDimensional ℓ).comp
      (continuous_subtype_val.comp hdc),
      fun s => LinearMap.congr_fun hℓ (d s : TpHS C.pt)⟩
  set R : 𝕄 ≃ₗ[ℝ] 𝕄 := ((ρ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) with hR_def
  let hom : GammaP C.pt →* (𝕄 ≃ₗ[ℝ] 𝕄) :=
    (Causal.Flat.lorentz 2).subtype.comp (GammaP C.pt).subtype
  have hR : ∀ n : ℤ, R ^ n = (((ρ ^ n : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) :=
    fun n => (map_zpow hom ρ n).symm
  have hρ' : ∀ s, d (s - 1) = ρ⁻¹ • d s := fun s => by
    have := hρ (s - 1)
    rw [sub_add_cancel] at this
    rw [this, inv_smul_smul]
  have hdn : ∀ (n : ℤ) (s : ℝ), d (s + n) = ρ ^ n • d s := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · intro s
      simp
    · intro k ih s
      rw [show s + (((k : ℤ) + 1 : ℤ) : ℝ) = (s + ((k : ℤ) : ℝ)) + 1 by push_cast; ring, hρ, ih,
        ← mul_smul, ← zpow_one_add, add_comm (1 : ℤ)]
    · intro k ih s
      rw [show s + ((-(k : ℤ) - 1 : ℤ) : ℝ) = (s + ((-(k : ℤ) : ℤ) : ℝ)) - 1 by push_cast; ring,
        hρ', ih, ← mul_smul, ← zpow_neg_one, ← zpow_add, show (-1 + -(k : ℤ)) = -(k : ℤ) - 1 by ring]
  have hdir : ∀ s, ∃ κ : ℝ, 0 < κ ∧ tpMk C.pt (tentAvg R w₀ s) = κ • (d s : TpHS C.pt) := by
    intro s
    have hterm : ∀ n : ℤ, tpMk C.pt (tent (s - n) • (R ^ n) (w₀ (s - n))) =
        (tent (s - n) * ‖GammaP.tangent (ρ ^ n) (d (s - n))‖) • (d s : TpHS C.pt) := by
      intro n
      have hds : d s = ρ ^ n • d (s - n) := by
        have := hdn n (s - n)
        rwa [sub_add_cancel] at this
      have hT : GammaP.tangent (ρ ^ n) (d (s - n)) =
          ‖GammaP.tangent (ρ ^ n) (d (s - n))‖ • (d s : TpHS C.pt) := by
        rw [hds, gammaP_smul_def, coe_linRaySmul, smul_smul, mul_inv_cancel₀
          (norm_ne_zero_iff.2 ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero _))), one_smul]
      show Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.mk_smul, hR n]
      change tent (s - n) • tpMk C.pt ((((ρ ^ n : GammaP C.pt) : Causal.Flat.lorentz 2) :
        𝕄 ≃ₗ[ℝ] 𝕄) (w₀ (s - n))) = _
      rw [tpMk_gammaP, hw₀ (s - n), mul_smul, ← hT]
    set g : ℤ → ℝ := fun n => tent (s - n) * ‖GammaP.tangent (ρ ^ n) (d (s - n))‖ with hg_def
    have hgfin : Function.HasFiniteSupport g := by
      refine (finite_int_near s 1).subset fun n hn => ?_
      have h0 : tent (s - n) ≠ 0 := left_ne_zero_of_mul hn
      have := abs_lt_of_tent_ne_zero h0
      rwa [abs_sub_comm] at this
    have hgnn : ∀ n, 0 ≤ g n := fun n => mul_nonneg (tent_nonneg _) (norm_nonneg _)
    have hgpos : 0 < g ⌊s⌋ := by
      refine mul_pos (tent_pos_of_abs_lt ?_)
        (norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero _)))
      rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg s)]
      exact Int.fract_lt_one s
    refine ⟨∑ᶠ n, g n, lt_of_lt_of_le hgpos (single_le_finsum _ hgfin hgnn), ?_⟩
    show (ℝ ∙ (C.pt : 𝕄)).mkQ (tentAvg R w₀ s) = _
    rw [tentAvg, map_finsum _ (hasFiniteSupport_tentAvg R w₀ s), finsum_smul' hgfin]
    exact finsum_congr hterm
  refine ⟨{
    E := E
    periodic := hE
    d := d
    dev := hd
    hol := ρ
    d_add_one := hρ
    vlift := tentAvg R w₀
    continuous_vlift := continuous_tentAvg R hw₀c
    tpMk_vlift_ne := ?_
    dirOf_vlift := ?_
    vlift_add_one := fun s => tentAvg_add_one R w₀ s }⟩
  · intro s
    obtain ⟨κ, hκ, h⟩ := hdir s
    rw [h]
    exact smul_ne_zero hκ.ne' (raySphere_ne_zero _)
  · intro s
    obtain ⟨κ, hκ, h⟩ := hdir s
    have hne : tpMk C.pt (tentAvg R w₀ s) ≠ 0 := by
      rw [h]
      exact smul_ne_zero hκ.ne' (raySphere_ne_zero _)
    apply Subtype.ext
    rw [coe_dirOf _ hne, h, norm_smul, norm_raySphere, mul_one, Real.norm_eq_abs, abs_of_pos hκ,
      smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]

end DevData

/-! ## 7. The suspension `𝔢(L)` -/

section Suspension

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

namespace GammaLinkCircle.DevData

theorem _root_.GX.gammaP_coe_mul_apply {p : HS 2} (A B : GammaP p) (v : 𝕄) :
    (((A * B : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v =
      ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (((B : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v) :=
  rfl

theorem _root_.GX.gammaP_coe_inv_apply {p : HS 2} (A : GammaP p) (v : 𝕄) :
    (((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v) = v :=
  LinearEquiv.symm_apply_apply _ v

theorem _root_.GX.gammaP_coe_apply_inv {p : HS 2} (A : GammaP p) (v : 𝕄) :
    ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      ((((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v) = v :=
  LinearEquiv.apply_symm_apply _ v

theorem _root_.GX.tpMk_gammaP_ne_zero {p : HS 2} (A : GammaP p) {w : 𝕄} (hw : tpMk p w ≠ 0) :
    tpMk p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) ≠ 0 := by
  rw [tpMk_gammaP]
  exact (LinearEquiv.map_ne_zero_iff _).2 hw

/-- The lift along the deck translations: `w(s + n) = ρⁿ w(s)`. -/
theorem vlift_add_int (Δ : C.DevData) (n : ℤ) (s : ℝ) :
    Δ.vlift (s + n) = (((Δ.hol ^ n : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (Δ.vlift s) := by
  set R : 𝕄 ≃ₗ[ℝ] 𝕄 := ((Δ.hol : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
  let hom : GammaP C.pt →* (𝕄 ≃ₗ[ℝ] 𝕄) :=
    (Causal.Flat.lorentz 2).subtype.comp (GammaP C.pt).subtype
  have hR : R ^ n = (((Δ.hol ^ n : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) :=
    (map_zpow hom Δ.hol n).symm
  rw [← hR]
  revert s
  refine Int.induction_on n ?_ ?_ ?_
  · intro s
    simp
  · intro k ih s
    rw [show s + (((k : ℤ) + 1 : ℤ) : ℝ) = (s + ((k : ℤ) : ℝ)) + 1 by push_cast; ring,
      Δ.vlift_add_one, ih, ← LinearEquiv.mul_apply, ← zpow_one_add, add_comm (1 : ℤ)]
  · intro k ih s
    apply R.injective
    rw [← Δ.vlift_add_one, show s + ((-(k : ℤ) - 1 : ℤ) : ℝ) + 1 = s + ((-(k : ℤ) : ℤ) : ℝ) by
      push_cast; ring, ih, ← LinearEquiv.mul_apply, ← zpow_one_add,
      show (1 + (-(k : ℤ) - 1)) = -(k : ℤ) by ring]

/-- An eventual property along `E` near `s` holds near `E s`. -/
theorem eventually_of_eventually_E (Δ : C.DevData) {P : L → Prop} {s : ℝ}
    (h : ∀ᶠ s' in 𝓝 s, P (Δ.E s')) : ∀ᶠ σ in 𝓝 (Δ.E s), P σ := by
  filter_upwards [Δ.periodic.isCoveringMap.isLocalHomeomorph.isOpenMap.image_mem_nhds h] with σ hσ
  obtain ⟨s', hs', rfl⟩ := hσ
  exact hs'

/-- `W` is, near every point of `c.source`, a `Γ_p`-translate of the lift `Δ.vlift`, read
through `E`. -/
def IsLiftOf (Δ : C.DevData) (c : OpenPartialHomeomorph L (Link C.pt)) (W : L → 𝕄) : Prop :=
  ∀ σ ∈ c.source, ∃ s, Δ.E s = σ ∧ ∃ A : GammaP C.pt,
    ∀ᶠ s' in 𝓝 s, W (Δ.E s') = ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s')

/-- **The HS-atlas of `𝔢(L)`**: the cone charts over the charts `c` of `L`, with lifts that are
locally `Γ_p`-translates of the equivariant lift of the developing map. -/
def suspAtlas (Δ : C.DevData) : Set (OpenPartialHomeomorph (BiSusp L) (HS 2)) :=
  {χ | ∃ (c : OpenPartialHomeomorph L (Link C.pt)) (W : L → 𝕄) (hW : IsConeLift c W),
    Δ.IsLiftOf c W ∧ χ = suspChart c W hW}

/-- **The chart changes of `𝔢(L)` lie in `Γ_p`** (the paper's gluing maps `g_ij ∈ Γ_p`,
`colI_v1.tex:646–651`): near every point of the overlap of two cone charts, one is an element
of `Γ_p` times the other. -/
theorem suspAtlas_eventually_eq_smul (Δ : C.DevData)
    {χ χ' : OpenPartialHomeomorph (BiSusp L) (HS 2)} (hχ : χ ∈ Δ.suspAtlas)
    (hχ' : χ' ∈ Δ.suspAtlas) {x : BiSusp L} (hx : x ∈ χ.source ∩ χ'.source) :
    ∃ g : GammaP C.pt, ∀ᶠ y in 𝓝 x, χ' y = (g : Causal.Flat.lorentz 2) • χ y := by
  obtain ⟨c, W, hW, hl, rfl⟩ := hχ
  obtain ⟨c', W', hW', hl', rfl⟩ := hχ'
  obtain ⟨⟨q, hq, rfl⟩, ⟨q', hq', hqq'⟩⟩ := hx
  have hqe : q' = q := BiSusp.mk'_injOn_regSet ⟨trivial, hq'.2⟩ ⟨trivial, hq.2⟩ hqq'
  rw [hqe] at hq'
  obtain ⟨s, hs, A, hA⟩ := hl q.1 hq.1
  obtain ⟨s', hs', A', hA'⟩ := hl' q.1 hq'.1
  obtain ⟨n, hn⟩ := Δ.periodic.fiber s s' (hs.trans hs'.symm)
  set g : GammaP C.pt := A' * Δ.hol ^ n * A⁻¹ with hg
  have hev : ∀ᶠ s'' in 𝓝 s, W' (Δ.E s'') =
      ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W (Δ.E s'')) := by
    have hA'' : ∀ᶠ s'' in 𝓝 s, W' (Δ.E (s'' + n)) =
        ((A' : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift (s'' + n)) := by
      have ht : Tendsto (fun s'' => s'' + (n : ℝ)) (𝓝 s) (𝓝 s') := by
        rw [hn]
        exact (continuous_add_const _).tendsto s
      exact ht.eventually hA'
    filter_upwards [hA, hA''] with s'' h1 h2
    rw [show W' (Δ.E s'') = W' (Δ.E (s'' + n)) by rw [Δ.periodic.add_int], h2,
      Δ.vlift_add_int n s'', h1, hg, gammaP_coe_mul_apply, gammaP_coe_mul_apply,
      gammaP_coe_inv_apply]
  have hevσ : ∀ᶠ σ'' in 𝓝 q.1, W' σ'' = ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W σ'') := by
    rw [← hs]
    exact Δ.eventually_of_eventually_E hev
  refine ⟨g, ?_⟩
  rw [BiSusp.nhds_mk ⟨trivial, hq.2⟩, eventually_map]
  have hqc : ∀ᶠ q'' in 𝓝 q, q''.1 ∈ c.source :=
    continuous_fst.continuousAt.eventually (c.open_source.mem_nhds hq.1)
  have hσ' : ∀ᶠ q'' in 𝓝 q, W' q''.1 = ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W q''.1) :=
    continuous_fst.continuousAt.eventually hevσ
  filter_upwards [hqc, hσ'] with q'' h1 h2
  show arcPt C.pt (W' q''.1) q''.2 = (g : Causal.Flat.lorentz 2) • arcPt C.pt (W q''.1) q''.2
  rw [h2, smul_arcPt _ g (hW.tpMk_ne _ h1)]

theorem suspAtlas_compatible (Δ : C.DevData) {χ χ' : OpenPartialHomeomorph (BiSusp L) (HS 2)}
    (hχ : χ ∈ Δ.suspAtlas) (hχ' : χ' ∈ Δ.suspAtlas) :
    χ.symm.trans χ' ∈ gxGroupoid (Causal.Flat.lorentz 2) (HS 2) := by
  refine symm_trans_mem_gxGroupoid fun x hx => ?_
  obtain ⟨g, hg⟩ := Δ.suspAtlas_eventually_eq_smul hχ hχ' hx
  exact ⟨g, hg⟩

theorem support_suspAtlas (Δ : C.DevData) : support Δ.suspAtlas = (BiSusp.poles L)ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨χ, ⟨c, W, hW, -, rfl⟩, hxχ⟩ := mem_support.1 hx
    rw [← BiSusp.image_mk'_regSet_univ]
    obtain ⟨q, hq, rfl⟩ := hxχ
    exact ⟨q, ⟨trivial, hq.2⟩, rfl⟩
  · intro hx
    rw [← BiSusp.image_mk'_regSet_univ] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    letI := C.atlas
    obtain ⟨s, hs⟩ := Δ.periodic.surjective q.1
    obtain ⟨B, hB⟩ := Δ.dev s
    obtain ⟨eE, hsE, hEe⟩ := Δ.periodic.isCoveringMap.isLocalHomeomorph s
    set ch := chartAt (Link C.pt) (Δ.E s)
    set P : Set ℝ := {s' | s' ∈ eE.source ∧ Δ.E s' ∈ ch.source ∧ Δ.d s' = B • ch (Δ.E s')}
    have hP : P ∈ 𝓝 s := by
      refine Filter.inter_mem (eE.open_source.mem_nhds hsE) (Filter.inter_mem ?_ hB)
      exact Δ.periodic.isCoveringMap.continuous.continuousAt.preimage_mem_nhds
        (ch.open_source.mem_nhds (mem_chart_source _ _))
    set O := interior P
    have hO : IsOpen O := isOpen_interior
    have hsO : s ∈ O := mem_interior_iff_mem_nhds.2 hP
    have hOP : O ⊆ P := interior_subset
    set U := Δ.E '' O
    have hU : IsOpen U := Δ.periodic.isCoveringMap.isLocalHomeomorph.isOpenMap O hO
    have hUch : U ⊆ ch.source := by
      rintro _ ⟨s', hs', rfl⟩
      exact (hOP hs').2.1
    set c := ch.restrOpen U hU
    have hcs : c.source = U := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact inter_eq_right.2 hUch
    have hEsymm : ∀ s' ∈ O, eE.symm (Δ.E s') = s' := fun s' hs' => by
      rw [hEe]
      exact eE.left_inv (hOP hs').1
    have hUt : U ⊆ eE.target := by
      rintro _ ⟨s', hs', rfl⟩
      rw [hEe]
      exact eE.map_source (hOP hs').1
    set W : L → 𝕄 := fun σ' =>
      (((B⁻¹ : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift (eE.symm σ'))
    have hW : IsConeLift c W := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hcs]
        refine ((LinearMap.continuous_of_finiteDimensional
          ((((B⁻¹ : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) : 𝕄 →ₗ[ℝ] 𝕄)).comp
            Δ.continuous_vlift).comp_continuousOn ?_
        exact eE.continuousOn_symm.mono hUt
      · intro σ' _
        exact tpMk_gammaP_ne_zero _ (Δ.tpMk_vlift_ne _)
      · intro σ' hσ'
        rw [hcs] at hσ'
        obtain ⟨s', hs', rfl⟩ := hσ'
        have h1 : W (Δ.E s') =
            (((B⁻¹ : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s') := by
          show (((B⁻¹ : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
            (Δ.vlift (eE.symm (Δ.E s'))) = _
          rw [hEsymm s' hs']
        rw [h1, dirOf_gammaP _ _ (Δ.tpMk_vlift_ne s'), Δ.dirOf_vlift, (hOP hs').2.2,
          inv_smul_smul]
        rfl
    have hl : Δ.IsLiftOf c W := by
      intro σ' hσ'
      rw [hcs] at hσ'
      obtain ⟨s', hs', rfl⟩ := hσ'
      refine ⟨s', rfl, B⁻¹, ?_⟩
      filter_upwards [eE.open_source.mem_nhds (hOP hs').1] with s'' hs''
      show (((B⁻¹ : GammaP C.pt) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
        (Δ.vlift (eE.symm (Δ.E s''))) = _
      rw [hEe, eE.left_inv hs'']
    refine mem_support.2 ⟨suspChart c W hW, ⟨c, W, hW, hl, rfl⟩, ⟨q, ⟨?_, hq.2⟩, rfl⟩⟩
    rw [hcs, ← hs]
    exact ⟨s, hsO, rfl⟩

/-- **`𝔢(L)` as a singular HS-structure** on `BiSusp L`: singular set the two apices
`p̄, −p̄`, regular part charted by `suspAtlas`. -/
def suspStructure (Δ : C.DevData) : SingularHSStructure (BiSusp L) where
  sing := BiSusp.poles L
  atlas := Δ.suspAtlas
  compatible _ he _ he' := Δ.suspAtlas_compatible he he'
  support_eq := Δ.support_suspAtlas

/-- The cone charts of `𝔢(L)` lie over charts of `L`'s `(Γ_p, ℓ(p))`-structure. -/
theorem mem_maximalAtlas_of_mem_suspAtlas (Δ : C.DevData) {c : OpenPartialHomeomorph L (Link C.pt)}
    {W : L → 𝕄} (hW : IsConeLift c W) (hl : Δ.IsLiftOf c W) :
    letI := C.atlas
    c ∈ (gxGroupoid (GammaP C.pt) (Link C.pt)).maximalAtlas L := by
  letI := C.atlas
  haveI := C.hasGroupoid
  refine mem_maximalAtlas_iff_eventually.2 fun σ hσ => ?_
  obtain ⟨s, hs, A, hA⟩ := hl σ hσ
  obtain ⟨B, hB⟩ := Δ.dev s
  refine ⟨A * B, ?_⟩
  rw [← hs]
  refine Δ.eventually_of_eventually_E ?_
  have hsrc : ∀ᶠ s' in 𝓝 s, Δ.E s' ∈ c.source :=
    Δ.periodic.isCoveringMap.continuous.continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds (hs ▸ hσ))
  filter_upwards [hA, hB, hsrc] with s' h1 h2 h3
  rw [← hW.dirOf_eq _ h3, h1, dirOf_gammaP _ _ (Δ.tpMk_vlift_ne s'), Δ.dirOf_vlift, h2, mul_smul]

end GammaLinkCircle.DevData

theorem GammaLinkCircle.nonempty (C : GammaLinkCircle L) : Nonempty L := by
  obtain ⟨φ⟩ := C.isCircle
  exact ⟨φ.symm 1⟩

/-- **`𝔢(L)` is homeomorphic to `HS²`** (`colI_v1.tex:779`). -/
def GammaLinkCircle.suspHomeomorph (C : GammaLinkCircle L) : BiSusp L ≃ₜ HS 2 :=
  BiSusp.homeomorphHS (Classical.choice C.isCircle)

theorem GammaLinkCircle.isTopologicalSurface_susp (C : GammaLinkCircle L) :
    IsTopologicalSurface (BiSusp L) :=
  BiSusp.isTopologicalSurface (Classical.choice C.isCircle)

theorem GammaLinkCircle.t2Space_susp (C : GammaLinkCircle L) : T2Space (BiSusp L) :=
  BiSusp.t2Space_of_homeomorph (Classical.choice C.isCircle)

/-- **`𝔢(L)` is an HS-surface off its two apices** (`colI_v1.tex:779–780`, « locally modeled on
`HS²` in the complement of two singular points »). -/
theorem GammaLinkCircle.DevData.isHSSurface_reg (Δ : C.DevData) :
    haveI := C.t2Space_susp
    letI := Δ.suspStructure.regChartedSpace
    IsHSSurface Δ.suspStructure.regOpens := by
  haveI := C.t2Space_susp
  exact Δ.suspStructure.isHSSurface_reg

end Suspension

/-! ## 8. Singular HS-surfaces -/

section SingularSurface

/-- `bbsdef:singular_hs_surface_oriented_surface` (`colI_v1.tex:948–953`): a singular
HS-surface is a surface `Σ` (read `GX.IsTopologicalSurface`, OQ-104) with a discrete subset `𝒮`
such that `Σ ∖ 𝒮` is an HS-surface, and such that every point of `𝒮` has a neighbourhood
HS-isomorphic to an open subset of the suspension `𝔢(L)` of a `(Γ_p, ℓ(p))`-circle `L`. -/
def IsSingularHSSurface (M : Type*) [TopologicalSpace M] (A : SingularHSStructure M) : Prop :=
  IsTopologicalSurface M ∧ DiscreteTopology A.sing ∧
    ∀ x ∈ A.sing, ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (Δ : C.DevData)
      (φ : OpenPartialHomeomorph M (BiSusp L)), x ∈ φ.source ∧ A.IsIso Δ.suspStructure φ

/-- **Every HS-surface is a singular HS-surface** (with `𝒮 = ∅`). -/
theorem isSingularHSSurface_ofHSSurface (M : Type*) [TopologicalSpace M] [ChartedSpace (HS 2) M]
    [IsHSSurface M] : IsSingularHSSurface M (SingularHSStructure.ofHSSurface M) := by
  refine ⟨(inferInstance : IsHSSurface M).toIsTopologicalSurface, ?_,
    fun x hx => absurd hx (notMem_empty x)⟩
  show DiscreteTopology (∅ : Set M)
  infer_instance

/-- **`𝔢(L)` is a singular HS-surface** (with `𝒮 = {p̄, −p̄}`, its own local model). -/
theorem GammaLinkCircle.DevData.isSingularHSSurface {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) : IsSingularHSSurface (BiSusp L) Δ.suspStructure := by
  haveI : Nonempty L := C.nonempty
  haveI := C.t2Space_susp
  refine ⟨C.isTopologicalSurface_susp, ?_, fun x hx => ⟨L, inferInstance, C, Δ,
    OpenPartialHomeomorph.refl _, trivial, Δ.suspStructure.isIso_refl⟩⟩
  have hfin : (BiSusp.poles L).Finite := by
    rw [BiSusp.poles_eq]
    exact Set.toFinite _
  haveI := hfin.to_subtype
  show DiscreteTopology (BiSusp.poles L)
  infer_instance

end SingularSurface

/-! ## 9. The regular link: `𝔢(ℓ(p)) = HS²` -/

section Regular

variable {p : HS 2}

/-- **For the regular link `ℓ(p)`, `𝔢(ℓ(p))` is `HS²` itself** (`colI_v1.tex:658–659`, the
analogue of `e(HS²) = E(p)`): a homeomorphism `𝔢(ℓ(p)) ≃ₜ HS²` sending `p̄ ↦ p`, `−p̄ ↦ −p`,
which is an HS-chart (near every point of every cone chart, an element of `SO₀(1,2)` times it):
the HS-structure of `𝔢(ℓ(p))` off its apices is the one of `HS² ∖ {±p}`, and the apices are
regular. -/
theorem GammaLinkCircle.DevData.regular_susp (Δ : (GammaLinkCircle.regular p).DevData) :
    ∃ F : BiSusp (Link p) ≃ₜ HS 2, F (BiSusp.north (Link p)) = p ∧
      F (BiSusp.south (Link p)) = -p ∧
      ∀ χ ∈ Δ.suspAtlas, ∀ x ∈ χ.source,
        ∃ g : Causal.Flat.lorentz 2, ∀ᶠ y in 𝓝 x, F y = g • χ y := by
  letI := (GammaLinkCircle.regular p).atlas
  have hEl : IsLocalHomeomorph Δ.E := Δ.periodic.isCoveringMap.isLocalHomeomorph
  have hEdev : (GammaLinkCircle.regular p).IsDevAlong Δ.E Δ.E := fun s =>
    ⟨1, Eventually.of_forall fun s' => by
      show Δ.E s' = (1 : GammaP p) • chartAt (Link p) (Δ.E s) (Δ.E s')
      rw [chartAt_self_eq, one_smul]
      rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : ℝ → Link p, d' = Δ.d := ⟨Δ.d, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : GammaP p, ∀ s, d' s = A • (Δ.E s : Link p) := by
    obtain ⟨A, hA, -⟩ := hEdev.existsUnique_eq_smul hEl Δ.dev
    exact ⟨A, fun s => by rw [hd']; exact hA s⟩
  have hdv : ∀ s, dirOf p (Δ.vlift s) = d' s := fun s => by rw [hd']; exact Δ.dirOf_vlift s
  have hvne : ∀ s, tpMk p (Δ.vlift s) ≠ 0 := Δ.tpMk_vlift_ne
  set ρ : GammaP p := Δ.hol with hρ_def
  have hvadd : ∀ (n : ℤ) (s : ℝ), Δ.vlift (s + n) =
      (((ρ ^ n : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s) :=
    Δ.vlift_add_int
  have hdadd : ∀ s, d' (s + 1) = ρ • d' s := fun s => by rw [hd']; exact Δ.d_add_one s
  -- the holonomy is trivial
  have hρ : ρ = 1 := by
    refine eq_of_smul_eq_smul (α := Link p) fun σ => ?_
    obtain ⟨s, hs⟩ := Δ.periodic.surjective (A⁻¹ • σ)
    have hσ : A • (Δ.E s : Link p) = σ := by rw [hs, smul_inv_smul]
    rw [one_smul, ← hσ, ← hA s, ← hdadd, hA, Δ.periodic.add_one, hA s]
  have hvper : ∀ (n : ℤ) (s : ℝ), Δ.vlift (s + n) = Δ.vlift s := fun n s => by
    rw [hvadd, hρ, one_zpow]
    rfl
  -- the descended lift `W₀ : ℓ(p) → ℝ^{1,2}`
  set W₀ : Link p → 𝕄 := fun σ => (((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
    (Δ.vlift (Δ.periodic.surjective σ).choose) with hW₀_def
  have hW₀E : ∀ s, W₀ (Δ.E s) =
      (((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s) := fun s => by
    show (((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (Δ.vlift (Δ.periodic.surjective (Δ.E s)).choose) = _
    obtain ⟨n, hn⟩ := Δ.periodic.fiber _ s (Δ.periodic.surjective (Δ.E s)).choose_spec
    conv_rhs => rw [hn]
    rw [hvper]
  have hW₀ne : ∀ σ, tpMk p (W₀ σ) ≠ 0 := fun σ => by
    obtain ⟨s, rfl⟩ := Δ.periodic.surjective σ
    rw [hW₀E]
    exact tpMk_gammaP_ne_zero _ (hvne s)
  have hW₀dir : ∀ σ, dirOf p (W₀ σ) = σ := fun σ => by
    obtain ⟨s, rfl⟩ := Δ.periodic.surjective σ
    rw [hW₀E, dirOf_gammaP p _ (hvne s), hdv, hA s, inv_smul_smul]
  have hW₀c : Continuous W₀ := by
    refine continuous_iff_continuousAt.2 fun σ => ?_
    obtain ⟨s, rfl⟩ := Δ.periodic.surjective σ
    obtain ⟨eE, hsE, hEe⟩ := hEl s
    have hev : ∀ᶠ σ' in 𝓝 (Δ.E s), W₀ σ' = (((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) :
        𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift (eE.symm σ')) := by
      have ht : eE.target ∈ 𝓝 (Δ.E s) := by
        rw [hEe]
        exact eE.open_target.mem_nhds (eE.map_source hsE)
      filter_upwards [ht] with σ' hσ'
      have : Δ.E (eE.symm σ') = σ' := by rw [hEe]; exact eE.right_inv hσ'
      rw [← hW₀E, this]
    refine ContinuousAt.congr ?_ (hev.mono fun _ h => h.symm)
    have hcs : ContinuousAt eE.symm (Δ.E s) := by
      apply eE.continuousAt_symm
      rw [hEe]
      exact eE.map_source hsE
    exact ((LinearMap.continuous_of_finiteDimensional
      ((((A⁻¹ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) : 𝕄 →ₗ[ℝ] 𝕄)).comp
        Δ.continuous_vlift).continuousAt.comp hcs
  -- the map `𝔢(ℓ(p)) → HS²` and its inverse
  set F₀ : BiSusp (Link p) → HS 2 := suspMap p W₀ with hF₀
  have hF₀c : Continuous F₀ := by
    refine BiSusp.continuous_lift _ _ (continuous_iff_continuousAt.2 fun q => ?_)
    exact (continuousAt_arcPt p (hW₀ne q.1) q.2).comp
      (f := fun q : Link p × Icc (0 : ℝ) Real.pi => (W₀ q.1, (q.2 : ℝ)))
      ((hW₀c.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
  open Classical in
  let G : HS 2 → BiSusp (Link p) := fun y =>
    if y = p then BiSusp.north (Link p) else if y = -p then BiSusp.south (Link p) else
      BiSusp.mk (dirOf p (y : 𝕄)) (projIcc 0 Real.pi Real.pi_pos.le
        (arcAngle p y (W₀ (dirOf p (y : 𝕄)))))
  have hF₀north : F₀ (BiSusp.north (Link p)) = p := arcPt_zero p _
  have hF₀south : F₀ (BiSusp.south (Link p)) = -p := arcPt_pi p _
  have hleft : Function.LeftInverse G F₀ := by
    intro x
    obtain ⟨σ, t, rfl⟩ := BiSusp.mk_surjective x
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have hx : BiSusp.mk σ t = BiSusp.north (Link p) :=
        BiSusp.mk_eq_mk.2 (Or.inr (Or.inl ⟨h0.symm, rfl⟩))
      rw [hx]
      show (if F₀ (BiSusp.north (Link p)) = p then _ else _) = _
      rw [if_pos hF₀north]
    rcases eq_or_lt_of_le t.2.2 with hπ | hπ
    · have hx : BiSusp.mk σ t = BiSusp.south (Link p) :=
        BiSusp.mk_eq_mk.2 (Or.inr (Or.inr ⟨hπ, rfl⟩))
      rw [hx]
      show (if F₀ (BiSusp.south (Link p)) = p then _ else _) = _
      rw [if_neg (by rw [hF₀south]; exact neg_ne_self_hs p), if_pos hF₀south]
    have hne := tpMk_arcPt_ne_zero p (hW₀ne σ) h0 hπ
    have hne' := (tpMk_ne_zero_iff p).1 hne
    have hF : F₀ (BiSusp.mk σ t) = arcPt p (W₀ σ) t := rfl
    show (if F₀ (BiSusp.mk σ t) = p then BiSusp.north (Link p) else
      if F₀ (BiSusp.mk σ t) = -p then BiSusp.south (Link p) else
        BiSusp.mk (dirOf p (F₀ (BiSusp.mk σ t) : 𝕄)) (projIcc 0 Real.pi Real.pi_pos.le
          (arcAngle p (F₀ (BiSusp.mk σ t)) (W₀ (dirOf p (F₀ (BiSusp.mk σ t) : 𝕄)))))) =
      BiSusp.mk σ t
    rw [hF, if_neg hne'.1, if_neg hne'.2, dirOf_arcPt p (hW₀ne σ) h0 hπ, hW₀dir,
      arcAngle_arcPt p (hW₀ne σ) h0 hπ, projIcc_of_mem _ t.2]
  have hright : Function.RightInverse G F₀ := by
    intro y
    by_cases h1 : y = p
    · show F₀ (if y = p then _ else _) = y
      rw [if_pos h1, hF₀north, h1]
    by_cases h2 : y = -p
    · show F₀ (if y = p then _ else _) = y
      rw [if_neg h1, if_pos h2, hF₀south, h2]
    have hy : tpMk p (y : 𝕄) ≠ 0 := (tpMk_ne_zero_iff p).2 ⟨h1, h2⟩
    show F₀ (if y = p then _ else _) = y
    rw [if_neg h1, if_neg h2]
    obtain ⟨ha0, haπ⟩ := arcAngle_mem p hy (hW₀ne (dirOf p (y : 𝕄)))
    show arcPt p (W₀ (dirOf p (y : 𝕄))) (projIcc 0 Real.pi Real.pi_pos.le
      (arcAngle p y (W₀ (dirOf p (y : 𝕄)))) : ℝ) = y
    rw [coe_projIcc_of_mem ⟨ha0.le, haπ.le⟩]
    exact arcPt_arcAngle p hy (hW₀ne _) (hW₀dir _).symm
  haveI : CompactSpace (Link p) := (Classical.choice (isCircle_link p)).symm.compactSpace
  let e : BiSusp (Link p) ≃ HS 2 := ⟨F₀, G, hleft, hright⟩
  refine ⟨hF₀c.homeoOfEquivCompactToT2 (f := e), hF₀north, hF₀south, ?_⟩
  rintro χ ⟨c, W, hW, hl, rfl⟩ x hx
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨s, hs, B, hB⟩ := hl q.1 hq.1
  set B' : GammaP p := B with hB'_def
  have hB' : ∀ᶠ s' in 𝓝 s, W (Δ.E s') =
      ((B' : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s') := hB
  set g : GammaP p := A⁻¹ * B'⁻¹ with hg
  have hev : ∀ᶠ s' in 𝓝 s, W₀ (Δ.E s') =
      ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W (Δ.E s')) := by
    filter_upwards [hB'] with s' h
    rw [hW₀E, h, hg, gammaP_coe_mul_apply, gammaP_coe_inv_apply]
  have hevσ : ∀ᶠ σ' in 𝓝 q.1, W₀ σ' = ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W σ') := by
    rw [← hs]
    exact Δ.eventually_of_eventually_E hev
  refine ⟨(g : Causal.Flat.lorentz 2), ?_⟩
  rw [BiSusp.nhds_mk ⟨trivial, hq.2⟩, eventually_map]
  have hqc : ∀ᶠ q'' in 𝓝 q, q''.1 ∈ c.source :=
    continuous_fst.continuousAt.eventually (c.open_source.mem_nhds hq.1)
  filter_upwards [hqc, continuous_fst.continuousAt.eventually hevσ] with q'' h1 h2
  have hWne : tpMk p (W q''.1) ≠ 0 := hW.tpMk_ne _ h1
  show arcPt p (W₀ q''.1) q''.2 = (g : Causal.Flat.lorentz 2) • arcPt p (W q''.1) q''.2
  rw [h2, smul_arcPt p g hWne]

end Regular

end GX
