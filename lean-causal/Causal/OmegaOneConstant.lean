import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Instances.Discrete
import Mathlib.Order.Filter.EventuallyConst

/-!
# A continuous map from ω₁ into a T1, second countable space is eventually constant

Programme target `T-abs-omega-one-constant` (`programme/roadmap.toml`; layer 1, pure topology:
Mathlib imports only, no `Causal` import, `uses = []`). It is the lemma that stops long chains of
curves in `T-abs-curves-extend-second-countable` (step (2b) there). There is no paper behind it,
so **no label is marked**. The statement, as the target words it:

> A continuous map from ω₁ into a T1, second countable space is eventually constant: for
> g : ω₁ → Y continuous for the order topology (equivalently, g λ is the limit of g β, β → λ, at
> every limit λ < ω₁), some γ < ω₁ has g α = g γ for every α ≥ γ.

> Optionally, the same for any well-order of uncountable cofinality. (the target's evidence)

## What is proved

* **Continuity at limits**, `LimitContinuous g`: at every successor limit `a`, `g c → g a` as
  `c → a` from below. The index order carries no topology. On a well order with its order
  topology this is continuity (`continuous_iff_limitContinuous`); on any linear order continuity
  implies it (`limitContinuous_of_continuous`).
* **The general theorem**, on any well order `α` of uncountable cofinality (`ℵ₀ < Order.cof α`).
  A `LimitContinuous` map into a space with a countable family of open sets separating points in
  the T1 sense is eventually constant (`LimitContinuous.exists_forall_ge_eq_of_separating`). So is
  one into a T1, second countable space (`LimitContinuous.exists_forall_ge_eq`), or into a space
  injecting continuously into one (`LimitContinuous.exists_forall_ge_eq_of_injective`). The
  continuous forms are `exists_forall_ge_eq_of_continuous` and
  `eventuallyConst_atTop_of_continuous`. On a non-empty order, `cof α ≠ ℵ₀` suffices
  (`LimitContinuous.exists_forall_ge_eq_of_cof_ne_aleph0`). The proof is the target's sketch,
  through clubs (`IsClub.iInter`) and the bound on countable sets that `ℵ₀ < cof α` gives.
* **At ω₁** (Mathlib's `ω₁ = Ordinal.omega 1`): `aleph0_lt_cof_Iio_omega_one`. For
  `g : Iio ω₁ → Y` continuous (the subspace topology of `Iio ω₁ ⊆ Ordinal` is its order
  topology), `exists_forall_ge_eq_of_continuous_omega_one`. For `g : Ordinal → Y` read below ω₁,
  the conclusion `∃ γ < ω₁, ∀ a, γ ≤ a → a < ω₁ → g a = g γ` follows from three hypotheses:
  * the limit condition at every limit `λ < ω₁` (`exists_lt_omega_one_forall_eq`);
  * that condition as a `Tendsto` (`exists_lt_omega_one_forall_eq_of_tendsto`);
  * `ContinuousOn g (Iio ω₁)` (`exists_lt_omega_one_forall_eq_of_continuousOn`).

  One `γ` serves countably many maps at once (`exists_lt_omega_one_forall_eq_family`), and every
  tail `[γ, ω₁)` holds a limit (`exists_isSuccLimit_ge_lt_omega_one`).
* **Each hypothesis is needed.**
  * Cofinality `ℵ₀`: the identity of `ℕ` (`nat_separates`).
  * T1 weakened to T0: Sierpiński space is T0 and second countable, and the indicator of the
    non-limit ordinals is a counterexample (`sierpinski_separates`).
  * Second countability weakened to first countability, even with T2: the identity of ω₁
    (`omega_one_id_separates`, `firstCountableTopology_Iio_omega_one`).

## Hypothesis checklist

| the target's statement | here |
|---|---|
| ω₁ with the order topology | ✓ `Iio (ω₁ : Ordinal.{u})`, or `Ordinal → Y` read below ω₁; ⚠ weakened: any well order with `ℵ₀ < Order.cof α`, or `≠ ℵ₀` if non-empty |
| `g` continuous | ✓ `Continuous g`; ⚠ weakened: `LimitContinuous g`, the target's "equivalently" (equivalent on a well order, `continuous_iff_limitContinuous`) |
| `Y` T1 | ✓ `T1Space Y`; needed (`sierpinski_separates`) |
| `Y` second countable | ✓ `SecondCountableTopology Y`; ⚠ weakened: a countable family of opens separating points (a coarser T1, second countable topology); first countable and T2 is not enough (`omega_one_id_separates`) |
| some `γ < ω₁` with `g α = g γ` for every `α ≥ γ` | ✓ `∃ γ, ∀ a, γ ≤ a → g a = g γ`, `∃ γ < ω₁, …`, `EventuallyConst g atTop` |

## SCOPE (disclosed)

* **Nothing marked**: no paper, no label. The target's statement is proved as written, in the
  general form its evidence calls optional, and with each hypothesis shown needed.
* `(ω₁).ToType` has no topology instance in Mathlib. The general theorem applies to it in the
  `LimitContinuous` form, through `Ordinal.cof_toType`.
* Cofinality `ℵ₀` is refuted on `ℕ` only. On a general well order of countable cofinality, the
  clopen blocks between the terms of a cofinal ω-sequence map onto `ℕ`; not formalized.
  Compactness is no substitute for second countability either (ω₁ inside ω₁ + 1); not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology Cardinal Order

universe u v w x

/-! ## 1. Continuity at limits -/

section LimitContinuous

variable {α : Type u} {Y : Type w} [TopologicalSpace Y]

/-- **Continuity at limits** (the target's "g λ is the limit of g β, β → λ, at every limit λ"):
at every successor limit `a` of `α`, `g c` tends to `g a` as `c` tends to `a` from below. No
topology on `α`; on a well order with its order topology it is continuity
(`continuous_iff_limitContinuous`). -/
def LimitContinuous [Preorder α] (g : α → Y) : Prop :=
  ∀ a, IsSuccLimit a → ∀ U ∈ 𝓝 (g a), ∃ b < a, ∀ c, b < c → c < a → g c ∈ U

/-- A continuous map on a linear order with its order topology is continuous at limits. -/
theorem limitContinuous_of_continuous [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {g : α → Y} (hg : Continuous g) : LimitContinuous g := by
  intro a ha U hU
  have h1 : g ⁻¹' U ∈ 𝓝[<] a := nhdsWithin_le_nhds (hg.continuousAt hU)
  obtain ⟨b, hba⟩ := ha.nonempty_Iio
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hba).1 h1
  exact ⟨l, hl, fun c hlc hca ↦ hsub ⟨hlc, hca⟩⟩

/-- **On a well order with its order topology, continuity is continuity at limits**: a point that
is not a limit is isolated from the left (it is minimal or covers a point), and every point is
isolated from the right (it is maximal or covered by its successor). -/
theorem continuous_iff_limitContinuous [LinearOrder α] [WellFoundedLT α] [TopologicalSpace α]
    [OrderTopology α] {g : α → Y} : Continuous g ↔ LimitContinuous g := by
  refine ⟨limitContinuous_of_continuous, fun hg ↦ continuous_iff_continuousAt.2 fun a ↦ ?_⟩
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · by_cases ha : IsSuccLimit a
    · intro U hU
      obtain ⟨b, hb, hsub⟩ := hg a ha U hU
      exact Filter.mem_map.2 (mem_of_superset (Ioo_mem_nhdsLT hb) (fun c hc ↦ hsub c hc.1 hc.2))
    · have h : 𝓝[<] a = ⊥ := by
        rw [nhdsLT_eq_bot_iff]
        rcases not_isSuccLimit_iff.1 ha with h | h
        · exact Or.inl h.isBot
        · exact Or.inr (not_isSuccPrelimit_iff.1 h)
      simp [ContinuousWithinAt, h]
  · have h : 𝓝[>] a = ⊥ := by
      rw [nhdsGT_eq_bot_iff]
      by_cases hmax : IsMax a
      · exact Or.inl hmax.isTop
      · exact Or.inr (exists_covBy_of_wellFoundedLT hmax)
    simp [ContinuousWithinAt, h]

end LimitContinuous

/-! ## 2. Well orders of uncountable cofinality -/

section General

variable {α : Type u} [LinearOrder α] [WellFoundedLT α] {Y : Type w} [TopologicalSpace Y]

/-- **The core.** On a well order of uncountable cofinality, a map continuous at limits into a
space with a countable family `B` of open sets separating points in the T1 sense (for `x ≠ y`,
some `B i` contains `x` and misses `y`) is eventually constant.

The target's proof: for each `i`, either `g⁻¹(B i)` contains a tail `[γᵢ, →)`, or its complement
is closed under suprema (continuity at limits) and cofinal, a club. Past the supremum `γ₀` of the
countably many `γᵢ` lies a point `δ` of the intersection of the clubs (`IsClub.iInter`); then
`g δ ∈ B i` only if `g⁻¹(B i)` holds a tail, so every `g a`, `a ≥ γ₀`, lies in every `B i`
containing `g δ`, and `g a = g δ` by separation. -/
theorem LimitContinuous.exists_forall_ge_eq_of_separating (hα : ℵ₀ < Order.cof α)
    {ι : Type v} [Countable ι] {B : ι → Set Y} (hB : ∀ i, IsOpen (B i))
    (hsep : ∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∉ B i) {g : α → Y} (hg : LimitContinuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ := by
  classical
  have hne : Nonempty α := by
    rw [← Order.cof_ne_zero_iff]; exact (aleph0_pos.trans hα).ne'
  -- a countable set is bounded, strictly
  have hbdd : ∀ s : Set α, s.Countable → ∃ x, ∀ y ∈ s, y < x := by
    intro s hs
    rw [← not_isCofinal_iff]
    intro hcof
    exact (Order.cof_le hcof).not_gt ((le_aleph0_iff_set_countable.2 hs).trans_lt hα)
  -- `T i`: the preimage of `B i` contains a tail
  let T : ι → Prop := fun i ↦ ∃ γ, ∀ a, γ ≤ a → g a ∈ B i
  let γ' : ι → α := fun i ↦ if h : T i then h.choose else Classical.arbitrary α
  obtain ⟨γ₀, hγ₀⟩ := hbdd (Set.range γ') (Set.countable_range γ')
  let F : ι → Set α := fun i ↦ if T i then Set.univ else {a | g a ∉ B i}
  have hF : ∀ i, IsClub (F i) := by
    intro i
    by_cases h : T i
    · simp only [F, if_pos h]; exact IsClub.univ
    · simp only [F, if_neg h]
      refine ⟨?_, ?_⟩
      · rw [dirSupClosed_iff_of_linearOrder]
        intro d hd hd₀ a ha
        by_contra hga
        simp only [Set.mem_setOf_eq, not_not] at hga
        have haD : a ∉ d := fun h' ↦ hd h' hga
        have hlim : IsSuccLimit a := ha.isSuccLimit_of_notMem hd₀ haD
        obtain ⟨b, hba, hb⟩ := hg a hlim (B i) ((hB i).mem_nhds hga)
        obtain ⟨c, hcd, hbc⟩ : ∃ c ∈ d, b < c := by
          by_contra hcon
          push Not at hcon
          exact (ha.2 (fun c hc ↦ hcon c hc)).not_gt hba
        have hca : c < a := lt_of_le_of_ne (ha.1 hcd) (fun h' ↦ haD (h' ▸ hcd))
        exact hd hcd (hb c hbc hca)
      · intro a
        simp only [T, not_exists, not_forall] at h
        obtain ⟨b, hab, hb⟩ := h a
        exact ⟨b, hb, hab⟩
  have hcard : Cardinal.lift.{u} #ι < Cardinal.lift.{v} (Order.cof α) :=
    (Cardinal.lift_le_aleph0.2 (Cardinal.mk_le_aleph0 (α := ι))).trans_lt
      (Cardinal.aleph0_lt_lift.2 hα)
  have hI : IsClub (⋂ i, F i) := IsClub.iInter hα.ne' hcard hF
  obtain ⟨δ, hδ, hγδ⟩ := hI.isCofinal γ₀
  have key : ∀ a, γ₀ ≤ a → g a = g δ := by
    intro a ha
    by_contra hne
    obtain ⟨i, hδi, hai⟩ := hsep (g δ) (g a) (Ne.symm hne)
    by_cases h : T i
    · have h1 : γ' i < γ₀ := hγ₀ _ ⟨i, rfl⟩
      have hγ'i : γ' i = h.choose := dif_pos h
      exact hai (h.choose_spec a (hγ'i ▸ h1.le |>.trans ha))
    · have h2 := Set.mem_iInter.1 hδ i
      simp only [F, if_neg h] at h2
      exact h2 hδi
  exact ⟨γ₀, fun a ha ↦ (key a ha).trans (key γ₀ le_rfl).symm⟩

/-- **A map continuous at limits from a well order of uncountable cofinality into a T1, second
countable space is eventually constant.** -/
theorem LimitContinuous.exists_forall_ge_eq [T1Space Y] [SecondCountableTopology Y]
    (hα : ℵ₀ < Order.cof α) {g : α → Y} (hg : LimitContinuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ := by
  haveI := (TopologicalSpace.countable_countableBasis Y).to_subtype
  refine hg.exists_forall_ge_eq_of_separating hα
    (B := fun s : TopologicalSpace.countableBasis Y ↦ s.1)
    (fun s ↦ TopologicalSpace.isOpen_of_mem_countableBasis s.2) (fun x y hxy ↦ ?_)
  obtain ⟨v, hv, hxv, hvy⟩ :=
    (TopologicalSpace.isBasis_countableBasis Y).exists_subset_of_mem_open
      (show x ∈ ({y}ᶜ : Set Y) from hxy) isOpen_compl_singleton
  exact ⟨⟨v, hv⟩, hxv, fun hy ↦ hvy hy rfl⟩

/-- Second countability weakened: it suffices that `Y` inject continuously into a T1, second
countable space (a coarser T1, second countable topology). -/
theorem LimitContinuous.exists_forall_ge_eq_of_injective {Z : Type x} [TopologicalSpace Z]
    [T1Space Z] [SecondCountableTopology Z] (hα : ℵ₀ < Order.cof α) {f : Y → Z}
    (hf : Continuous f) (hinj : Function.Injective f) {g : α → Y} (hg : LimitContinuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ := by
  have hfg : LimitContinuous (f ∘ g) := fun a ha U hU ↦ hg a ha _ (hf.continuousAt hU)
  obtain ⟨γ, hγ⟩ := hfg.exists_forall_ge_eq hα
  exact ⟨γ, fun a ha ↦ hinj (hγ a ha)⟩

/-- **A continuous map from a well order of uncountable cofinality, with its order topology, into
a T1, second countable space is eventually constant.** -/
theorem exists_forall_ge_eq_of_continuous [TopologicalSpace α] [OrderTopology α] [T1Space Y]
    [SecondCountableTopology Y] (hα : ℵ₀ < Order.cof α) {g : α → Y} (hg : Continuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ :=
  (limitContinuous_of_continuous hg).exists_forall_ge_eq hα

/-- The same conclusion as a filter statement: `g` is eventually constant along `atTop`. -/
theorem eventuallyConst_atTop_of_continuous [TopologicalSpace α] [OrderTopology α] [T1Space Y]
    [SecondCountableTopology Y] (hα : ℵ₀ < Order.cof α) {g : α → Y} (hg : Continuous g) :
    EventuallyConst g atTop := by
  have : Nonempty α := by
    rw [← Order.cof_ne_zero_iff]; exact (aleph0_pos.trans hα).ne'
  exact eventuallyConst_atTop.2 (exists_forall_ge_eq_of_continuous hα hg)

/-- The cofinality hypothesis at its weakest: on a non-empty well order, `cof α ≠ ℵ₀` suffices (a
well order of cofinality `≤ 1` has a top, where every map is constant). `cof α = ℵ₀` does not
(`nat_separates`). -/
theorem LimitContinuous.exists_forall_ge_eq_of_cof_ne_aleph0 [Nonempty α] [T1Space Y]
    [SecondCountableTopology Y] (hα : Order.cof α ≠ ℵ₀) {g : α → Y} (hg : LimitContinuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ := by
  by_cases h1 : Order.cof α ≤ 1
  · obtain ⟨x, hx⟩ := (Order.cof_le_one_iff).1 h1
    exact ⟨x, fun a ha ↦ congrArg g (le_antisymm (hx a) ha)⟩
  · have h2 : ℵ₀ ≤ Order.cof α := Order.aleph0_le_cof_iff.2 (not_le.1 h1)
    exact hg.exists_forall_ge_eq (h2.lt_of_ne' hα)

end General

/-! ## 3. At ω₁ -/

section OmegaOne

open Ordinal

variable {Y : Type w} [TopologicalSpace Y]

/-- The ordinals below `ω₁` have uncountable cofinality (`ℵ₁`, lifted). -/
theorem aleph0_lt_cof_Iio_omega_one : ℵ₀ < Order.cof (Iio (ω₁ : Ordinal.{u})) := by
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, Cardinal.cof_omega_one]
  exact Cardinal.aleph0_lt_lift.2 Cardinal.aleph0_lt_aleph_one

/-- Every tail `[γ, ω₁)` holds a limit ordinal: `γ + ω` (`ω₁` is additively principal). -/
theorem exists_isSuccLimit_ge_lt_omega_one {γ : Ordinal.{u}} (hγ : γ < ω₁) :
    ∃ l, γ ≤ l ∧ l < ω₁ ∧ IsSuccLimit l :=
  ⟨γ + ω, le_self_add, isPrincipal_add_omega 1 hγ omega0_lt_omega_one,
    isSuccLimit_add _ isSuccLimit_omega0⟩

/-- **The target's statement**: a continuous map from `ω₁` (the ordinals below it, with the order
topology) into a T1, second countable space is eventually constant. -/
theorem exists_forall_ge_eq_of_continuous_omega_one [T1Space Y] [SecondCountableTopology Y]
    {g : Iio (ω₁ : Ordinal.{u}) → Y} (hg : Continuous g) :
    ∃ γ, ∀ a, γ ≤ a → g a = g γ :=
  exists_forall_ge_eq_of_continuous aleph0_lt_cof_Iio_omega_one hg

/-- **The target's statement, in its limit form, for a map on the ordinals read below `ω₁`**: if
`g λ` is the limit of `g β`, `β → λ`, at every limit `λ < ω₁`, then some `γ < ω₁` has
`g α = g γ` for every `α ∈ [γ, ω₁)`. The form `T-abs-curves-extend-second-countable` consumes. -/
theorem exists_lt_omega_one_forall_eq [T1Space Y] [SecondCountableTopology Y]
    {g : Ordinal.{u} → Y}
    (hg : ∀ a < ω₁, IsSuccLimit a → ∀ U ∈ 𝓝 (g a), ∃ b < a, ∀ c, b < c → c < a → g c ∈ U) :
    ∃ γ < ω₁, ∀ a, γ ≤ a → a < ω₁ → g a = g γ := by
  have hg' : LimitContinuous (fun a : Iio (ω₁ : Ordinal.{u}) ↦ g a) := by
    intro a ha U hU
    obtain ⟨b, hb, h⟩ := hg a a.2 (ha.subtypeVal (isLowerSet_Iio _)) U hU
    exact ⟨⟨b, hb.trans a.2⟩, hb, fun c hbc hca ↦ h c hbc hca⟩
  obtain ⟨γ, hγ⟩ := hg'.exists_forall_ge_eq aleph0_lt_cof_Iio_omega_one
  exact ⟨γ, γ.2, fun a hγa ha ↦ hγ ⟨a, ha⟩ hγa⟩

/-- The limit form with `Tendsto` and the order topology of `Ordinal`: `g` tends to `g λ` from
the left at every limit `λ < ω₁`. -/
theorem exists_lt_omega_one_forall_eq_of_tendsto [T1Space Y] [SecondCountableTopology Y]
    {g : Ordinal.{u} → Y} (hg : ∀ a < ω₁, IsSuccLimit a → Tendsto g (𝓝[<] a) (𝓝 (g a))) :
    ∃ γ < ω₁, ∀ a, γ ≤ a → a < ω₁ → g a = g γ := by
  refine exists_lt_omega_one_forall_eq fun a ha hl U hU ↦ ?_
  obtain ⟨b, hba⟩ := hl.nonempty_Iio
  obtain ⟨l, hl', hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hba).1 (hg a ha hl hU)
  exact ⟨l, hl', fun c hlc hca ↦ hsub ⟨hlc, hca⟩⟩

/-- The continuous form for a map on the ordinals: continuous on `[0, ω₁)`. -/
theorem exists_lt_omega_one_forall_eq_of_continuousOn [T1Space Y] [SecondCountableTopology Y]
    {g : Ordinal.{u} → Y} (hg : ContinuousOn g (Iio ω₁)) :
    ∃ γ < ω₁, ∀ a, γ ≤ a → a < ω₁ → g a = g γ := by
  obtain ⟨γ, hγ⟩ := exists_forall_ge_eq_of_continuous_omega_one hg.restrict
  exact ⟨γ, γ.2, fun a hγa ha ↦ hγ ⟨a, ha⟩ hγa⟩

/-- **Countably many maps, one bound**: a countable family of maps, each continuous at the limits
below `ω₁`, are all constant on one tail `[γ, ω₁)` (the supremum of the countably many bounds is
below `ω₁`, `Ordinal.iSup_lt_omega_one`). -/
theorem exists_lt_omega_one_forall_eq_family [T1Space Y] [SecondCountableTopology Y]
    {ι : Type v} [Countable ι] {g : ι → Ordinal.{u} → Y}
    (hg : ∀ i, ∀ a < ω₁, IsSuccLimit a → ∀ U ∈ 𝓝 (g i a),
      ∃ b < a, ∀ c, b < c → c < a → g i c ∈ U) :
    ∃ γ < ω₁, ∀ i a, γ ≤ a → a < ω₁ → g i a = g i γ := by
  choose γ hγ₁ hγ using fun i ↦ exists_lt_omega_one_forall_eq (hg i)
  have hbdd : BddAbove (Set.range γ) := Ordinal.bddAbove_of_small
  have hsup : ⨆ i, γ i < ω₁ := Ordinal.iSup_lt_omega_one hγ₁
  refine ⟨⨆ i, γ i, hsup, fun i a ha ha' ↦ ?_⟩
  have hi : γ i ≤ ⨆ i, γ i := le_ciSup hbdd i
  exact (hγ i a (hi.trans ha) ha').trans (hγ i _ hi hsup).symm

end OmegaOne

/-! ## 4. Each hypothesis is needed -/

section Sharp

open Ordinal

/-- **Cofinality `ℵ₀` is not enough**: `ℕ` (cofinality `ℵ₀`, no limit points, so every map is
continuous at limits) and its identity into the discrete, T2, second countable `ℕ`, which is not
eventually constant. -/
theorem nat_separates :
    T2Space ℕ ∧ SecondCountableTopology ℕ ∧ Order.cof ℕ = ℵ₀ ∧
      LimitContinuous (fun n : ℕ ↦ n) ∧ ¬ ∃ γ : ℕ, ∀ a, γ ≤ a → a = γ := by
  refine ⟨inferInstance, inferInstance, Order.cof_nat, fun a ha ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · exact absurd ha not_isSuccLimit_of_isSuccArchimedean
  · exact absurd (hγ (γ + 1) (Nat.le_succ γ)) (Nat.succ_ne_self γ)

/-- Sierpiński space (`Prop`, `{True}` open) is T0. -/
theorem t0Space_prop : T0Space Prop := by
  refine (t0Space_iff_inseparable Prop).2 fun p q h ↦ ?_
  have h' : 𝓝 p = 𝓝 q := h
  have key : ∀ r s : Prop, r → ¬ s → 𝓝 r ≠ 𝓝 s := by
    intro r s hr hs hrs
    rw [eq_true hr, eq_false hs, nhds_true, nhds_false] at hrs
    have h2 : ({True} : Set Prop) ∈ (⊤ : Filter Prop) := hrs ▸ Filter.mem_pure.2 rfl
    rw [Filter.mem_top] at h2
    have h3 : False ∈ ({True} : Set Prop) := h2 ▸ trivial
    exact (h3 : False = True) ▸ trivial
  by_cases hp : p <;> by_cases hq : q
  · exact propext ⟨fun _ ↦ hq, fun _ ↦ hp⟩
  · exact absurd h' (key p q hp hq)
  · exact absurd h'.symm (key q p hq hp)
  · exact propext ⟨fun h ↦ absurd h hp, fun h ↦ absurd h hq⟩

/-- The non-limit ordinals form an open set: each is isolated. -/
theorem isOpen_setOf_not_isSuccLimit : IsOpen {o : Ordinal.{u} | ¬ IsSuccLimit o} :=
  isOpen_iff_forall_mem_open.2 fun o ho ↦
    ⟨{o}, by simpa using ho, SuccOrder.isOpen_singleton_iff.2 ho, rfl⟩

/-- **T1 cannot be weakened to T0**: Sierpiński space is T0 and second countable, and "is not a
limit" is a continuous map `ω₁ → Prop` that is not eventually constant (above every `γ < ω₁`
lie the successor `γ + 1` and the limit `γ + ω`). -/
theorem sierpinski_separates :
    T0Space Prop ∧ SecondCountableTopology Prop ∧
      ∃ g : Iio (ω₁ : Ordinal.{u}) → Prop, Continuous g ∧ ¬ ∃ γ, ∀ a, γ ≤ a → g a = g γ := by
  refine ⟨t0Space_prop, inferInstance, fun a ↦ ¬ IsSuccLimit (a : Ordinal), ?_, ?_⟩
  · exact continuous_Prop.2 (isOpen_setOf_not_isSuccLimit.preimage continuous_subtype_val)
  · rintro ⟨γ, hγ⟩
    by_cases h : IsSuccLimit (γ : Ordinal)
    · have hlt : (γ : Ordinal) + 1 < ω₁ := by
        rw [← Order.succ_eq_add_one]; exact (isSuccLimit_omega 1).succ_lt γ.2
      have := hγ ⟨_, hlt⟩ (show (γ : Ordinal) ≤ γ + 1 from le_self_add)
      simp only [eq_iff_iff] at this
      exact (this.1 (by rw [← Order.succ_eq_add_one]; exact not_isSuccLimit_succ _)) h
    · obtain ⟨l, hγl, hl, hlim⟩ := exists_isSuccLimit_ge_lt_omega_one γ.2
      have := hγ ⟨l, hl⟩ hγl
      simp only [eq_iff_iff] at this
      exact (this.2 h) hlim

/-- A countable ordinal has countably many predecessors. -/
theorem countable_Iio_of_lt_omega_one {o : Ordinal.{u}} (ho : o < ω₁) : (Iio o).Countable := by
  rw [← le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0,
    ← lt_aleph_one_iff, ← lt_ord, ord_aleph]
  exact ho

/-- `ω₁` is first countable: at `a`, the intervals `(b, a]`, `b < a`, are countably many and form
a neighbourhood basis (or `{a}` is open). -/
theorem firstCountableTopology_Iio_omega_one :
    FirstCountableTopology (Iio (ω₁ : Ordinal.{u})) := by
  haveI : NoMaxOrder (Iio (ω₁ : Ordinal.{u})) :=
    (isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio
  refine ⟨fun a ↦ ?_⟩
  have hgt : 𝓝[>] a = ⊥ := by
    rw [nhdsGT_eq_bot_iff]
    exact Or.inr (exists_covBy_of_wellFoundedLT (not_isMax a))
  have hlt : (𝓝[<] a).IsCountablyGenerated := by
    by_cases h : ∃ b, b < a
    · refine HasCountableBasis.isCountablyGenerated ⟨nhdsLT_basis_of_exists_lt h, ?_⟩
      have : {b : Iio (ω₁ : Ordinal.{u}) | b < a} = Subtype.val ⁻¹' Iio (a : Ordinal) := rfl
      rw [this]
      exact (countable_Iio_of_lt_omega_one a.2).preimage Subtype.val_injective
    · push Not at h
      have : Iio a = ∅ := Set.eq_empty_iff_forall_notMem.2 fun b hb ↦ (h b).not_gt hb
      rw [this, nhdsWithin_empty]
      exact isCountablyGenerated_bot
  haveI := isCountablyGenerated_pure a
  rw [← nhdsLE_sup_nhdsGT, hgt, sup_bot_eq, ← Iio_insert, nhdsWithin_insert]
  infer_instance

/-- **Second countability cannot be weakened to first countability, even with T2**: `ω₁` itself
is T2 and first countable, and its identity is not eventually constant. -/
theorem omega_one_id_separates :
    T2Space (Iio (ω₁ : Ordinal.{u})) ∧ FirstCountableTopology (Iio (ω₁ : Ordinal.{u})) ∧
      ¬ ∃ γ : Iio (ω₁ : Ordinal.{u}), ∀ a, γ ≤ a → a = γ := by
  refine ⟨inferInstance, firstCountableTopology_Iio_omega_one, fun ⟨γ, hγ⟩ ↦ ?_⟩
  have hlt : succ (γ : Ordinal) < ω₁ := (isSuccLimit_omega 1).succ_lt γ.2
  have := congrArg Subtype.val
    (hγ ⟨_, hlt⟩ (Subtype.coe_le_coe.1 (show (γ : Ordinal) ≤ succ (γ : Ordinal) from le_succ _)))
  exact (lt_succ (γ : Ordinal)).ne' this

end Sharp

end Causal
