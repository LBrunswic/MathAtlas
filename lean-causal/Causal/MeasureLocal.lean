import Causal.MeasureSum
import Causal.ArcConnected
import Causal.Measure

/-!
# Admissible measures from local to global

**`prop:mesure_dieckmann_topo`** — `ETT.tex:1094`.

> Let $M$ be a causally arc-connected, strongly causal topological spacetime. Assume that
> (i) for every $p\in M$ there is an open neighbourhood $\U_p$ of $p$, causally convex in $M$,
> carrying a measure admissible in the past; (ii) for every $p\in M$ and every $q\leq p$,
> $K^-(q)\subset K^-(p)$. Then $M$ carries a measure admissible in the past. The symmetric
> statement holds in the future.

> Since $M$ is second countable, there exists a family $(\U_n)_{n\in \N}$ of open subsets of
> $M$ covering $M$ and such that for every $n\in \N$ the set $\U_n$ carries a measure admissible
> in the past and is causally convex in $M$. For every $n\in \N$ choose such a measure $\mu_n$
> on $\U_n$, normalised so that $\mu_n(\U_n)=1$. Set $\mu := \sum_{n\in \N} 2^{-n-1} \mu_n$.

The paper's statement, with the paper's hypotheses, is `mesure_dieckmann_topo_past` and
`mesure_dieckmann_topo_future`; the theorems under the hypotheses the proof uses are
`exists_admissiblePast_of_local` and `exists_admissibleFuture_of_local`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| causally arc-connected | ✓ carried |
| strongly causal | ⚠ weakened: not used (carried, unused, in `mesure_dieckmann_topo_*`) |
| second countable (`def:category_topological_spacetimes`) | ⚠ weakened: `LindelofSpace M` — the proof uses only a countable subcover of `(U_p)` |
| Hausdorff (`def:category_topological_spacetimes`) | ⚠ weakened: `R1Space M` — used for the regularity of the sum |
| "regular Borel measure" | ✓ carried: `BorelSpace M`, `μ.Regular` |
| (i) a causally convex open neighbourhood `U_p` carrying a measure admissible in the past | ✓ carried: `AdmissiblePastOn`, a measure on `M` carried by `U_p` (see SCOPE) |
| (ii) `q ≤ p ⇒ K^-(q) ⊂ K^-(p)` | ✓ carried; used for property 4. only |
| the future statement, "symmetric" | ✓ carried: (i) with `AdmissibleFutureOn`, (ii) as `p ≤ q ⇒ K^+(q) ⊂ K^+(p)`, the time reversal |

## SCOPE (disclosed)

* **A measure on the open set `U` is a measure on `M` carried by `U`** (`kb/0001`: no subtype in
  a statement): `AdmissiblePastOn U ν` asks `ν Uᶜ = 0`, `ν` regular on `M`, `ν(M) < ∞`, and
  properties 3. and 4. with `J^-_U`, `K^-_U` (for every `A ⊂ U`). What is proved of the reading:
  for `ν` a measure on the subspace `U`, `AdmissiblePastOn U (map val ν)` holds iff `ν` is regular,
  finite, and satisfies 3. and 4. on the sets `val⁻¹'(J^-_U(q) ∖ J^-_U(p))` and
  `val⁻¹'(J^-_U(A) ∖ K^-_U(A))` (`admissiblePastOn_map_subtype_iff`, in an R₁ space); and every
  measure admissible on `U` is such a push-forward (`AdmissiblePastOn.exists_subtype`). Not
  proved: that these traces are the `J^-` and `K^-` of a causality on the type `↥U` — the library
  has no restricted causality on a subtype (`kb/0001`); `K^-_U` is computed with sequences of `M`,
  which agrees with sequences of `U` for points of `U` (`mem_Kminus_singleton_iff_seq_mem`).
* **The normalisation `μ_n(U_n) = 1` is not used and is not always possible**: a measure
  admissible in the past on `U_n` may be zero (when `U_n` contains no pair `p <_{U_n} q`). The
  weights are `c_n > 0`, finite, with `∑ c_n μ_n(U_n) < ∞` (`exists_weights_tsum_lt`).
* **"μ is a regular Borel measure" is proved** (`regular_sum`): a countable sum of regular
  measures need not be outer regular term by term; with finite total mass it is.
* The first step of property 3. ("there exist `n_0` and `q' ∈ U_{n_0}` such that `p ∈ U_{n_0}`
  and `p <_{U_{n_0}} q'` with `q' ≤ q`") is the first link leaving `p` of the chain given by
  `cor:causalement_connexe_minimal` (`transGen_exists_first_ne`).
* `admissiblePast_local_of_admissiblePast`: hypothesis (i) is necessary — if `M` carries a
  measure admissible in the past, `U_p = M` does.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory Relation

open scoped ENNReal

universe u

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M]

namespace Causality

variable (C : Causality M)

/-- `defi:mesure_dieckmann`, past, for the open subset `W` seen as a spacetime: a measure on `W`
is a measure on `M` carried by `W`. -/
structure AdmissiblePastOn (W : Opens M) (μ : Measure M) : Prop where
  /-- `μ` is a measure on `W`. -/
  carried : μ (W : Set M)ᶜ = 0
  /-- 1. -/
  regular : μ.Regular
  /-- 2. -/
  finite : μ univ < ∞
  /-- 3. -/
  pos : ∀ ⦃p q : M⦄, C.le W p q → p ≠ q → 0 < μ (C.Jminus W {q} \ C.Jminus W {p})
  /-- 4. -/
  null : ∀ A : Set M, A ⊆ W → μ (C.Jminus W A \ C.Kminus W A) = 0

/-- `defi:mesure_dieckmann`, future, for the open subset `W` seen as a spacetime. -/
structure AdmissibleFutureOn (W : Opens M) (μ : Measure M) : Prop where
  /-- `μ` is a measure on `W`. -/
  carried : μ (W : Set M)ᶜ = 0
  /-- 1. -/
  regular : μ.Regular
  /-- 2. -/
  finite : μ univ < ∞
  /-- 3. -/
  pos : ∀ ⦃p q : M⦄, C.le W p q → p ≠ q → 0 < μ (C.Jplus W {p} \ C.Jplus W {q})
  /-- 4. -/
  null : ∀ A : Set M, A ⊆ W → μ (C.Jplus W A \ C.Kplus W A) = 0

variable {C} {W : Opens M} {μ : Measure M}

theorem dual_admissiblePastOn : C.dual.AdmissiblePastOn W μ ↔ C.AdmissibleFutureOn W μ :=
  ⟨fun h => ⟨h.carried, h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩,
    fun h => ⟨h.carried, h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne),
      h.null⟩⟩

theorem dual_admissibleFutureOn : C.dual.AdmissibleFutureOn W μ ↔ C.AdmissiblePastOn W μ :=
  ⟨fun h => ⟨h.carried, h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩,
    fun h => ⟨h.carried, h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne),
      h.null⟩⟩

/-- On `W = M` the local notion is the notion of `Causal.Measure`. -/
theorem admissiblePastOn_top : C.AdmissiblePastOn ⊤ μ ↔ C.AdmissiblePast μ :=
  ⟨fun h => ⟨h.regular, h.finite, h.pos, fun A => h.null A fun _ _ => trivial⟩,
    fun h => ⟨by rw [Opens.coe_top, compl_univ, measure_empty], h.regular, h.finite, h.pos,
      fun A _ => h.null A⟩⟩

theorem admissibleFutureOn_top : C.AdmissibleFutureOn ⊤ μ ↔ C.AdmissibleFuture μ := by
  rw [← dual_admissiblePastOn, admissiblePastOn_top, dual_admissiblePast]

/-- The reading of `AdmissiblePastOn`: the push-forward to `M` of a measure `ν` on the subspace
`U` is admissible in the past on `U` iff `ν` is regular, finite, and satisfies properties 3. and
4. for the traces on `U` of `J^-_U` and `K^-_U` (`val⁻¹'`). -/
theorem admissiblePastOn_map_subtype_iff [R1Space M] [BorelSpace M] {U : Opens M}
    (ν : Measure (U : Set M)) :
    C.AdmissiblePastOn U (Measure.map Subtype.val ν) ↔
      ν.Regular ∧ ν univ < ∞ ∧
      (∀ ⦃p q : M⦄, C.le U p q → p ≠ q →
        0 < ν (Subtype.val ⁻¹' (C.Jminus U {q} \ C.Jminus U {p}))) ∧
      (∀ A : Set M, A ⊆ U →
        ν (Subtype.val ⁻¹' (C.Jminus U A \ C.Kminus U A)) = 0) := by
  have he := MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hmap : ∀ s, Measure.map Subtype.val ν s = ν (Subtype.val ⁻¹' s) := he.map_apply ν
  constructor
  · intro h
    refine ⟨?_, by simpa [hmap] using h.finite, fun p q hpq hne => by
      simpa [hmap] using h.pos hpq hne, fun A hA => by simpa [hmap] using h.null A hA⟩
    haveI := h.regular
    have := Measure.Regular.comap' (Measure.map Subtype.val ν) U.isOpen.isOpenEmbedding_subtypeVal
    rwa [he.comap_map] at this
  · rintro ⟨hreg, hfin, hpos, hnull⟩
    haveI := hreg
    haveI : IsFiniteMeasure ν := ⟨hfin⟩
    exact ⟨map_subtype_val_compl_null U.isOpen ν, regular_map_subtype_val ν,
      measure_lt_top _ _, fun p q hpq hne => by simpa [hmap] using hpos hpq hne,
      fun A hA => by simpa [hmap] using hnull A hA⟩

/-- `admissiblePastOn_map_subtype_iff`, future. -/
theorem admissibleFutureOn_map_subtype_iff [R1Space M] [BorelSpace M] {U : Opens M}
    (ν : Measure (U : Set M)) :
    C.AdmissibleFutureOn U (Measure.map Subtype.val ν) ↔
      ν.Regular ∧ ν univ < ∞ ∧
      (∀ ⦃p q : M⦄, C.le U p q → p ≠ q →
        0 < ν (Subtype.val ⁻¹' (C.Jplus U {p} \ C.Jplus U {q}))) ∧
      (∀ A : Set M, A ⊆ U →
        ν (Subtype.val ⁻¹' (C.Jplus U A \ C.Kplus U A)) = 0) := by
  rw [← dual_admissiblePastOn, admissiblePastOn_map_subtype_iff (C := C.dual)]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, fun _ _ hpq hne => h3 hpq (Ne.symm hne), h4⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, fun _ _ hpq hne => h3 hpq (Ne.symm hne), h4⟩⟩

/-- Every measure admissible in the past on `U` is such a push-forward. -/
theorem AdmissiblePastOn.exists_subtype [R1Space M] [BorelSpace M] {U : Opens M}
    (h : C.AdmissiblePastOn U μ) :
    ∃ ν : Measure (U : Set M), Measure.map Subtype.val ν = μ := by
  haveI := h.regular
  obtain ⟨ν, -, hν⟩ := exists_regular_subtype_of_compl_null U.isOpen h.carried
  exact ⟨ν, hν⟩

/-- Every measure admissible in the future on `U` is such a push-forward. -/
theorem AdmissibleFutureOn.exists_subtype [R1Space M] [BorelSpace M] {U : Opens M}
    (h : C.AdmissibleFutureOn U μ) :
    ∃ ν : Measure (U : Set M), Measure.map Subtype.val ν = μ :=
  AdmissiblePastOn.exists_subtype (C := C.dual) (dual_admissiblePastOn.2 h)

/-- A chain of steps from `a` to `b ≠ a` has a first step leaving `a`. -/
theorem transGen_exists_first_ne {α : Type*} {r : α → α → Prop} {a b : α} (h : TransGen r a b)
    (hab : a ≠ b) : ∃ c, r a c ∧ a ≠ c ∧ ReflTransGen r c b := by
  revert hab
  induction h using TransGen.head_induction_on with
  | single hl => exact fun hab => ⟨_, hl, hab, ReflTransGen.refl⟩
  | @head a' c' hl hcb ih =>
    intro hab
    by_cases hac : a' = c'
    · subst hac
      exact ih hab
    · exact ⟨c', hl, hac, hcb.to_reflTransGen⟩

/-- `prop:mesure_dieckmann_topo`, past, under the hypotheses the proof uses. -/
theorem exists_admissiblePast_of_local [R1Space M] [LindelofSpace M] [BorelSpace M]
    (hac : C.CausallyArcConnected)
    (hloc : ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      ∃ ν : Measure M, C.AdmissiblePastOn U ν)
    (hK : ∀ p q : M, C.le ⊤ q p → C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p}) :
    ∃ μ : Measure M, C.AdmissiblePast μ := by
  choose U hpU hconv ν hν using hloc
  -- a countable subcover: the only use of second countability
  obtain ⟨t, htc, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun p => (U p : Set M))
    (fun p => (U p).isOpen.mem_nhds (hpU p))
  haveI : Countable t := htc.to_subtype
  have hcov : ∀ x : M, ∃ i : t, x ∈ U i := fun x => by
    have hx : x ∈ ⋃ p ∈ t, (U p : Set M) := hcover ▸ mem_univ x
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    exact ⟨⟨p, hp⟩, hxp⟩
  -- the weights
  obtain ⟨c, hc0, hctop, hcsum⟩ :=
    exists_weights_tsum_lt (fun i : t => ν i univ) (fun i => (hν i).finite.ne)
  have hfin : Measure.sum (fun i : t => c i • ν i) univ < ∞ := by
    rw [sum_smul_apply]
    exact hcsum
  refine ⟨Measure.sum (fun i : t => c i • ν i), ⟨?_, hfin, ?_, ?_⟩⟩
  -- 1.
  · exact regular_sum (fun i => by
      haveI := (hν i).regular
      exact Measure.Regular.smul (hctop i)) hfin
  -- 3.
  · intro p q hpq hne
    have hchain := (CausallyArcConnectedOn.absolutelyMinimalOn hac).linkLe_of_family
      (fun i : t => U i) (fun x _ => hcov x) le_rfl hpq
    obtain ⟨q', ⟨i, hpq'⟩, hne', hrt⟩ := transGen_exists_first_ne hchain hne
    have hpq'U : C.le (U i) p q' := by simpa using hpq'
    have hq'q : C.le ⊤ q' q := by
      clear hchain hpq hne
      induction hrt with
      | refl => exact C.le_refl trivial
      | tail _ hl ih =>
        obtain ⟨j, hj⟩ := hl
        exact C.le_trans ih (C.le_mono le_top hj)
    have hpU' : p ∈ U i := C.le_mem_left hpq'U
    have hsub : C.Jminus (U i) {q'} \ C.Jminus (U i) {p} ⊆
        C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} := by
      rintro x ⟨hxq', hxp⟩
      have hxU : x ∈ U i := Precausality.Jminus_subset_carrier hxq'
      refine ⟨?_, fun hx => hxp ?_⟩
      · rw [Precausality.mem_Jminus_singleton] at hxq' ⊢
        exact C.le_trans (C.le_mono le_top hxq') hq'q
      · rw [Jminus_eq_inter_of_causallyConvexIn hac (hconv i) (singleton_subset_iff.2 hpU')]
        exact ⟨hx, hxU⟩
    have hpos : 0 < c i * ν i (C.Jminus (U i) {q'} \ C.Jminus (U i) {p}) :=
      ENNReal.mul_pos (hc0 i) ((hν i).pos hpq'U hne').ne'
    refine lt_sum_apply_of_lt _ _ i ?_
    rw [Measure.smul_apply, smul_eq_mul]
    refine hpos.trans_le ?_
    gcongr
  -- 4.
  · intro A
    rw [sum_apply_eq_zero_iff]
    intro i
    rw [Measure.smul_apply, smul_eq_mul]
    refine mul_eq_zero_of_right _ ?_
    have hBU : C.Jminus ⊤ A ∩ U i ⊆ U i := inter_subset_right
    rw [measure_eq_inter_of_compl_null (hν i).carried]
    refine measure_mono_null ?_ ((hν i).null _ hBU)
    rintro x ⟨⟨hxJ, hxK⟩, hxU⟩
    refine ⟨Precausality.subset_Jminus hBU ⟨hxJ, hxU⟩, fun hx => hxK ?_⟩
    rw [Kminus_eq_inter_of_causallyConvexIn hac (hconv i) hBU] at hx
    have hx1 := hx.1
    rw [Kminus_eq_biUnion] at hx1
    obtain ⟨b, ⟨⟨a, ha, hba⟩, -⟩, hxb⟩ := mem_iUnion₂.1 hx1
    exact Kminus_mono (singleton_subset_iff.2 ha) (hK a b hba hxb)

/-- `prop:mesure_dieckmann_topo`, future, under the hypotheses the proof uses. -/
theorem exists_admissibleFuture_of_local [R1Space M] [LindelofSpace M] [BorelSpace M]
    (hac : C.CausallyArcConnected)
    (hloc : ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      ∃ ν : Measure M, C.AdmissibleFutureOn U ν)
    (hK : ∀ p q : M, C.le ⊤ p q → C.Kplus ⊤ {q} ⊆ C.Kplus ⊤ {p}) :
    ∃ μ : Measure M, C.AdmissibleFuture μ := by
  obtain ⟨μ, hμ⟩ := exists_admissiblePast_of_local (C := C.dual)
    (dual_causallyArcConnectedOn.2 hac)
    (fun p => by
      obtain ⟨U, hp, hc, ν, hν⟩ := hloc p
      exact ⟨U, hp, dual_causallyConvexIn.2 hc, ν, dual_admissiblePastOn.2 hν⟩)
    hK
  exact ⟨μ, dual_admissiblePast.1 hμ⟩

/-- **`prop:mesure_dieckmann_topo`**, past, with the paper's hypotheses: a causally
arc-connected, strongly causal topological spacetime (second countable, Hausdorff). -/
theorem mesure_dieckmann_topo_past [T2Space M] [SecondCountableTopology M] [BorelSpace M]
    (hac : C.CausallyArcConnected) (_hsc : C.StronglyCausal)
    (hloc : ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      ∃ ν : Measure M, C.AdmissiblePastOn U ν)
    (hK : ∀ p q : M, C.le ⊤ q p → C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p}) :
    ∃ μ : Measure M, C.AdmissiblePast μ :=
  exists_admissiblePast_of_local hac hloc hK

/-- **`prop:mesure_dieckmann_topo`**, future: "the symmetric statement holds in the future". -/
theorem mesure_dieckmann_topo_future [T2Space M] [SecondCountableTopology M] [BorelSpace M]
    (hac : C.CausallyArcConnected) (_hsc : C.StronglyCausal)
    (hloc : ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      ∃ ν : Measure M, C.AdmissibleFutureOn U ν)
    (hK : ∀ p q : M, C.le ⊤ p q → C.Kplus ⊤ {q} ⊆ C.Kplus ⊤ {p}) :
    ∃ μ : Measure M, C.AdmissibleFuture μ :=
  exists_admissibleFuture_of_local hac hloc hK

/-- Hypothesis (i) of `prop:mesure_dieckmann_topo` is necessary: a measure admissible in the past
on `M` is admissible in the past on the causally convex open neighbourhood `M` of every point. -/
theorem admissiblePast_local_of_admissiblePast (hμ : C.AdmissiblePast μ) :
    ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      ∃ ν : Measure M, C.AdmissiblePastOn U ν :=
  fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, μ,
    admissiblePastOn_top.2 hμ⟩

end Causality

end Causal
