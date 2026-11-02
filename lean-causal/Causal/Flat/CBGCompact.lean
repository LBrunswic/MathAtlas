import Causal.Flat.GerochFlat
import Causal.Flat.CauchyComplete
import Causal.CurvesExtend

/-!
# `J⁻(p) ∩ Σ` and `J⁺(p) ∩ Σ` are compact for a Cauchy surface `Σ`, without limit curves

R1's last input for the flat instance of the CBG campaign (design `docs/CBG-DESIGN.md` §5, risk
R1; `Flat/CBG.lean`'s `flat_isCompact_Jminus_inter_of_isCauchySurface` and its past form, which
this module discharges). **No label is marked**: the result is an input of `theo:CBG`
(`ETT.tex:1884`), which the CBG campaign does not mark (`docs/CBG-DESIGN.md:5–6`). Cited, unmarked:
O'Neill 14.40ff, Hawking–Ellis 6.6 (the classical statement, proved there by limit curves).

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism. (`theo:CBG`, `ETT.tex:1885–1886`)

> Risks: R1 `sigmaCompact` (compactness of J⁺(Σ) ∩ J⁻(p)) (`docs/CBG-DESIGN.md` §5)

## What is proved

* **The general theorem** `Causality.isCompact_Jminus_inter_of_isCauchySurface` (model-free,
  sorry-free): in a T2 locally compact causality, causal (`IsCausal`), causally arc-connected,
  with **closed** causal relation, a continuous `τ` strictly increasing along `≤`, and `J⁻(W)` open
  for every open `W`, if `Σ` is an acausal Cauchy surface with `J^±(Σ)` closed then `J⁻(p) ∩ Σ` is
  compact for every `p`. **Compactness of diamonds is not used**; it enters the flat instance only
  through the closedness of `≤` (`GloballyHyperbolic.isClosed_le`) and the time function.
* **Its GH form** `Causality.GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface` and the
  past forms `isCompact_Jplus_inter_of_isCauchySurface` (by `C.dual`, kb/0002).
* **The flat instance** `flat_isCompact_Jminus_inter_cauchy`, `flat_isCompact_Jplus_inter_cauchy`
  (sorry-free), with **exactly** the hypotheses and conclusion of
  `CBG.flat_isCompact_Jminus_inter_of_isCauchySurface` / `…Jplus…` of `Flat/CBG.lean`: the time
  function is the Geroch time (`exists_admissible_measure`, `geroch_i_imp_ii`), openness of `J^∓`
  of open sets is push-up along the chronal causal flow (`flat_hasChronalCausalFlow`,
  `flatCausality_pushUp`), closedness of `J^±(Σ)` is the Cauchy splitting.

## The proof: Zorn on time graphs instead of limit curves

Call `x` **past-noncompact** (`PastNoncompactAt Σ x`) if for every neighbourhood `V` of `x`,
`J⁻(V) ∩ Σ` lies in no compact set. Let `B` be the set of such points.
1. `B` is closed (`pastNoncompactAt_of_mem_closure`), and a future set: `x ∈ B`, `x ≤ w` ⇒ `w ∈ B`
   (`PastNoncompactAt.of_le`; `J⁻(int W)` is an open neighbourhood of `x`).
2. **The step** (`exists_pastNoncompactAt_frontier`): for `y ∈ B` and a compact `N` with
   `y ∈ int N`, some `z ∈ ∂N ∩ J⁻(y) ∩ J⁺(Σ)` is in `B`. Otherwise finitely many neighbourhoods
   `W_z` with `J⁻(W_z) ∩ Σ` bounded cover the compact `Z = ∂N ∩ J⁻(y) ∩ J⁺(Σ)`; the points `ℓ ∈ N`
   above some `z ∈ ∂N ∩ J⁺(Σ) ∖ W` form a compact set (closed relation) missing `y`; off it, every
   `x ∈ Σ ∩ J⁻(ℓ)` outside `N` reaches `ℓ` through a frontier point (`exists_frontier_of_le`, a
   causal curve and connectedness), which lies in `W`: `y ∉ B`. In particular `B ∩ Σ = ∅` (a point
   of `Σ` has no `z ≠ y` in `J⁻(y) ∩ J⁺(Σ)`, `Σ` acausal).
3. **Zorn** (`CurvesExtend.lean`'s time graphs, ordered by inclusion, now constrained to lie in `B`):
   if `p ∈ B`, a maximal time graph `K ⊆ B` exists. It has no least point (the step, then
   `exists_prepend`: the prepended arc lies above a point of `B`). It is **inextensible**: a strict
   extension `c'` either adds a point above a point of `K` (the up-closure lies in `B`, so it is in
   `K` by maximality), or only points below all of `K`; then `c'(inf)` is in `closure K ⊆ B`, the arc
   above it lies in `B`, so `c'(inf) ∈ K` is its least point — excluded.
4. `Σ` is Cauchy, so the inextensible `K` meets `Σ`, inside `B`: contradiction. So `p ∉ B`, and
   `J⁻(p) ∩ Σ` (closed) lies in a compact set.

## Hypothesis checklist

| paper / design | here |
|---|---|
| `M` globally hyperbolic (ETT `def:globally_hyperbolic`, `Causal/Properties.lean:144`) | ✓ carried (flat instance); ⚠ weakened in the general theorem: only causality and closed `≤` |
| `Σ` Cauchy (`def:cauchy_surface`, DEC-14) | ✓ carried; acausality derived in the flat instance (`IsCauchySurface.isAcausal`) |
| limit curves (O'Neill, Hawking–Ellis) | not used: Zorn on time graphs (`CurvesExtend.lean`) |
| statement of `CBG.flat_isCompact_Jminus_inter_of_isCauchySurface` (`Flat/CBG.lean:463`) | ✓ identical hypotheses and conclusion (`flat_isCompact_Jminus_inter_cauchy`); past form likewise |

## SCOPE (disclosed)

* Nothing is left: the module is sorry-free. It does not import `Flat/CBG.lean` (which may import
  it) nor `Flat/Cla/Cover*`. Integration: the two bodies in `Flat/CBG.lean` become
  `flat_isCompact_Jminus_inter_cauchy hGH hS p` and `flat_isCompact_Jplus_inter_cauchy hGH hS p`.
* The general theorem asks `J⁻(W)` open for open `W` (causal openness, past half); the flat
  instance proves it from push-up and the chronal flow (`flat_isOpen_Jminus_of_isOpen`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

namespace Causality

section General

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

variable (C) in
/-- `x` is **past-noncompact** relative to `S`: for every neighbourhood `V` of `x`, `J⁻(V) ∩ S`
is contained in no compact set. -/
def PastNoncompactAt (S : Set M) (x : M) : Prop :=
  ∀ V ∈ 𝓝 x, ¬ ∃ K : Set M, IsCompact K ∧ C.Jminus ⊤ V ∩ S ⊆ K

/-- The past-noncompact points form a closed set. -/
theorem pastNoncompactAt_of_mem_closure {S : Set M} {x : M}
    (hx : x ∈ closure {y | C.PastNoncompactAt S y}) : C.PastNoncompactAt S x := by
  intro V hV hK
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff_nhds.1 hx _ (interior_mem_nhds.2 hV)
  exact hy V (mem_interior_iff_mem_nhds.1 hyV) hK

/-- The past-noncompact points form a future set, when `J⁻` of an open set is open. -/
theorem PastNoncompactAt.of_le (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W))
    {S : Set M} {x w : M} (hx : C.PastNoncompactAt S x) (hxw : C.le ⊤ x w) :
    C.PastNoncompactAt S w := by
  rintro V hV ⟨K, hK, hsub⟩
  refine hx (C.Jminus ⊤ (interior V))
    ((hJo _ isOpen_interior).mem_nhds ⟨w, mem_interior_iff_mem_nhds.2 hV, hxw⟩) ⟨K, hK, ?_⟩
  rintro y ⟨⟨v, ⟨w', hw', hvw'⟩, hyv⟩, hyS⟩
  exact hsub ⟨⟨w', interior_subset hw', C.le_trans hyv hvw'⟩, hyS⟩

/-- **Exit through the frontier**: if `x ≤ ℓ`, `x ∉ N`, `ℓ ∈ int N`, then some frontier point
`z` of `N` satisfies `x ≤ z ≤ ℓ` (a causal curve from `x` to `ℓ`, connectedness of its image). -/
theorem exists_frontier_of_le (hC : C.CausallyArcConnected) {N : Set M} {x ℓ : M} (hx : x ∉ N) (hℓ : ℓ ∈ interior N) (hxℓ : C.le ⊤ x ℓ) :
    ∃ z ∈ frontier N, C.le ⊤ x z ∧ C.le ⊤ z ℓ := by
  obtain ⟨γ, hγ, h0, h1⟩ := ((hC ⊤ le_rfl x ℓ).1).1 hxℓ
  have hcont : ContinuousOn γ (Icc 0 1) := CurveOn.continuousOn C.isRelFamily_le hγ
  have hpc : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hcont
  by_contra hne
  have hsub : γ '' Icc 0 1 ⊆ interior N ∪ (closure N)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hi : γ t ∈ interior N
    · exact Or.inl hi
    · refine Or.inr fun hcl => hne ⟨γ t, ⟨hcl, hi⟩, ?_, ?_⟩
      · rw [← h0]; exact hγ.le_of_le le_rfl ht.1 ht.2
      · rw [← h1]; exact hγ.le_of_le ht.1 ht.2 le_rfl
  have hdisj : Disjoint (interior N) (closure N)ᶜ :=
    disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  have hin := hpc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj
    hsub ⟨ℓ, ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩, hℓ⟩
  exact hx (interior_subset (hin ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩))

/-- `J⁻(y)` is closed when the causal relation is closed. -/
theorem isClosed_Jminus_singleton_of_isClosed_le (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    (y : M) : IsClosed (C.Jminus ⊤ {y}) := by
  have : C.Jminus ⊤ {y} = (fun x => (x, y)) ⁻¹' {z : M × M | C.le ⊤ z.1 z.2} := by
    ext x; simp [Precausality.mem_Jminus_singleton]
  rw [this]
  exact hle.preimage (continuous_id.prodMk continuous_const)

/-- **The step**: a past-noncompact `y` has a past-noncompact `z ≤ y` on the frontier of any
compact `N` with `y ∈ int N`, and `z ∈ J⁺(S)`. -/
theorem exists_pastNoncompactAt_frontier [T2Space M] (hC : C.CausallyArcConnected)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {S : Set M} (hSc : IsClosed S)
    (hSp : IsClosed (C.Jplus ⊤ S)) {y : M} (hy : C.PastNoncompactAt S y) {N : Set M}
    (hN : IsCompact N) (hyN : y ∈ interior N) :
    ∃ z ∈ frontier N, C.le ⊤ z y ∧ z ∈ C.Jplus ⊤ S ∧ C.PastNoncompactAt S z := by
  by_contra hcon
  push Not at hcon
  have hNc : IsClosed N := hN.isClosed
  have hfrN : frontier N ⊆ N := frontier_subset_closure.trans hNc.closure_eq.subset
  set Z := frontier N ∩ (C.Jminus ⊤ {y} ∩ C.Jplus ⊤ S) with hZdef
  have hZ : IsCompact Z := hN.of_isClosed_subset
    (isClosed_frontier.inter ((isClosed_Jminus_singleton_of_isClosed_le hle y).inter hSp))
    (inter_subset_left.trans hfrN)
  have hgood : ∀ z ∈ Z, ∃ V ∈ 𝓝 z, ∃ K : Set M, IsCompact K ∧ C.Jminus ⊤ V ∩ S ⊆ K := by
    rintro z ⟨hzfr, hzy, hzS⟩
    have := hcon z hzfr (Precausality.mem_Jminus_singleton.1 hzy) hzS
    unfold PastNoncompactAt at this
    push Not at this
    exact this
  choose! V hV K hK hVK using hgood
  obtain ⟨t, htZ, hcov⟩ := hZ.elim_nhds_subcover (fun z => interior (V z))
    (fun z hz => interior_mem_nhds.2 (hV z hz))
  set W := ⋃ z ∈ t, interior (V z) with hWdef
  have hWo : IsOpen W := isOpen_biUnion fun _ _ => isOpen_interior
  set Kc := ⋃ z ∈ t, K z with hKcdef
  have hKc : IsCompact Kc := t.isCompact_biUnion fun z hz => hK z (htZ z hz)
  have hW : C.Jminus ⊤ W ∩ S ⊆ Kc := by
    rintro x ⟨⟨w, hw, hxw⟩, hxS⟩
    obtain ⟨z, hzt, hwz⟩ := mem_iUnion₂.1 hw
    exact mem_iUnion₂.2 ⟨z, hzt, hVK z (htZ z hzt) ⟨⟨w, interior_subset hwz, hxw⟩, hxS⟩⟩
  set F := frontier N ∩ C.Jplus ⊤ S ∩ Wᶜ with hFdef
  have hF : IsCompact F := hN.of_isClosed_subset
    ((isClosed_frontier.inter hSp).inter hWo.isClosed_compl)
    (inter_subset_left.trans (inter_subset_left.trans hfrN))
  set Q := (F ×ˢ N) ∩ {z : M × M | C.le ⊤ z.1 z.2} with hQdef
  have hQ : IsCompact Q := (hF.prod hN).inter_right hle
  set P := Prod.snd '' Q with hPdef
  have hP : IsClosed P := (hQ.image continuous_snd).isClosed
  have hyP : y ∉ P := by
    rintro ⟨⟨z, ℓ⟩, ⟨⟨hzF, -⟩, hzℓ⟩, rfl⟩
    have hzZ : z ∈ Z := ⟨hzF.1.1, Precausality.mem_Jminus_singleton.2 hzℓ, hzF.1.2⟩
    exact hzF.2 (hcov hzZ)
  set L := interior N ∩ Pᶜ with hLdef
  have hL : L ∈ 𝓝 y := (isOpen_interior.inter hP.isOpen_compl).mem_nhds ⟨hyN, hyP⟩
  refine hy L hL ⟨(N ∩ S) ∪ Kc, (hN.inter_right hSc).union hKc, ?_⟩
  rintro x ⟨⟨ℓ, hℓL, hxℓ⟩, hxS⟩
  by_cases hxN : x ∈ N
  · exact Or.inl ⟨hxN, hxS⟩
  right
  obtain ⟨z, hzfr, hxz, hzℓ⟩ := exists_frontier_of_le hC hxN hℓL.1 hxℓ
  have hzS : z ∈ C.Jplus ⊤ S := ⟨x, hxS, hxz⟩
  by_cases hzW : z ∈ W
  · exact hW ⟨⟨z, hzW, hxz⟩, hxS⟩
  · exact absurd ⟨(z, ℓ), ⟨⟨⟨⟨hzfr, hzS⟩, hzW⟩, interior_subset hℓL.1⟩, hzℓ⟩, rfl⟩ hℓL.2

/-- A past-noncompact point is not on an acausal `S` (the step, at a point of `S`). -/
theorem not_pastNoncompactAt_of_mem [T2Space M] [LocallyCompactSpace M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {S : Set M} (hSc : IsClosed S)
    (hSp : IsClosed (C.Jplus ⊤ S)) (hac : C.IsAcausal S) {x : M} (hxS : x ∈ S) :
    ¬ C.PastNoncompactAt S x := by
  intro hx
  obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds x
  obtain ⟨z, hzfr, hzx, ⟨σ, hσS, hσz⟩, -⟩ := exists_pastNoncompactAt_frontier hC hle hSc hSp hx
    hNc (mem_interior_iff_mem_nhds.2 hNn)
  have hσx : σ = x := hac σ hσS x hxS (C.le_trans hσz hzx)
  subst hσx
  have hzx' : z = σ := hcaus hzx hσz
  subst hzx'
  exact hzfr.2 (mem_interior_iff_mem_nhds.2 hNn)

/-- **`J⁻(p) ∩ Σ` is compact** for an acausal Cauchy surface `Σ` with `J^±(Σ)` closed, in a causal,
causally arc-connected, T2, locally compact spacetime with closed causal relation, a continuous
function `τ` strictly increasing along `≤`, and `J⁻` of open sets open. No limit curve: Zorn on
time graphs inside the past-noncompact set (see the module docstring). -/
theorem isCompact_Jminus_inter_of_isCauchySurface [T2Space M] [LocallyCompactSpace M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y)
    (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) (hSp : IsClosed (C.Jplus ⊤ S))
    (hSm : IsClosed (C.Jminus ⊤ S)) (p : M) : IsCompact (C.Jminus ⊤ {p} ∩ S) := by
  -- `S` is closed: `S = J⁺(S) ∩ J⁻(S)`
  have hSc : IsClosed S := by
    have : S = C.Jplus ⊤ S ∩ C.Jminus ⊤ S := by
      refine Subset.antisymm (fun x hx => ⟨⟨x, hx, C.le_refl trivial⟩, ⟨x, hx, C.le_refl trivial⟩⟩) ?_
      rintro x ⟨⟨σ, hσ, hσx⟩, ⟨σ', hσ', hxσ'⟩⟩
      have h := hac σ hσ σ' hσ' (C.le_trans hσx hxσ')
      subst h
      exact hcaus hσx hxσ' ▸ hσ
    rw [this]; exact hSp.inter hSm
  have hclosed : IsClosed (C.Jminus ⊤ {p} ∩ S) :=
    (isClosed_Jminus_singleton_of_isClosed_le hle p).inter hSc
  by_contra hp
  have hB : C.PastNoncompactAt S p := by
    rintro V hV ⟨K, hK, hsub⟩
    refine hp (hK.of_isClosed_subset hclosed fun x hx => hsub ⟨?_, hx.2⟩)
    exact ⟨p, mem_of_mem_nhds hV, Precausality.mem_Jminus_singleton.1 hx.1⟩
  haveI : Nonempty M := ⟨p⟩
  set B : Set M := {x | C.PastNoncompactAt S x} with hBdef
  have hBcl : closure B ⊆ B := fun x hx => pastNoncompactAt_of_mem_closure hx
  have hBle : ∀ {x w : M}, x ∈ B → C.le ⊤ x w → w ∈ B := fun hx hxw =>
    PastNoncompactAt.of_le hJo hx hxw
  let 𝒮 : Set (Set M) := {K | C.IsTimeGraph ⊤ τ K ∧ K ⊆ B}
  have h0 : ((fun _ : ℝ => p) '' Icc (0 : ℝ) 0) ∈ 𝒮 := by
    refine ⟨CausalCurveIn.isTimeGraph_image hτc hτ
      ((causalCurveOn_const (C := C) (a := 0) (b := 0) (show p ∈ (⊤ : Opens M) from trivial)).causalCurveIn_Icc
        le_rfl), ?_⟩
    rintro _ ⟨_, _, rfl⟩
    exact hB
  obtain ⟨K, -, hK⟩ := zorn_subset_nonempty 𝒮
    (fun ch hch hchain hne => ⟨⋃₀ ch, ⟨isTimeGraph_sUnion hchain hne fun K hK => (hch hK).1,
      sUnion_subset fun K hK => (hch hK).2⟩, fun _ hs => subset_sUnion_of_mem hs⟩) _ h0
  have hKtg : C.IsTimeGraph ⊤ τ K := hK.1.1
  have hKB : K ⊆ B := hK.1.2
  have hmax : ∀ K' : Set M, C.IsTimeGraph ⊤ τ K' → K' ⊆ B → K ⊆ K' → K' ⊆ K :=
    fun K' h1 h2 h3 => hK.2 ⟨h1, h2⟩ h3
  -- no least point
  have hnoleast : ∀ a, ¬ IsLeast (τ '' K) a := by
    intro a ha
    have hc₀a := IsTimeGraph.time_invFunOn (T := τ) ha.1
    obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds (invFunOn τ K a)
    obtain ⟨z, hzfr, hzy, -, hzB⟩ := exists_pastNoncompactAt_frontier hC hle hSc hSp
      (hKB hc₀a.1) hNc (mem_interior_iff_mem_nhds.2 hNn)
    have hzne : z ≠ invFunOn τ K a := by
      rintro rfl; exact hzfr.2 (mem_interior_iff_mem_nhds.2 hNn)
    obtain ⟨c', hc', hc'eq, hc'a⟩ := exists_prepend hC hKtg.2 ha hzy
    have hK'B : c' '' (Icc (a - 1) a ∪ τ '' K) ⊆ B := by
      rintro _ ⟨s, hs, rfl⟩
      have hs1 : a - 1 ≤ s := by
        rcases hs with hs | hs
        · exact hs.1
        · linarith [ha.2 hs]
      have hle' := hc'.le_of_le (Or.inl ⟨le_rfl, by linarith⟩) hs hs1
      rw [hc'a] at hle'
      exact hBle hzB hle'
    have hsub : K ⊆ c' '' (Icc (a - 1) a ∪ τ '' K) := fun x hx =>
      ⟨τ x, Or.inr (mem_image_of_mem τ hx), by
        rw [hc'eq _ (mem_image_of_mem τ hx)]; exact hKtg.invFunOn_time hx⟩
    have hzK : z ∈ K := hmax _ (hc'.isTimeGraph_image hτc hτ) hK'B hsub
      ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, hc'a⟩
    have h1 := ha.2 (mem_image_of_mem τ hzK)
    have h2 := hτ z _ hzy hzne
    rw [hc₀a.2] at h2
    linarith
  -- inextensible
  have hinext : C.Inextensible ⊤ (τ '' K) (invFunOn τ K) := by
    refine ⟨hKtg.2, ?_⟩
    rintro ⟨I', c', hcurve, ⟨φ, -, hφmaps, -, hφeq⟩, ⟨t', ht', hgrow⟩⟩
    set A := φ '' (τ '' K) with hAdef
    have hAI : A ⊆ I' := by rintro _ ⟨u, hu, rfl⟩; exact hφmaps hu
    have hAK : ∀ u ∈ τ '' K, c' (φ u) ∈ K := fun u hu => by
      rw [hφeq u hu]; exact (IsTimeGraph.time_invFunOn hu).1
    have hKsub : ∀ L ⊆ I', L.OrdConnected → A ⊆ L → (∀ s ∈ L, c' s ∈ B) →
        ∀ s ∈ L, c' s ∈ K := by
      intro L hLI hLoc hAL hLB s hs
      have hL : C.CausalCurveIn ⊤ L c' :=
        ⟨⟨s, hs⟩, hLoc, fun a ha b hb => hcurve.curve a (hLI ha) b (hLI hb)⟩
      refine hmax _ (hL.isTimeGraph_image hτc hτ) (by rintro _ ⟨s, hs, rfl⟩; exact hLB s hs) ?_
        ⟨s, hs, rfl⟩
      intro x hx
      refine ⟨φ (τ x), hAL ⟨τ x, mem_image_of_mem τ hx, rfl⟩, ?_⟩
      rw [hφeq _ (mem_image_of_mem τ hx)]
      exact hKtg.invFunOn_time hx
    -- the new point is below every point of `A`
    have ht'A : ∀ a ∈ A, t' < a := by
      rintro _ ⟨u, hu, rfl⟩
      by_contra hle'
      push Not at hle'
      set L := {s ∈ I' | ∃ a ∈ A, a ≤ s} with hLdef
      have hLoc : L.OrdConnected := ⟨fun x hx y hy z hz =>
        ⟨hcurve.ordConnected.out hx.1 hy.1 hz,
          let ⟨a, ha, hax⟩ := hx.2; ⟨a, ha, hax.trans hz.1⟩⟩⟩
      have hLB : ∀ s ∈ L, c' s ∈ B := by
        rintro s ⟨hs, _, ⟨v, hv, rfl⟩, hvs⟩
        exact hBle (hKB (hAK v hv)) (hcurve.le_of_le (hφmaps hv) hs hvs)
      have hmem := hKsub L (fun s hs => hs.1) hLoc (fun a ha => ⟨hAI ha, a, ha, le_rfl⟩) hLB t'
        ⟨ht', φ u, ⟨u, hu, rfl⟩, hle'⟩
      rw [← hKtg.image_invFunOn] at hmem
      obtain ⟨t, ht, e⟩ := hmem
      exact hgrow t ht e.symm
    obtain ⟨u₁, hu₁⟩ := hKtg.2.nonempty
    have ha₁ : φ u₁ ∈ A := ⟨u₁, hu₁, rfl⟩
    have hAne : A.Nonempty := ⟨_, ha₁⟩
    have hAbdd : BddBelow A := ⟨t', fun a ha => (ht'A a ha).le⟩
    set s₀ := sInf A with hs₀def
    have hs₀a : ∀ a ∈ A, s₀ ≤ a := fun a ha => csInf_le hAbdd ha
    have ht's₀ : t' ≤ s₀ := le_csInf hAne fun a ha => (ht'A a ha).le
    have hs₀I : s₀ ∈ I' := hcurve.ordConnected.out ht' (hφmaps hu₁) ⟨ht's₀, hs₀a _ ha₁⟩
    -- `c' s₀` is in the closure of `K`
    have hcl : c' s₀ ∈ closure K := by
      have hcont : ContinuousOn c' (Icc s₀ (φ u₁)) :=
        CurveOn.continuousOn C.isRelFamily_le (hcurve.curve s₀ hs₀I _ (hφmaps hu₁))
      have hglb : IsGLB (A ∩ Icc s₀ (φ u₁)) s₀ := by
        refine ⟨fun a ha => ha.2.1, fun b hb => le_csInf hAne fun a ha => ?_⟩
        by_cases h : a ≤ φ u₁
        · exact hb ⟨ha, hs₀a a ha, h⟩
        · exact (hb ⟨ha₁, hs₀a _ ha₁, le_rfl⟩).trans (not_le.1 h).le
      have hmem : s₀ ∈ closure (A ∩ Icc s₀ (φ u₁)) :=
        hglb.mem_closure ⟨_, ha₁, hs₀a _ ha₁, le_rfl⟩
      have := ((hcont s₀ ⟨le_rfl, hs₀a _ ha₁⟩).mono inter_subset_right).mem_closure_image hmem
      refine closure_mono ?_ this
      rintro _ ⟨a, ⟨⟨u, hu, rfl⟩, -⟩, rfl⟩
      exact hAK u hu
    have hs₀B : c' s₀ ∈ B := hBcl (closure_mono hKB hcl)
    set L := {s ∈ I' | s₀ ≤ s} with hLdef
    have hLoc : L.OrdConnected := ⟨fun x hx y hy z hz =>
      ⟨hcurve.ordConnected.out hx.1 hy.1 hz, hx.2.trans hz.1⟩⟩
    have hy : c' s₀ ∈ K := hKsub L (fun s hs => hs.1) hLoc (fun a ha => ⟨hAI ha, hs₀a a ha⟩)
      (fun s hs => hBle hs₀B (hcurve.le_of_le hs₀I hs.1 hs.2)) s₀ ⟨hs₀I, le_rfl⟩
    refine hnoleast (τ (c' s₀)) ⟨mem_image_of_mem τ hy, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxe : c' (φ (τ x)) = x := by
      rw [hφeq _ (mem_image_of_mem τ hx)]; exact hKtg.invFunOn_time hx
    have hle' := hcurve.le_of_le hs₀I (hφmaps (mem_image_of_mem τ hx))
      (hs₀a _ ⟨τ x, mem_image_of_mem τ hx, rfl⟩)
    rw [hxe] at hle'
    rcases eq_or_ne (c' s₀) x with e | e
    · rw [e]
    · exact (hτ _ _ hle' e).le
  -- the Cauchy surface meets `K ⊆ B`
  obtain ⟨x, ⟨hxK, hxS⟩, -⟩ := hS (τ '' K) (invFunOn τ K) hinext
  rw [hKtg.image_invFunOn] at hxK
  exact not_pastNoncompactAt_of_mem hcaus hC hle hSc hSp hac hxS (hKB hxK)

/-- **Past form**: `J⁺(p) ∩ Σ` is compact (`C.dual`, kb/0002). -/
theorem isCompact_Jplus_inter_of_isCauchySurface [T2Space M] [LocallyCompactSpace M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y)
    (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jplus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) (hSp : IsClosed (C.Jplus ⊤ S))
    (hSm : IsClosed (C.Jminus ⊤ S)) (p : M) : IsCompact (C.Jplus ⊤ {p} ∩ S) := by
  have hle' : IsClosed {z : M × M | C.dual.le ⊤ z.1 z.2} :=
    hle.preimage (continuous_snd.prodMk continuous_fst)
  exact isCompact_Jminus_inter_of_isCauchySurface (C := C.dual)
    (fun x y h1 h2 => hcaus h2 h1) (dual_causallyArcConnectedOn.2 hC) hle'
    (τ := fun x => -τ x) hτc.neg
    (fun x y h hne => neg_lt_neg (hτ y x h (Ne.symm hne))) hJo
    (dual_isCauchySurfaceOn.2 hS) (fun x hx y hy h => (hac y hy x hx h).symm) hSm hSp p

/-- **GH form**: in a tarentin GH Hausdorff locally compact spacetime. -/
theorem GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface [T2Space M]
    [LocallyCompactSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y)
    (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) (hSp : IsClosed (C.Jplus ⊤ S))
    (hSm : IsClosed (C.Jminus ⊤ S)) (p : M) : IsCompact (C.Jminus ⊤ {p} ∩ S) :=
  Causality.isCompact_Jminus_inter_of_isCauchySurface hG.1 hC (hG.isClosed_le hT) hτc hτ hJo hS
    hac hSp hSm p

/-- **GH form, past**. -/
theorem GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface [T2Space M]
    [LocallyCompactSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y)
    (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jplus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) (hSp : IsClosed (C.Jplus ⊤ S))
    (hSm : IsClosed (C.Jminus ⊤ S)) (p : M) : IsCompact (C.Jplus ⊤ {p} ∩ S) :=
  Causality.isCompact_Jplus_inter_of_isCauchySurface hG.1 hC (hG.isClosed_le hT) hτc hτ hJo hS
    hac hSp hSm p

end General

end Causality

/-! ### The flat instance -/

section Flat

open Flat

variable {d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [SecondCountableTopology M] [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- In a flat spacetime, `J⁻(W)` is open for every open `W`: push the point of `W` up along the
chronal causal flow, then push-up. -/
theorem flat_isOpen_Jminus_of_isOpen {W : Set M} (hW : IsOpen W) :
    IsOpen ((flatCausality d M).Jminus ⊤ W) := by
  obtain ⟨φ, -, hch⟩ := (flat_hasChronalCausalFlow : (flatCausality d M).HasChronalCausalFlow)
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hw, hxw⟩
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), φ t w ∈ W := by
    have hc : Continuous fun t : ℝ => φ t w := φ.continuous continuous_id continuous_const
    have := hc.tendsto 0
    rw [φ.map_zero_apply] at this
    exact this (hW.mem_nhds hw)
  obtain ⟨t, htW, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hlt : (flatCausality d M).lt ⊤ w (φ t w) := by
    have := hch.lt w (s := 0) (t := t) ht
    rwa [φ.map_zero_apply] at this
  have hpush := ((flatCausality_pushUp (N := FlatSpacetime.of (d := d) M)) ⊤ (φ t w)).1.2
  have hx : x ∈ (flatCausality d M).Iminus ⊤ {φ t w} :=
    hpush ⟨w, Precausality.mem_Iminus_singleton.2 hlt, hxw⟩
  refine mem_of_superset (Causality.isOpen_Iminus.mem_nhds hx) ?_
  intro y hy
  exact ⟨φ t w, htW, (flatCausality d M).le_of_lt (Precausality.mem_Iminus_singleton.1 hy)⟩

/-- In a flat spacetime, `J⁺(W)` is open for every open `W` (the flow run backwards). -/
theorem flat_isOpen_Jplus_of_isOpen {W : Set M} (hW : IsOpen W) :
    IsOpen ((flatCausality d M).Jplus ⊤ W) := by
  obtain ⟨φ, -, hch⟩ := (flat_hasChronalCausalFlow : (flatCausality d M).HasChronalCausalFlow)
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hw, hwx⟩
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), φ t w ∈ W := by
    have hc : Continuous fun t : ℝ => φ t w := φ.continuous continuous_id continuous_const
    have := hc.tendsto 0
    rw [φ.map_zero_apply] at this
    exact this (hW.mem_nhds hw)
  obtain ⟨t, htW, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Iio (0 : ℝ) ∈ 𝓝[<] 0)).exists
  have hlt : (flatCausality d M).lt ⊤ (φ t w) w := by
    have := hch.lt w (s := t) (t := 0) ht
    rwa [φ.map_zero_apply] at this
  have hpush := ((flatCausality_pushUp (N := FlatSpacetime.of (d := d) M)) ⊤ (φ t w)).1.1
  have hx : x ∈ (flatCausality d M).Iplus ⊤ {φ t w} :=
    hpush ⟨w, Precausality.mem_Iplus_singleton.2 hlt, hwx⟩
  refine mem_of_superset (Causality.isOpen_Iplus.mem_nhds hx) ?_
  intro y hy
  exact ⟨φ t w, htW, (flatCausality d M).le_of_lt (Precausality.mem_Iplus_singleton.1 hy)⟩

/-- The flat inputs of the general theorem: local compactness, acausality of `Σ`, closedness of
`J^±(Σ)` (Cauchy splitting), and a continuous time function (Geroch time). -/
theorem flat_cbgCompact_inputs (hGH : (flatCausality d M).GloballyHyperbolic) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    (flatCausality d M).IsAcausal S ∧ IsClosed ((flatCausality d M).Jplus ⊤ S) ∧
      IsClosed ((flatCausality d M).Jminus ⊤ S) ∧
      ∃ τ : M → ℝ, Continuous τ ∧ ∀ x y, (flatCausality d M).le ⊤ x y → x ≠ y → τ x < τ y := by
  obtain ⟨φ, hφ, hch⟩ := (flat_hasChronalCausalFlow : (flatCausality d M).HasChronalCausalFlow)
  have hac : (flatCausality d M).IsAcausal S :=
    hS.isAcausal (flatCausality_causallyArcConnected d M) (curvesExtend_of_isCausalFlow hφ)
  obtain ⟨ψ, hψ⟩ := (flat_hasChronalCausalFlow : (flatCausality d M).HasChronalCausalFlow)
    |>.nonempty_isCauchySplitting hGH.1 hS hac
  refine ⟨hac, ?_, ?_, ?_⟩
  · rw [hψ.Jplus_eq hGH.1 hac]
    exact ψ.isClosedMap _ (isClosed_univ.prod isClosed_Ici)
  · rw [hψ.Jminus_eq hGH.1 hac]
    exact ψ.isClosedMap _ (isClosed_univ.prod isClosed_Iic)
  · let N : FlatSpacetime.{0} d := FlatSpacetime.of M
    letI : MeasurableSpace N := borel N
    haveI : BorelSpace N := ⟨rfl⟩
    have hGH' : (flatCausality d N).GloballyHyperbolic := hGH
    obtain ⟨μ, hp, hm⟩ := exists_admissible_measure N hGH'
    obtain ⟨T, hT, hTs⟩ := Causality.geroch_i_imp_ii hp hm flatCausality_tarentin
      (flatCausality_causallyArcConnected d N) (jminus_ne_singleton_of_isCausalFlow hφ)
      (jplus_ne_singleton_of_isCausalFlow hφ) hGH'
    exact ⟨T, hT.1.continuous, hTs⟩

/-- **`J⁻(p) ∩ Σ` is compact in a GH flat spacetime with Cauchy surface `Σ`** — the statement of
`CBG.flat_isCompact_Jminus_inter_of_isCauchySurface` (`Flat/CBG.lean`), proved. -/
theorem flat_isCompact_Jminus_inter_cauchy
    (hGH : (flatCausality d M).GloballyHyperbolic) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (p : M) :
    IsCompact ((flatCausality d M).Jminus ⊤ {p} ∩ S) := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Minkowski d) M
  obtain ⟨hac, hSp, hSm, τ, hτc, hτ⟩ := flat_cbgCompact_inputs hGH hS
  exact Causality.GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface
    flatCausality_tarentin hGH (flatCausality_causallyArcConnected d M) hτc hτ
    (fun _ hW => flat_isOpen_Jminus_of_isOpen (d := d) hW) hS hac hSp hSm p

/-- **`J⁺(p) ∩ Σ` is compact in a GH flat spacetime with Cauchy surface `Σ`** — the statement of
`CBG.flat_isCompact_Jplus_inter_of_isCauchySurface` (`Flat/CBG.lean`), proved. -/
theorem flat_isCompact_Jplus_inter_cauchy
    (hGH : (flatCausality d M).GloballyHyperbolic) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (p : M) :
    IsCompact ((flatCausality d M).Jplus ⊤ {p} ∩ S) := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Minkowski d) M
  obtain ⟨hac, hSp, hSm, τ, hτc, hτ⟩ := flat_cbgCompact_inputs hGH hS
  exact Causality.GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface
    flatCausality_tarentin hGH (flatCausality_causallyArcConnected d M) hτc hτ
    (fun _ hW => flat_isOpen_Jplus_of_isOpen (d := d) hW) hS hac hSp hSm p

end Flat

end Causal
