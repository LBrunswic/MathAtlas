import GX.BTZ.Surgery
import GX.BTZ.GluingTransitions
import Causal.LemmaKLocal

/-!
# `GX.BTZ.AbsMax` — absolute maximality of `Reg M` (B21 Lemmas 2.12–2.15, Props 2.16–2.17, Cor 2.18)

Packages WP-41k, WP-43c, WP-44f, WP-46f, WP-47f (and its fixer round 1). `brunswic2021cauchy` (**B21**,
`papers/gx/sources/2108.12631/src/BTZ_1.tex`), §2.3–2.4 (l.936–1117), the input of DEC-28's
headline. No gx ledger label; these are cited results built here (DEC-23). Rows (B21 labels):

* **`brunswic2021cauchy:Remark 1`** — `BTZ_1.tex:994–996` (closed, DEC-125 (f)):
  `GX.E0AbsMax.globallyHyperbolicOn_of_causallyConvexIn` (open-set form, any causally
  arc-connected causality); literal embedding form for `𝔼₀`-manifolds
  `GX.E0AbsMax.globallyHyperbolic_of_isE0Mor_of_causallyConvexIn`.
* **`brunswic2021cauchy:lem:BTZext_caus_conv`** (Lemma 2.13) — `BTZ_1.tex:999–1023` (closed,
  DEC-125 (f)): (a) `GX.E0AbsMax.btzExt_causallyConvexIn_iff`, (b) `…_of_globallyHyperbolicOn`
  (`SingularFlatAxioms`); `𝔼₀` forms `btzExt_causallyConvexIn_iff_e0`, `…_of_globallyHyperbolicOn_e0`.
* **`brunswic2021cauchy:Lemma 2.14`** — `BTZ_1.tex:1026–1037` (closed, DEC-116 (e), DEC-126): the
  abstract `GX.E0AbsMax.btzExt_isCausal_of_stronglyCausalOn` with `NoCausalLoopIn`; and, **proved
  (DEC-126)**, the `𝔼₀` form with no extra hypothesis `btzExt_isCausal_of_stronglyCausalOn_e0`,
  its closed-BTZ-loop case `sing_eq_of_le_of_le_of_stronglyCausalOn_e0` (§2b, the paper's tube).
* **`brunswic2021cauchy:cor:GH_causal`** (Cor 2.15) — `BTZ_1.tex:1038–1039` (closed, DEC-116 (e)):
  `GX.E0AbsMax.cor_GH_causal`; the instance Prop 2.17 uses, `isCausal_of_twoOpens`, has no extra
  hypothesis; the `𝔼₀` form with no extra hypothesis `cor_GH_causal_e0`.
* `brunswic2021cauchy:lem:extension_hausdorff` (Lemma 2.12) — `BTZ_1.tex:941–991` (partial: only
  the case Prop 2.17 uses, `M₀ = Reg M`, `M₂` flat GH): `GX.E0AbsMax.lem_extension_hausdorff`.
* **`brunswic2021cauchy:prop:cauchy_abs_max`** (Prop 2.16) — `BTZ_1.tex:1048–1075` (closed,
  DEC-125 (e): `A = {0}`, targets connected; DEC-107): `GX.E0AbsMax.prop_cauchy_abs_max_C1`,
  `prop_cauchy_abs_max_e0`; small local Cauchy charts `exists_small_cauchyChart` (§1b).
* **`brunswic2021cauchy:prop:abs_max`** (Prop 2.17, `A = {0}`) — `BTZ_1.tex:1078–1082`, proof
  l.1088–1119 (closed, DEC-125 (e), DEC-107/117): `GX.E0AbsMax.prop_abs_max_C1`; its leaf, the
  mixed diamonds `E0Pushout.isCompact_diamond_mixed`, is proved (§4c, WP-47d's proof).
* **`brunswic2021cauchy:cor:abs_max`** (Cor 2.18) — `BTZ_1.tex:1083–1086` (closed, DEC-117):
  `GX.E0AbsMax.cor_abs_max_C1`.

DEC-117: the topological route (`prop_abs_max`, `cor_abs_max`, `prop_abs_max_e0`, `cor_abs_max_e0`,
through the deleted `E0Surgery.regM_isCauchyComplete` and its (G0)) is **deleted**.

> Let $M_0\xrightarrow{\iota} M_1$ be a BTZ-extension of $\mass{\geq0}$-manifolds. (a) $\iota(M_0)$
> is causally convex in $M_1$ iff $\forall x\in \sing_0(M_0), \sing_0[J^+(\iota(x))] \subset
> \iota(M_0)$. (b) If $M_0$ is globally hyperbolic then $\iota(M_0)$ is causally convex. (l.999–1006)
>
> If $M_0$ is strongly causal then $M_1$ is causal. (l.1026–1027) Let $M$ be a globally hyperbolic
> Cauchy-compact $\mass{0}$-manifold. If $M$ is Cauchy-maximal then $\Reg(M)$ is globally
> hyperbolic Cauchy-complete and absolutely maximal in the sense of Barbot. (l.1084–1086)

## What is proved (0 `sorry`)

* §1 model-free: Remark 1; diamonds inside an open set; transport of GH onto an image; a compact
  acausal Cauchy surface of a connected GH spacetime is connected (no splitting).
* §1b model-free (WP-46f): **small local Cauchy domains** `cauchyDomain C S U` — the points whose
  causal past and future down to the Cauchy surface `S` stay in the open `U`: open (R1, closedness
  of `≤`, tube lemma), causally convex, saturated, and `S ∩ W` Cauchy in them (Levin's
  time-parametrised extension, Spear's `extensible_of_timeGraph_future/past`).
* §2 under `SingularFlatAxioms`: Lemma 2.13 (a), (b); Reg causally convex; GH ⇒ strongly causal;
  the abstract Lemma 2.14 / Cor 2.15; the two-open causality and diamond lemmas of Prop 2.17;
  `exists_nhds_diff_sing_subset_Iplus`, `lt_reg_of_lt`, the loop's order content.
* §2b `𝔼₀`-manifolds (WP-47f fixer, DEC-126): `prop:isom` near the axis (`e0Loop_localForm`,
  with `λ = 1`), the shadow relation along BTZ causal curves (`shadowRel_of_curve`), and the
  closed BTZ loop excluded (`sing_eq_of_le_of_le_of_stronglyCausalOn_e0`, in §3).
* §3–§5 `𝔼₀`-manifolds: SFA unconditionally (`e0_sfa_of_globalBTZ`); Remark 1 (embedding form);
  Prop 2.16 through lemma K, now with no `sorry`; `Reg M` GH; Lemma 2.12 (§4a); the push-out atlas
  (§4b); the mixed diamonds (§4c, WP-47d's proof) and `E0Pushout.globallyHyperbolic`.
* §7–§8 the unconditional (`hLine`-free) forms and the DEC-107 forms of record.

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifolds (Remark 1, Lemmas 2.13–2.15) | ✓ read (DEC-116 (e) for 2.14/2.15, DEC-125 (f) for Remark 1 / 2.13): abstract forms over any causality with `SingularFlatAxioms` (resp. causal arc-connectedness), BTZ-extension in open-set form (kb/0001); Lemmas 2.14/2.15 with `NoCausalLoopIn` explicit. `𝔼₀` forms unconditional (2.13, Remark 1, and 2.14/2.15 `_e0`, DEC-126) |
| `𝔼_A`-manifolds (Props 2.16–2.17, Cor 2.18) | ✓ read (DEC-125 (e)) `A = {0}`: `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable (DEC-66) |
| Cauchy-compact / Cauchy-maximal | ✓ DEC-107/117: `E0Surgery.IsE0C1SpacelikeCauchy` (forms of record; acausality derived); `E0Spear.IsE0CauchyMaximal` (DEC-77(c)) |
| `𝔼_A`-maximal | ✓ read (DEC-125 (e)) `IsE0Maximal`, targets `N` **connected** (finding: unrestricted, no `M` is maximal) |
| absolutely maximal (Barbot) | ✓ `Causal.Flat.AbsMax (fun _ => True)` over `FlatSpacetime.{0} 2` |
| Prop 2.16: smooth splitting, O'Neill Lemma 45, intersection theory | ✓ replaced by lemma K and §1b's local Cauchy domains (no `sorry`) |
| Lemma 2.12: general `M₀ → M₁`, `M₂` | ⚠ the case Prop 2.17 uses: `M₀ = Reg M`, `M₂ = N` flat GH (sing₀ = ∅); proved |

## SCOPE (disclosed; no `sorry`)

**WP-47f.** The mixed diamonds are **closed**: WP-47d's proof (`GX.BTZ.MixedDiamond`
§0–§4) is placed in §4c above the leaf, in the namespace `GX.E0AbsMax.Mixed` (AbsMax cannot import
MixedDiamond, which imports it; the namespace keeps MixedDiamond's own copy `GX.E0MixedDiamond`
building), and `E0Pushout.isCompact_diamond_mixed` is `Mixed.isCompact_diamond_mixed`. Hence
Props 2.16, 2.17 and Cor 2.18 have no `sorry` beneath (standard axioms,
`campaign/WP-47f/axioms.out`). DEC-125 (e) closes Props 2.16/2.17 (`A = {0}`, connected
targets) and DEC-125 (f) closes Remark 1 and Lemma 2.13 (the abstract readings).

**WP-47f fixer round 1.** The `𝔼₀` closed-BTZ-loop form of Lemma 2.14 (DEC-126) is **proved**
(§2b): `sing_eq_of_le_of_le_of_stronglyCausalOn_e0`, hence `btzExt_isCausal_of_stronglyCausalOn_e0`
and `cor_GH_causal_e0` with no `sorry`. Two pieces of strict-library proofs are re-proved here
because they are not exported: Rigid's local core, as `e0Loop_core_of_region` (verbatim proof,
conclusion extended by the axis-preserving isometry it constructs), and the hypothesis reduction
of `e0_localUnique_core_of_region` (inside `e0Loop_localForm`). Lemma 2.12 stays partial (the
special case Prop 2.17 uses; question recorded).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`; imports strict `Causal.LemmaKLocal`, DEC-33).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0AbsMax

/-! ### §1 Model-free: causally convex open sets of a globally hyperbolic spacetime -/

section Abstract

variable {X : Type*} [TopologicalSpace X] {C : Causal.Causality X}

/-- A diamond of `X` contained in an open `N` is a diamond of `N`: causally related points of a
diamond `J(x, y) ⊆ N` are related in `N` (causal arc-connectedness, `le_of_causallyConvexIn`). -/
theorem le_of_diamond_subset (hC : C.CausallyArcConnected) {N : Opens X} {p q x y : X}
    (hN : C.diamond ⊤ p q ⊆ N) (hx : x ∈ C.diamond ⊤ p q) (hy : y ∈ C.diamond ⊤ p q)
    (hxy : C.le ⊤ x y) : C.le N x y :=
  Causal.Causality.le_of_causallyConvexIn hC Causal.Causality.causallyConvexIn_diamond hN hx hy hxy

/-- **A diamond of `X` inside an open `N` is the diamond of `N`.** -/
theorem diamond_eq_of_subset (hC : C.CausallyArcConnected) {N : Opens X} {p q : X}
    (hN : C.diamond ⊤ p q ⊆ N) : C.diamond N p q = C.diamond ⊤ p q := by
  ext z
  simp only [Causal.Causality.mem_diamond]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨C.le_mono le_top h1, C.le_mono le_top h2⟩
  · rintro ⟨h1, h2⟩
    have hz : z ∈ C.diamond ⊤ p q := Causal.Causality.mem_diamond.2 ⟨h1, h2⟩
    have hp : p ∈ C.diamond ⊤ p q :=
      Causal.Causality.mem_diamond.2 ⟨C.le_refl trivial, C.le_trans h1 h2⟩
    have hq : q ∈ C.diamond ⊤ p q :=
      Causal.Causality.mem_diamond.2 ⟨C.le_trans h1 h2, C.le_refl trivial⟩
    exact ⟨le_of_diamond_subset hC hN hp hz h1, le_of_diamond_subset hC hN hz hq h2⟩

/-- The diamond of an open `N` is empty unless both its tips lie in `N`. -/
theorem diamond_eq_empty_of_notMem {N : Opens X} {p q : X} (h : p ∉ N ∨ q ∉ N) :
    C.diamond N p q = ∅ := by
  ext z
  simp only [Causal.Causality.mem_diamond, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  rcases h with h | h
  · exact h (C.le_mem_left h1)
  · exact h (C.le_mem_right h2)

/-- **B21 Remark 1** (`BTZ_1.tex:994–996`, model-free, open-set form, kb/0001): an open subset
`A`, causally convex in a globally hyperbolic causally arc-connected spacetime, is globally
hyperbolic (`GloballyHyperbolicOn A`). -/
theorem globallyHyperbolicOn_of_causallyConvexIn (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {A : Opens X} (hA : C.CausallyConvexIn (A : Set X) ⊤) :
    C.GloballyHyperbolicOn A := by
  refine ⟨fun x y hxy hyx => hG.1 (C.le_mono le_top hxy) (C.le_mono le_top hyx), fun p q => ?_⟩
  by_cases hp : p ∈ A
  · by_cases hq : q ∈ A
    · have hsub : C.diamond ⊤ p q ⊆ A := hA.2 p hp q hq
      rw [diamond_eq_of_subset hC hsub]
      exact hG.2 p q
    · rw [diamond_eq_empty_of_notMem (Or.inr hq)]; exact isCompact_empty
  · rw [diamond_eq_empty_of_notMem (Or.inl hp)]; exact isCompact_empty

/-- **Global hyperbolicity transported onto an image** (model-free): if `φ : Z → X` is continuous,
`U = φ(Z)` open, and the relation of `U` between images is that of `Z`, a globally hyperbolic
`Z` makes `U` globally hyperbolic. -/
theorem globallyHyperbolicOn_of_le_iff {Z : Type*} [TopologicalSpace Z] {D : Causal.Causality Z}
    (hD : D.GloballyHyperbolic) {φ : Z → X} (hφ : Continuous φ)
    {U : Opens X} (hU : (U : Set X) = range φ)
    (hle : ∀ x y, C.le U (φ x) (φ y) ↔ D.le ⊤ x y) : C.GloballyHyperbolicOn U := by
  have hmem : ∀ {z}, z ∈ U → ∃ x, φ x = z := fun {z} hz => by
    rw [← SetLike.mem_coe, hU] at hz; exact hz
  refine ⟨fun a b hab hba => ?_, fun p q => ?_⟩
  · obtain ⟨x, rfl⟩ := hmem (C.le_mem_left hab)
    obtain ⟨y, rfl⟩ := hmem (C.le_mem_right hab)
    rw [hD.1 ((hle x y).1 hab) ((hle y x).1 hba)]
  · by_cases hp : p ∈ U
    · by_cases hq : q ∈ U
      · obtain ⟨x, rfl⟩ := hmem hp
        obtain ⟨y, rfl⟩ := hmem hq
        have : C.diamond U (φ x) (φ y) = φ '' D.diamond ⊤ x y := by
          ext z
          constructor
          · intro hz
            obtain ⟨w, rfl⟩ := hmem (C.le_mem_right (Causal.Causality.mem_diamond.1 hz).1)
            obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
            exact ⟨w, Causal.Causality.mem_diamond.2 ⟨(hle x w).1 h1, (hle w y).1 h2⟩, rfl⟩
          · rintro ⟨w, hw, rfl⟩
            obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
            exact Causal.Causality.mem_diamond.2 ⟨(hle x w).2 h1, (hle w y).2 h2⟩
        rw [this]
        exact (hD.2 x y).image hφ
      · rw [diamond_eq_empty_of_notMem (Or.inr hq)]; exact isCompact_empty
    · rw [diamond_eq_empty_of_notMem (Or.inl hp)]; exact isCompact_empty

/-- The core of `isConnected_of_isCauchySurface_abstract`: no point lies in the causal future of
two disjoint closed pieces `S₁`, `S₂` of a compact acausal Cauchy surface `S = S₁ ∪ S₂`. A
`≤`-minimal point `y₀` of the compact `J⁻(x) ∩ J⁺(S₁) ∩ J⁺(S₂)` is off `S` (acausality); a
neighbourhood of `y₀` lies in `J⁺(s)` for one `s ∈ S`
(`Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn`), and the curve from the
other piece to `y₀` enters it just before reaching `y₀`, against minimality. -/
theorem not_le_of_le_of_isCauchySurface [T2Space X] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S S₁ S₂ : Set X}
    (hS : C.IsCauchySurface S) (hSac : C.IsAcausal S) (hS₁ : IsCompact S₁) (hS₂ : IsCompact S₂)
    (hSS : S = S₁ ∪ S₂) (hdisj : Disjoint S₁ S₂) {x a b : X} (ha : a ∈ S₁) (hb : b ∈ S₂)
    (hax : C.le ⊤ a x) (hbx : C.le ⊤ b x) : False := by
  have hle := hG.isClosed_le hT
  have hSc : IsCompact S := hSS ▸ hS₁.union hS₂
  set K : Set X := C.Jminus ⊤ {x} ∩ C.Jplus ⊤ S₁ ∩ C.Jplus ⊤ S₂ with hKdef
  have hKcl : IsClosed K :=
    ((hG.isClosed_Jminus_singleton hT x).inter
      (Causal.Causality.isClosed_Jplus_of_isCompact hle hS₁)).inter
      (Causal.Causality.isClosed_Jplus_of_isCompact hle hS₂)
  -- `K` is compact: inside finitely many diamonds `J(pᵢ, x)`, tarentin at the points of `S₁`
  have hcov : ∀ σ : S₁, ∃ p : X, (σ : X) ∈ interior (C.Jplus ⊤ {p}) := fun σ => by
    obtain ⟨p, -, q, -, hσ⟩ := hT σ univ univ_mem
    refine ⟨p, interior_mono (fun z hz => ?_) hσ⟩
    exact Causal.Precausality.mem_Jplus_singleton.2 (Causal.Causality.mem_diamond.1 hz).1
  choose p hp using hcov
  obtain ⟨F, hF⟩ := hS₁.elim_finite_subcover (fun σ : S₁ => interior (C.Jplus ⊤ {p σ}))
    (fun _ => isOpen_interior) (fun σ hσ => mem_iUnion.2 ⟨⟨σ, hσ⟩, hp ⟨σ, hσ⟩⟩)
  have hKsub : K ⊆ ⋃ σ ∈ F, C.diamond ⊤ (p σ) x := by
    rintro z ⟨⟨hzx, σ', hσ', hσ'z⟩, -⟩
    obtain ⟨σ, hσF, hσ⟩ := mem_iUnion₂.1 (hF hσ')
    have h1 : C.le ⊤ (p σ) σ' :=
      Causal.Precausality.mem_Jplus_singleton.1 (interior_subset hσ)
    exact mem_iUnion₂.2 ⟨σ, hσF, Causal.Causality.mem_diamond.2
      ⟨C.le_trans h1 hσ'z, Causal.Precausality.mem_Jminus_singleton.1 hzx⟩⟩
  have hKc : IsCompact K :=
    (F.isCompact_biUnion fun σ _ => hG.2 (p σ) x).of_isClosed_subset hKcl hKsub
  have hxK : x ∈ K := ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_refl trivial),
    a, ha, hax⟩, b, hb, hbx⟩
  obtain ⟨y₀, hy₀K, hmin⟩ := Causal.Causality.exists_minimal_of_isCompact hG.1
    (fun z => hG.isClosed_Jminus_singleton hT z) hKc ⟨x, hxK⟩
  obtain ⟨⟨hy₀x, a', ha', ha'y⟩, b', hb', hb'y⟩ := hy₀K
  have hy₀x' : C.le ⊤ y₀ x := Causal.Precausality.mem_Jminus_singleton.1 hy₀x
  have hSa' : a' ∈ S := hSS ▸ Or.inl ha'
  have hSb' : b' ∈ S := hSS ▸ Or.inr hb'
  -- `y₀ ∉ S`
  have hy₀S : y₀ ∉ S := by
    intro hy
    have e1 := hSac a' hSa' y₀ hy ha'y
    have e2 := hSac b' hSb' y₀ hy hb'y
    exact Set.disjoint_left.1 hdisj ha' (e1.trans e2.symm ▸ hb')
  have hSU : C.IsCauchySurfaceOn ⊤ (S ∩ (⊤ : Opens X)) := by
    rw [Opens.coe_top, inter_univ]; exact hS
  obtain ⟨s, ⟨hsS, -⟩, N, hN, -, hNs⟩ :=
    Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn hT hG hC hext
      Causal.Causality.causallyConvexIn_top hSc.isClosed hSU ⟨hSa', trivial⟩ trivial hy₀S ha'y
  -- the curve from the other piece's point `e ≤ y₀` meets `N ∖ {y₀}` just before `y₀`
  have hclose : ∀ e, e ∈ S → C.le ⊤ e y₀ →
      ∃ z ∈ N, C.le ⊤ e z ∧ C.le ⊤ z y₀ ∧ z ≠ y₀ := by
    intro e heS hey
    obtain ⟨c, hc, hc0, hc1⟩ := (hC ⊤ le_rfl e y₀).1.1 hey
    have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
    set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ c t = y₀} with hTdef
    have h1T : (1 : ℝ) ∈ T := ⟨right_mem_Icc.2 zero_le_one, hc1⟩
    have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
    have hTcl : IsClosed T := by
      have : T = Icc 0 1 ∩ c ⁻¹' {y₀} := rfl
      rw [this]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hτ : sInf T ∈ T := hTcl.csInf_mem ⟨1, h1T⟩ hTbdd
    have hτ0 : 0 < sInf T := by
      rcases hτ.1.1.eq_or_lt with h | h
      · exfalso
        have : c 0 = y₀ := by rw [h]; exact hτ.2
        rw [hc0] at this
        exact hy₀S (this ▸ heS)
      · exact h
    -- points just before `sInf T`
    have hpre : c ⁻¹' N ∈ 𝓝[Icc 0 1] (sInf T) :=
      (hcont _ hτ.1).preimage_mem_nhdsWithin (by rw [hτ.2]; exact hN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set t := max (sInf T - ε / 2) (sInf T / 2) with htdef
    have ht0 : 0 ≤ t := le_max_of_le_right (by linarith)
    have htlt : t < sInf T := max_lt (by linarith) (by linarith)
    have ht1 : t ≤ 1 := htlt.le.trans hτ.1.2
    have htN : c t ∈ N := by
      refine hball ⟨?_, ht0, ht1⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (sInf T - ε / 2) (sInf T / 2)]
    refine ⟨c t, htN, ?_, ?_, ?_⟩
    · have := hc.le_of_le le_rfl ht0 ht1; rwa [hc0] at this
    · have := hc.le_of_le ht0 htlt.le hτ.1.2; rwa [hτ.2] at this
    · intro he
      exact absurd (csInf_le hTbdd ⟨⟨ht0, ht1⟩, he⟩) (not_le.2 htlt)
  have hsS' : s ∈ S₁ ∪ S₂ := hSS ▸ hsS
  rcases hsS' with hs1 | hs2
  · obtain ⟨z, hzN, hb'z, hzy, hne⟩ := hclose b' hSb' hb'y
    exact hne (hmin z ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_trans hzy hy₀x'),
      s, hs1, hNs z hzN⟩, b', hb', hb'z⟩ hzy)
  · obtain ⟨z, hzN, ha'z, hzy, hne⟩ := hclose a' hSa' ha'y
    exact hne (hmin z ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_trans hzy hy₀x'),
      a', ha', ha'z⟩, s, hs2, hNs z hzN⟩ hzy)

/-- **A compact acausal Cauchy surface of a connected globally hyperbolic spacetime is connected**
(model-free; tarentin, causally arc-connected, curves extending, Hausdorff). No splitting: the
closed sets `J^±(S₁)`, `J^±(S₂)` of a separation `S = S₁ ⊔ S₂` cover the connected space, a common
point is in the future (or past) of both pieces, and `not_le_of_le_of_isCauchySurface` refutes it.
-/
theorem isConnected_of_isCauchySurface_abstract [T2Space X] [ConnectedSpace X] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set X} (hS : C.IsCauchySurface S) (hSc : IsCompact S) (hSac : C.IsAcausal S) :
    IsConnected S := by
  have hle := hG.isClosed_le hT
  -- every point is causally related to a point of `S`
  have hrel : ∀ x : X, ∃ σ ∈ S, C.le ⊤ σ x ∨ C.le ⊤ x σ := by
    intro x
    obtain ⟨I, c, hc, hsub⟩ := hext _ 0 1 zero_le_one
      (Causal.Causality.causalCurveOn_const (p := x) (W := ⊤) trivial)
    obtain ⟨v, hv, hcv⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hcv' : c v = x := hcv
    obtain ⟨σ, ⟨⟨u, hu, rfl⟩, hσ⟩, -⟩ := hS I c hc
    refine ⟨c u, hσ, ?_⟩
    rcases le_total u v with h | h
    · exact Or.inl (hcv' ▸ hc.1.le_of_le hu hv h)
    · exact Or.inr (hcv' ▸ hc.1.le_of_le hv hu h)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨σ₀, hσ₀, -⟩ := hrel x₀
  refine ⟨⟨σ₀, hσ₀⟩, ?_⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hSt hne hne'
  by_contra hempty
  have hdisj : Disjoint (S ∩ t) (S ∩ t') := Set.disjoint_left.2 fun z h1 h2 =>
    hempty ⟨z, h1.1, h1.2, h2.2⟩
  have hS₁ : IsCompact (S ∩ t) := hSc.inter_right ht
  have hS₂ : IsCompact (S ∩ t') := hSc.inter_right ht'
  have hSS : S = S ∩ t ∪ S ∩ t' := by
    ext z
    constructor
    · intro hz
      rcases hSt hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (h | h) <;> exact h.1
  set U₁ := C.Jplus ⊤ (S ∩ t) ∪ C.Jminus ⊤ (S ∩ t) with hU₁
  set U₂ := C.Jplus ⊤ (S ∩ t') ∪ C.Jminus ⊤ (S ∩ t') with hU₂
  have hU₁c : IsClosed U₁ := (Causal.Causality.isClosed_Jplus_of_isCompact hle hS₁).union
    (Causal.Causality.isClosed_Jminus_of_isCompact hle hS₁)
  have hU₂c : IsClosed U₂ := (Causal.Causality.isClosed_Jplus_of_isCompact hle hS₂).union
    (Causal.Causality.isClosed_Jminus_of_isCompact hle hS₂)
  have hcover : (univ : Set X) ⊆ U₁ ∪ U₂ := by
    intro x _
    obtain ⟨σ, hσ, h⟩ := hrel x
    rcases hSt hσ with hσt | hσt'
    · rcases h with h | h
      · exact Or.inl (Or.inl ⟨σ, ⟨hσ, hσt⟩, h⟩)
      · exact Or.inl (Or.inr ⟨σ, ⟨hσ, hσt⟩, h⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨σ, ⟨hσ, hσt'⟩, h⟩)
      · exact Or.inr (Or.inr ⟨σ, ⟨hσ, hσt'⟩, h⟩)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := hne'
  obtain ⟨x, -, hx₁, hx₂⟩ := (isPreconnected_closed_iff.1 isPreconnected_univ) U₁ U₂ hU₁c hU₂c
    hcover ⟨a, trivial, Or.inl ⟨a, ha, C.le_refl trivial⟩⟩
    ⟨b, trivial, Or.inl ⟨b, hb, C.le_refl trivial⟩⟩
  have hacS : ∀ {a' b'}, a' ∈ S ∩ t → b' ∈ S ∩ t' → C.le ⊤ a' b' → False := fun ha' hb' h =>
    Set.disjoint_left.1 hdisj ha' (hSac _ ha'.1 _ hb'.1 h ▸ hb')
  have hacS' : ∀ {a' b'}, a' ∈ S ∩ t → b' ∈ S ∩ t' → C.le ⊤ b' a' → False := fun ha' hb' h =>
    Set.disjoint_left.1 hdisj ha' ((hSac _ hb'.1 _ ha'.1 h).symm ▸ hb')
  rcases hx₁ with ⟨a', ha', h1⟩ | ⟨a', ha', h1⟩ <;> rcases hx₂ with ⟨b', hb', h2⟩ | ⟨b', hb', h2⟩
  · exact not_le_of_le_of_isCauchySurface hT hG hC hext hS hSac hS₁ hS₂ hSS hdisj ha' hb' h1 h2
  · exact hacS ha' hb' (C.le_trans h1 h2)
  · exact hacS' ha' hb' (C.le_trans h2 h1)
  · exact not_le_of_le_of_isCauchySurface (C := C.dual)
      (Causal.Causality.dual_tarentin.2 hT) (Causal.Causality.dual_globallyHyperbolic.2 hG)
      (Causal.Causality.dual_causallyArcConnectedOn.2 hC) hext.dual
      (Causal.Causality.dual_isCauchySurfaceOn.2 hS) (Causal.Causality.dual_isAcausal.2 hSac)
      hS₁ hS₂ hSS hdisj ha' hb' h1 h2

end Abstract

/-! ### §1b Model-free: small local Cauchy domains of a Cauchy surface (WP-46f)

The intrinsic content of B21 Prop 2.16's « spacelike » input (`exists_small_cauchyChart`, lemma K's
`IsLocallyCauchy`), with no graph theory: for a Cauchy surface `S` and an open `U`, the
**local Cauchy domain** `cauchyDomain C S U` is the set of points whose causal past down to `S`
(`J⁻(x) ∩ J⁺(S)`) and causal future down to `S` (`J⁺(x) ∩ J⁻(S)`) lie in `U`. It is inside `U`,
contains `S ∩ U`, is causally convex, is open (R1 compactness, closedness of `≤`, the tube lemma),
and `S` meets it in a Cauchy surface of it: an inextensible curve of the domain avoiding `S` lies
on Levin's time-parametrised inextensible curve of `X` (`exists_inextensible_of_timeFunction`),
whose arc down (or up) to its point of `S` stays in the domain by the saturation of the domain
along `J^∓` (`cauchyDomain_of_le_of_mem_Jplus`, `…_Jminus`), so the curve extends
(`E0Spear.extensible_of_timeGraph_future`, `…_past`, the technique of `isCauchySurfaceOn_of_isPast`). -/

section SmallCauchy

variable {X : Type} [TopologicalSpace X] {C : Causal.Causality X} {S U : Set X}

/-- **The local Cauchy domain** of a Cauchy surface `S` cut by `U` (WP-46f): the points whose causal
past down to `S` and whose causal future down to `S` stay in `U`. -/
def cauchyDomain (C : Causal.Causality X) (S U : Set X) : Set X :=
  {x | C.Jminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ U ∧ C.Jplus ⊤ {x} ∩ C.Jminus ⊤ S ⊆ U}

/-- In a causal spacetime, above an acausal `S` and below it at once is a single point:
`y ∈ J⁺(S)`, `y ≤ z`, `z ∈ J⁻(S)` force `z = y`. -/
theorem eq_of_mem_Jplus_of_le_of_mem_Jminus (hcaus : C.IsCausal) (hac : C.IsAcausal S)
    {y z : X} (hy : y ∈ C.Jplus ⊤ S) (hyz : C.le ⊤ y z) (hz : z ∈ C.Jminus ⊤ S) : z = y := by
  obtain ⟨σ, hσ, hσy⟩ := hy
  obtain ⟨σ', hσ', hzσ'⟩ := hz
  have e : σ = σ' := hac σ hσ σ' hσ' (C.le_trans hσy (C.le_trans hyz hzσ'))
  subst e
  have hyσ : C.le ⊤ y σ := C.le_trans hyz hzσ'
  have h1 : y = σ := hcaus hyσ hσy
  have hzy : C.le ⊤ z y := by rw [h1]; exact hzσ'
  exact hcaus hzy hyz

/-- The local Cauchy domain lies in `U` (every point is above or below `S`). -/
theorem cauchyDomain_subset (hcov : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) :
    cauchyDomain C S U ⊆ U := by
  intro x hx
  rcases hcov x with h | h
  · exact hx.1 ⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_refl trivial), h⟩
  · exact hx.2 ⟨Causal.Precausality.mem_Jplus_singleton.2 (C.le_refl trivial), h⟩

/-- A point of `S ∩ U` is in the local Cauchy domain (`J^∓(s) ∩ J^±(S) = {s}`). -/
theorem mem_cauchyDomain (hcaus : C.IsCausal) (hac : C.IsAcausal S) {s : X} (hs : s ∈ S)
    (hsU : s ∈ U) : s ∈ cauchyDomain C S U := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have := eq_of_mem_Jplus_of_le_of_mem_Jminus hcaus hac hz.2
      (Causal.Precausality.mem_Jminus_singleton.1 hz.1) ⟨s, hs, C.le_refl trivial⟩
    rw [← this]; exact hsU
  · have := eq_of_mem_Jplus_of_le_of_mem_Jminus hcaus hac ⟨s, hs, C.le_refl trivial⟩
      (Causal.Precausality.mem_Jplus_singleton.1 hz.1) hz.2
    rw [this]; exact hsU

/-- **Past saturation above `S`**: a point of `J⁺(S)` below a point of the domain is in it. -/
theorem cauchyDomain_of_le_of_mem_Jplus (hcaus : C.IsCausal) (hac : C.IsAcausal S) {x y : X}
    (hx : x ∈ cauchyDomain C S U) (hyx : C.le ⊤ y x) (hy : y ∈ C.Jplus ⊤ S) :
    y ∈ cauchyDomain C S U := by
  refine ⟨fun z hz => hx.1 ⟨Causal.Precausality.mem_Jminus_singleton.2
    (C.le_trans (Causal.Precausality.mem_Jminus_singleton.1 hz.1) hyx), hz.2⟩, fun z hz => ?_⟩
  have := eq_of_mem_Jplus_of_le_of_mem_Jminus hcaus hac hy
    (Causal.Precausality.mem_Jplus_singleton.1 hz.1) hz.2
  rw [this]
  exact hx.1 ⟨Causal.Precausality.mem_Jminus_singleton.2 hyx, hy⟩

/-- **Future saturation below `S`**: a point of `J⁻(S)` above a point of the domain is in it. -/
theorem cauchyDomain_of_le_of_mem_Jminus (hcaus : C.IsCausal) (hac : C.IsAcausal S) {x y : X}
    (hx : x ∈ cauchyDomain C S U) (hxy : C.le ⊤ x y) (hy : y ∈ C.Jminus ⊤ S) :
    y ∈ cauchyDomain C S U := by
  refine ⟨fun z hz => ?_, fun z hz => hx.2 ⟨Causal.Precausality.mem_Jplus_singleton.2
    (C.le_trans hxy (Causal.Precausality.mem_Jplus_singleton.1 hz.1)), hz.2⟩⟩
  have := eq_of_mem_Jplus_of_le_of_mem_Jminus hcaus hac hz.2
    (Causal.Precausality.mem_Jminus_singleton.1 hz.1) hy
  rw [← this]
  exact hx.2 ⟨Causal.Precausality.mem_Jplus_singleton.2 hxy, hy⟩

/-- **The local Cauchy domain is causally convex.** -/
theorem causallyConvexIn_cauchyDomain : C.CausallyConvexIn (cauchyDomain C S U) ⊤ := by
  refine ⟨subset_univ _, fun p hp q hq z hz => ?_⟩
  obtain ⟨hpz, hzq⟩ := Causal.Causality.mem_diamond.1 hz
  exact ⟨fun w hw => hq.1 ⟨Causal.Precausality.mem_Jminus_singleton.2
      (C.le_trans (Causal.Precausality.mem_Jminus_singleton.1 hw.1) hzq), hw.2⟩,
    fun w hw => hp.2 ⟨Causal.Precausality.mem_Jplus_singleton.2
      (C.le_trans hpz (Causal.Precausality.mem_Jplus_singleton.1 hw.1)), hw.2⟩⟩

/-- **The local Cauchy domain of an open `U` is open**, given R1 (`J⁺(S) ∩ J⁻(q)` and
`J⁻(S) ∩ J⁺(q)` compact): near `x`, inside a tarentin diamond `J(a, b)`, the pasts down to `S` lie
in the compact `J⁺(S) ∩ J⁻(b)`, whose part outside `U` is not below `x`; closedness of `≤` and the
tube lemma keep it not below the points near `x` (dually for the futures). -/
theorem isOpen_cauchyDomain [T2Space X] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hcP : ∀ q, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q}))
    (hcM : ∀ q, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {q})) (hU : IsOpen U) :
    IsOpen (cauchyDomain C S U) := by
  have hle := hG.isClosed_le hT
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨a, -, b, -, hab⟩ := hT x univ univ_mem
  set Fp := (C.Jplus ⊤ S ∩ C.Jminus ⊤ {b}) ∩ Uᶜ with hFp
  have hFpc : IsCompact Fp := (hcP b).inter_right hU.isClosed_compl
  have hFpx : Fp ×ˢ ({x} : Set X) ⊆ {z : X × X | C.le ⊤ z.1 z.2}ᶜ := by
    rintro ⟨y, x'⟩ ⟨hy, hx'⟩ hyx
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hy.2 (hx.1 ⟨Causal.Precausality.mem_Jminus_singleton.2 hyx, hy.1.1⟩)
  obtain ⟨u₁, v₁, -, hv₁, hFu₁, hxv₁, huv₁⟩ :=
    generalized_tube_lemma hFpc isCompact_singleton hle.isOpen_compl hFpx
  set Fm := (C.Jminus ⊤ S ∩ C.Jplus ⊤ {a}) ∩ Uᶜ with hFm
  have hFmc : IsCompact Fm := (hcM a).inter_right hU.isClosed_compl
  have hxFm : ({x} : Set X) ×ˢ Fm ⊆ {z : X × X | C.le ⊤ z.1 z.2}ᶜ := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩ hxy
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hy.2 (hx.2 ⟨Causal.Precausality.mem_Jplus_singleton.2 hxy, hy.1.1⟩)
  obtain ⟨u₂, v₂, hu₂, -, hxu₂, hFv₂, huv₂⟩ :=
    generalized_tube_lemma isCompact_singleton hFmc hle.isOpen_compl hxFm
  have hnb : C.openDiamond ⊤ a b ∩ v₁ ∩ u₂ ∈ 𝓝 x :=
    ((Causal.Causality.isOpen_openDiamond.inter hv₁).inter hu₂).mem_nhds
      ⟨⟨hab, hxv₁ (mem_singleton x)⟩, hxu₂ (mem_singleton x)⟩
  refine mem_of_superset hnb fun x' hx' => ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨⟨hx'D, hx'v⟩, -⟩ := hx'
    have hzx' := Causal.Precausality.mem_Jminus_singleton.1 hz.1
    have hx'b := (Causal.Causality.mem_diamond.1
      (Causal.Causality.openDiamond_subset_diamond hx'D)).2
    by_contra hzU
    have hzF : z ∈ Fp := ⟨⟨hz.2, Causal.Precausality.mem_Jminus_singleton.2
      (C.le_trans hzx' hx'b)⟩, hzU⟩
    exact huv₁ (show (z, x') ∈ u₁ ×ˢ v₁ from ⟨hFu₁ hzF, hx'v⟩) hzx'
  · obtain ⟨⟨hx'D, -⟩, hx'u⟩ := hx'
    have hx'z := Causal.Precausality.mem_Jplus_singleton.1 hz.1
    have hax' := (Causal.Causality.mem_diamond.1
      (Causal.Causality.openDiamond_subset_diamond hx'D)).1
    by_contra hzU
    have hzF : z ∈ Fm := ⟨⟨hz.2, Causal.Precausality.mem_Jplus_singleton.2
      (C.le_trans hax' hx'z)⟩, hzU⟩
    exact huv₂ (show (x', z) ∈ u₂ ×ˢ v₂ from ⟨hx'u, hFv₂ hzF⟩) hx'z

/-- **`S` meets its local Cauchy domain in a Cauchy surface of it** (given a continuous function
strictly increasing along `≤`): an inextensible curve `c` of the domain `W` lies on an inextensible
time-parametrised curve `γ` of `X`, which meets `S` at time `tS`; if `c` avoided `S`, its times
would all be below `tS` (or all above, intermediate value theorem), and the arc of `γ` from `c` up
to (or down from) `S` stays in `W` by saturation, so `c` would extend in `W`. -/
theorem isCauchySurfaceOn_cauchyDomain (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    {T : X → ℝ} (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hS : C.IsCauchySurface S) {W : Opens X} (hW : (W : Set X) = cauchyDomain C S U) :
    C.IsCauchySurfaceOn W (S ∩ W) := by
  have hac : C.IsAcausal S := hS.isAcausal_of_timeFunction hC hTc hT
  intro I c hc
  have hcT := hc.1.mono_opens le_top
  obtain ⟨J, γ, hγ, hsub, hTγ⟩ := Causal.Causality.exists_inextensible_of_timeFunction hTc hT hcT
  obtain ⟨_, ⟨⟨tS, htS, rfl⟩, hγS⟩, -⟩ := hS J γ hγ
  have hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t := by
    intro t ht
    obtain ⟨u, hu, hcu⟩ := hsub ⟨t, ht, rfl⟩
    rw [← hcu, hTγ u hu]; exact ⟨hu, rfl⟩
  have hcW : ∀ t ∈ I, c t ∈ cauchyDomain C S U := fun t ht => by
    rw [← hW]; exact hc.1.mem ht
  have hex : ∃ t ∈ I, c t ∈ S := by
    by_contra hno
    push Not at hno
    have hne : ∀ t ∈ I, T (c t) ≠ tS := fun t ht e =>
      hno t ht (by rw [← (hcγ t ht).2, e]; exact hγS)
    obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
    by_cases hall : ∀ t ∈ I, T (c t) < tS
    · -- the future case: the arc of `γ` from `c` up to `S` is in `W` (below `S`)
      set J' : Set ℝ := {u | u ∈ J ∧ u ≤ tS ∧ ∃ t ∈ I, T (c t) ≤ u} with hJ'
      have hJ'mem : ∀ u ∈ J', γ u ∈ W := by
        rintro u ⟨hu, hutS, t, ht, htu⟩
        have h1 := hγ.1.le_of_le (hcγ t ht).1 hu htu
        rw [(hcγ t ht).2] at h1
        have h2 := hγ.1.le_of_le hu htS hutS
        rw [SetLike.mem_coe.symm, hW]
        exact cauchyDomain_of_le_of_mem_Jminus hcaus hac (hcW t ht) h1 ⟨γ tS, hγS, h2⟩
      have hJ'oc : J'.OrdConnected := ⟨fun x hx y hy z hz => by
        refine ⟨hγ.1.ordConnected.out hx.1 hy.1 hz, hz.2.trans hy.2.1, ?_⟩
        obtain ⟨t, ht, h⟩ := hx.2.2
        exact ⟨t, ht, h.trans hz.1⟩⟩
      have htS' : tS ∈ J' := ⟨htS, le_rfl, t₀, ht₀, (hall t₀ ht₀).le⟩
      have hγ' : C.CausalCurveIn W J' γ := ⟨⟨tS, htS'⟩, hJ'oc, fun a ha b hb =>
        Causal.CurveOn.restrict (hγ.1.curve a ha.1 b hb.1) le_rfl le_rfl le_top
          fun u hu => hJ'mem u (hJ'oc.out ha hb hu)⟩
      have hcγ' : ∀ t ∈ I, T (c t) ∈ J' ∧ γ (T (c t)) = c t := fun t ht =>
        ⟨⟨(hcγ t ht).1, (hall t ht).le, t, ht, le_rfl⟩, (hcγ t ht).2⟩
      have hTγ' : ∀ τ ∈ J', T (γ τ) = τ := fun τ hτ => hTγ τ hτ.1
      exact hc.2 (E0Spear.extensible_of_timeGraph_future hC hcaus hTc hT hγ' hTγ' hc.1 hcγ'
        htS' hall)
    · push Not at hall
      obtain ⟨t₁, ht₁, h₁⟩ := hall
      have hgt : ∀ t ∈ I, tS < T (c t) := by
        intro t ht
        by_contra h
        push Not at h
        have hsub' : uIcc t t₁ ⊆ I := hc.1.ordConnected.uIcc_subset ht ht₁
        have hcont : ContinuousOn (T ∘ c) (uIcc t t₁) :=
          hTc.comp_continuousOn ((E0Spear.continuousOn_of_causalCurveIn hc.1).mono hsub')
        obtain ⟨s, hs, hse⟩ := intermediate_value_uIcc hcont (Set.mem_uIcc_of_le h h₁)
        exact hne s (hsub' hs) hse
      -- the past case: the arc of `γ` from `S` up to `c` is in `W` (above `S`)
      set J' : Set ℝ := {u | u ∈ J ∧ tS ≤ u ∧ ∃ t ∈ I, u ≤ T (c t)} with hJ'
      have hJ'mem : ∀ u ∈ J', γ u ∈ W := by
        rintro u ⟨hu, htSu, t, ht, hut⟩
        have h1 := hγ.1.le_of_le hu (hcγ t ht).1 hut
        rw [(hcγ t ht).2] at h1
        have h2 := hγ.1.le_of_le htS hu htSu
        rw [SetLike.mem_coe.symm, hW]
        exact cauchyDomain_of_le_of_mem_Jplus hcaus hac (hcW t ht) h1 ⟨γ tS, hγS, h2⟩
      have hJ'oc : J'.OrdConnected := ⟨fun x hx y hy z hz => by
        refine ⟨hγ.1.ordConnected.out hx.1 hy.1 hz, hx.2.1.trans hz.1, ?_⟩
        obtain ⟨t, ht, h⟩ := hy.2.2
        exact ⟨t, ht, hz.2.trans h⟩⟩
      have htS' : tS ∈ J' := ⟨htS, le_rfl, t₀, ht₀, (hgt t₀ ht₀).le⟩
      have hγ' : C.CausalCurveIn W J' γ := ⟨⟨tS, htS'⟩, hJ'oc, fun a ha b hb =>
        Causal.CurveOn.restrict (hγ.1.curve a ha.1 b hb.1) le_rfl le_rfl le_top
          fun u hu => hJ'mem u (hJ'oc.out ha hb hu)⟩
      have hcγ' : ∀ t ∈ I, T (c t) ∈ J' ∧ γ (T (c t)) = c t := fun t ht =>
        ⟨⟨(hcγ t ht).1, (hgt t ht).le, t, ht, le_rfl⟩, (hcγ t ht).2⟩
      have hTγ' : ∀ τ ∈ J', T (γ τ) = τ := fun τ hτ => hTγ τ hτ.1
      exact hc.2 (E0Spear.extensible_of_timeGraph_past hC hcaus hTc hT hγ' hTγ' hc.1 hcγ'
        htS' hgt)
  obtain ⟨t, ht, hcS⟩ := hex
  refine ⟨c t, ⟨mem_image_of_mem c ht, hcS, hc.1.mem ht⟩, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsS, -⟩
  rcases le_total s t with h | h
  · exact hac _ hsS _ hcS ((hc.1.mono_opens le_top).le_of_le hs ht h)
  · exact (hac _ hcS _ hsS ((hc.1.mono_opens le_top).le_of_le ht hs h)).symm

/-- **Small local Cauchy charts of a Cauchy surface, model-free** (WP-46f): in a Hausdorff tarentin
globally hyperbolic causally arc-connected spacetime with a continuous function strictly
increasing along `≤` and R1, every point `s` of a Cauchy surface `S` and every neighbourhood `O`
of `s` admit an open `W ∋ s` inside `O`, causally convex, in which `S ∩ W` is a Cauchy surface:
`W = cauchyDomain C S (interior O)`. -/
theorem exists_small_cauchyChart_abstract [T2Space X] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {Tf : X → ℝ} (hTc : Continuous Tf)
    (hTf : ∀ x y, C.le ⊤ x y → x ≠ y → Tf x < Tf y)
    (hcP : ∀ q, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q}))
    (hcM : ∀ q, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {q})) (hS : C.IsCauchySurface S) {s : X}
    (hs : s ∈ S) {O : Set X} (hO : O ∈ 𝓝 s) :
    ∃ W : Opens X, s ∈ W ∧ (W : Set X) ⊆ O ∧ C.CausallyConvexIn (W : Set X) ⊤ ∧
      C.IsCauchySurfaceOn W (S ∩ W) := by
  have hext := Causal.Causality.curvesExtend_of_timeFunction hTc hTf
  have hac : C.IsAcausal S := hS.isAcausal_of_timeFunction hC hTc hTf
  let W : Opens X := ⟨cauchyDomain C S (interior O), isOpen_cauchyDomain hT hG hcP hcM isOpen_interior⟩
  refine ⟨W, mem_cauchyDomain hG.1 hac hs (mem_interior_iff_mem_nhds.2 hO),
    (cauchyDomain_subset (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hS)).trans
      interior_subset, causallyConvexIn_cauchyDomain,
    isCauchySurfaceOn_cauchyDomain hC hG.1 hTc hTf hS rfl⟩

end SmallCauchy

/-! ### §2 Under `SingularFlatAxioms`: BTZ-extensions in open-set form (B21 Lemmas 2.13–2.15) -/

section SFA

variable {X : Type*} [TopologicalSpace X] {C : Causal.Causality X} {sing : ℝ → Set X}

/-- A point in the chronological future of another is regular (`I⁻ = ∅` at BTZ points). -/
theorem notMem_sing_of_lt (h : C.SingularFlatAxioms sing) {x y : X} (hxy : C.lt ⊤ x y) :
    y ∉ sing 0 := by
  intro hy
  have : x ∈ C.Iminus ⊤ {y} := Causal.Precausality.mem_Iminus_singleton.2 hxy
  rw [h.Iminus_eq_empty y hy] at this
  exact this

/-- Every point has a regular point in its chronological future (`Z⁺ = M`). -/
theorem exists_lt_notMem_sing (h : C.SingularFlatAxioms sing) (x : X) :
    ∃ q, C.lt ⊤ x q ∧ q ∉ sing 0 := by
  obtain ⟨q, hq, -⟩ := h.mem_Zplus x univ univ_mem
  have hxq : C.lt ⊤ x q := Causal.Precausality.mem_Iplus_singleton.1 hq
  exact ⟨q, hxq, notMem_sing_of_lt h hxq⟩

/-- **The regular part is causally convex** (BTZ points precede: B21 Lemma 1.9 in relational
form, `mem_sing_zero_of_le`). -/
theorem causallyConvexIn_reg (h : C.SingularFlatAxioms sing) :
    C.CausallyConvexIn ((sing 0)ᶜ) ⊤ := by
  refine ⟨subset_univ _, fun p hp q _ z hz hzs => ?_⟩
  exact hp (h.mem_sing_zero_of_le hzs (Causal.Causality.mem_diamond.1 hz).1)

/-- **B21 Lemma 2.13 (a)** (`BTZ_1.tex:1002, proof l.1010–1015`; open-set form, kb/0001): for an
open `A` whose complement consists of BTZ points (`A ↪ M` a BTZ-extension), `A` is causally
convex iff the BTZ part of the causal future of each BTZ point of `A` lies in `A`. -/
theorem btzExt_causallyConvexIn_iff (h : C.SingularFlatAxioms sing) {A : Opens X}
    (hA : (A : Set X)ᶜ ⊆ sing 0) :
    C.CausallyConvexIn (A : Set X) ⊤ ↔
      ∀ x ∈ sing 0, x ∈ A → ∀ y ∈ sing 0, C.le ⊤ x y → y ∈ A := by
  have hAreg : ∀ z, z ∉ sing 0 → z ∈ A := fun z hz => by_contra fun h' => hz (hA h')
  constructor
  · intro hconv x _ hxA y _ hxy
    obtain ⟨q, hyq, hqs⟩ := exists_lt_notMem_sing h y
    exact hconv.2 x hxA q (hAreg q hqs)
      (Causal.Causality.mem_diamond.2 ⟨hxy, C.le_of_lt hyq⟩)
  · intro hS
    refine ⟨subset_univ _, fun p hp q _ z hz => ?_⟩
    by_cases hzs : z ∈ sing 0
    · have hpz := (Causal.Causality.mem_diamond.1 hz).1
      exact hS p (h.mem_sing_zero_of_le hzs hpz) hp z hzs hpz
    · exact hAreg z hzs

/-- **B21 Lemma 2.13 (b)** (`BTZ_1.tex:1003, proof l.1017–1019`; open-set form): a globally hyperbolic open
`A` whose complement consists of BTZ points is causally convex. The paper's sup argument along
a causal curve from a BTZ point of `A`: at the first parameter `t` leaving `A`, every earlier point
lies in the compact diamond `J_A(c 0, q')` for a regular `q' ≫ c t` (push-up, `I⁻ = ∅` at BTZ
points, so the chronal curve to `q'` stays in `A`), hence so does `c t`. -/
theorem btzExt_causallyConvexIn_of_globallyHyperbolicOn
    (h : C.SingularFlatAxioms sing) {A : Opens X} (hA : (A : Set X)ᶜ ⊆ sing 0)
    (hG : C.GloballyHyperbolicOn A) : C.CausallyConvexIn (A : Set X) ⊤ := by
  haveI := h.t2
  have hAreg : ∀ z, z ∉ sing 0 → z ∈ A := fun z hz => by_contra fun h' => hz (hA h')
  refine ⟨subset_univ _, fun p hp q _ z hz => ?_⟩
  by_cases hzs : z ∉ sing 0
  · exact hAreg z hzs
  obtain ⟨hpz, -⟩ := Causal.Causality.mem_diamond.1 hz
  obtain ⟨c, hc, hc0, hc1⟩ := (h.causallyArcConnected ⊤ le_rfl p z).1.1 hpz
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
  -- the closing step: a point all of whose predecessors on the curve are in `A` is in `A`
  have key : ∀ t ∈ Icc (0 : ℝ) 1, (∀ s ∈ Ico (0 : ℝ) t, c s ∈ A) → c t ∈ A := by
    intro t ht hlow
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0, hc0]; exact hp
    obtain ⟨q', hq', hq'reg⟩ := exists_lt_notMem_sing h (c t)
    have hmem : ∀ s ∈ Ico (0 : ℝ) t, c s ∈ C.diamond A p q' := by
      intro s hs
      have hsA := hlow s hs
      have hcs : C.CausalCurveOn A c 0 s :=
        Causal.CurveOn.restrict hc le_rfl (hs.2.le.trans ht.2) le_top
          fun σ hσ => hlow σ ⟨hσ.1, hσ.2.trans_lt hs.2⟩
      have h1 : C.le A p (c s) := by
        have := hcs.le_of_le le_rfl hs.1 le_rfl
        rwa [hc0] at this
      have hst : C.le ⊤ (c s) (c t) := hc.le_of_le hs.1 hs.2.le ht.2
      have hlt : C.lt ⊤ (c s) q' := h.pushUp.lt_of_le_of_lt hst hq'
      obtain ⟨γ, hγ, hγ0, hγ1⟩ := (h.causallyArcConnected ⊤ le_rfl (c s) q').2.1 hlt
      have hγA : ∀ σ ∈ Icc (0 : ℝ) 1, γ σ ∈ A := by
        intro σ hσ
        rcases hσ.1.eq_or_lt with e | e
        · rw [← e, hγ0]; exact hsA
        · have hl := hγ.lt_of_lt le_rfl e hσ.2
          rw [hγ0] at hl
          exact hAreg _ (notMem_sing_of_lt h hl)
      have hγ' : C.ChronalCurveOn A γ 0 1 :=
        Causal.CurveOn.restrict hγ le_rfl le_rfl le_top hγA
      have h2 : C.le A (c s) q' := by
        have := hγ'.lt_of_lt le_rfl zero_lt_one le_rfl
        rw [hγ0, hγ1] at this
        exact C.le_of_lt this
      exact Causal.Causality.mem_diamond.2 ⟨h1, h2⟩
    have hK : IsClosed (C.diamond A p q') := (hG.2 p q').isClosed
    have hcw : ContinuousWithinAt c (Ico 0 t) t :=
      (hcont t ht).mono fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩
    have hcl : c t ∈ closure (c '' Ico 0 t) :=
      hcw.mem_closure_image (by rw [closure_Ico h0.ne]; exact right_mem_Icc.2 h0.le)
    have hct : c t ∈ C.diamond A p q' :=
      closure_minimal (by rintro _ ⟨s, hs, rfl⟩; exact hmem s hs) hK hcl
    exact C.le_mem_right (Causal.Causality.mem_diamond.1 hct).1
  -- the first exit time
  by_contra hzA
  set S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ c t ∉ A} with hSdef
  have h1S : (1 : ℝ) ∈ S := ⟨right_mem_Icc.2 zero_le_one, by rw [hc1]; exact hzA⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have ht₀ : sInf S ∈ Icc (0 : ℝ) 1 :=
    ⟨le_csInf hSne fun t ht => ht.1.1, csInf_le hSbdd h1S⟩
  have hlow : ∀ s ∈ Ico (0 : ℝ) (sInf S), c s ∈ A := fun s hs => by
    by_contra hsA
    have : sInf S ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans ht₀.2⟩, hsA⟩
    exact absurd hs.2 (not_lt.2 this)
  have hct₀ := key _ ht₀ hlow
  have hpre : c ⁻¹' A ∈ 𝓝[Icc 0 1] (sInf S) :=
    (hcont _ ht₀).preimage_mem_nhdsWithin (A.isOpen.mem_nhds hct₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  have hge : sInf S + ε ≤ sInf S := by
    refine le_csInf hSne fun s hs => ?_
    by_contra hlt
    push Not at hlt
    have hs0 : sInf S ≤ s := csInf_le hSbdd hs
    refine hs.2 (hball ⟨?_, hs.1⟩)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  linarith

/-- Strong causality of the open set `A` seen as a spacetime (`def:strongly_causal_spacetime`
relativised, kb/0001): every point of `A` has arbitrarily small neighbourhoods causally convex
in `A`. -/
def StronglyCausalOn (C : Causal.Causality X) (A : Opens X) : Prop :=
  ∀ p ∈ A, ∀ U ∈ 𝓝 p, ∃ V ∈ 𝓝 p, V ⊆ U ∧ C.CausallyConvexIn V A

/-- **No closed causal loop inside `K`**: `C.le ⊤` is antisymmetric on `K`. The explicit
hypothesis of the abstract Lemma 2.14 and Cor 2.15 below (`K = sing₀`, resp. `K = Aᶜ`): an
abstract `SingularFlatAxioms` causality carries neither `𝔼₀` charts nor Prop 1.3's tube, so the
paper's exclusion of a closed BTZ loop (`BTZ_1.tex:1035–1036`) is not available there. For
`𝔼₀`-manifolds it is proved: `sing_eq_of_le_of_le_of_stronglyCausalOn_e0` (§2b, §3). -/
def NoCausalLoopIn (C : Causal.Causality X) (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, C.le ⊤ x y → C.le ⊤ y x → x = y

/-- **B21 Lemma 2.14** (`BTZ_1.tex:1026–1037`; open-set form, abstract): a BTZ-extension of a
strongly causal `A` with no closed BTZ loop (`hloop`, explicit: see `NoCausalLoopIn`) is causal.
The regular case (l.1033): two regular causal points lie in a diamond of regular points (BTZ
points precede), inside `A`, and strong causality of `A` separates them; a loop through a BTZ
point stays in `sing₀` (l.1031) and is excluded by `hloop`. The unconditional `𝔼₀` form is
`btzExt_isCausal_of_stronglyCausalOn_e0`. -/
theorem btzExt_isCausal_of_stronglyCausalOn (h : C.SingularFlatAxioms sing)
    {A : Opens X} (hA : (A : Set X)ᶜ ⊆ sing 0) (hSC : StronglyCausalOn C A)
    (hloop : NoCausalLoopIn C (sing 0)) : C.IsCausal := by
  haveI := h.t2
  have hAreg : ∀ z, z ∉ sing 0 → z ∈ A := fun z hz => by_contra fun h' => hz (hA h')
  intro x y hxy hyx
  by_cases hx : x ∈ sing 0
  · exact hloop x hx y (h.mem_sing_zero_of_le hx hyx) hxy hyx
  have hy : y ∉ sing 0 := fun hy => hx (h.mem_sing_zero_of_le hy hxy)
  have hsub : C.diamond ⊤ x x ⊆ A := fun z hz =>
    hAreg z fun hzs => hx (h.mem_sing_zero_of_le hzs (Causal.Causality.mem_diamond.1 hz).1)
  have hxD : x ∈ C.diamond ⊤ x x := Causal.Causality.mem_diamond.2 ⟨C.le_refl trivial, C.le_refl trivial⟩
  have hyD : y ∈ C.diamond ⊤ x x := Causal.Causality.mem_diamond.2 ⟨hxy, hyx⟩
  have hxyA : C.le A x y := le_of_diamond_subset h.causallyArcConnected hsub hxD hyD hxy
  have hyxA : C.le A y x := le_of_diamond_subset h.causallyArcConnected hsub hyD hxD hyx
  by_contra hne
  obtain ⟨U, hU, hyU⟩ : ∃ U ∈ 𝓝 x, y ∉ U :=
    ⟨{y}ᶜ, isOpen_compl_singleton.mem_nhds hne, fun h => h rfl⟩
  obtain ⟨V, hV, hVU, hconv⟩ := hSC x (hAreg x hx) U hU
  exact hyU (hVU (hconv.2 x (mem_of_mem_nhds hV) x (mem_of_mem_nhds hV)
    (Causal.Causality.mem_diamond.2 ⟨hxyA, hyxA⟩)))

/-- **A globally hyperbolic BTZ-extended open set is strongly causal** (the step "globally
hyperbolic ⇒ strongly causal" of B21 Cor 2.15, l.1038–1039): `A` is causally convex (Lemma 2.13(b)),
so `X`'s tarentin diamonds at points of `A` are diamonds of `A`, and the library's
`GloballyHyperbolic.stronglyCausal` applies to `A` read as a space. -/
theorem stronglyCausalOn_of_globallyHyperbolicOn (h : C.SingularFlatAxioms sing)
    {A : Opens X} (hA : (A : Set X)ᶜ ⊆ sing 0) (hG : C.GloballyHyperbolicOn A) :
    StronglyCausalOn C A := by
  haveI := h.t2
  have hconv := btzExt_causallyConvexIn_of_globallyHyperbolicOn h hA hG
  set D := (C.restrict A).toSubtype with hDdef
  have hD : D.GloballyHyperbolic := Causal.Causality.globallyHyperbolic_toSubtype hG
  have hle : ∀ x y : A, D.le ⊤ x y ↔ C.le A x y := fun x y => by
    show C.le (Causal.imageOpens (⊤ : Opens A)) x y ↔ _
    rw [Causal.imageOpens_top]
  have hdiam : ∀ p q : A, D.diamond ⊤ p q = Subtype.val ⁻¹' C.diamond ⊤ p q := by
    intro p q
    have hsub : C.diamond ⊤ p q ⊆ A := hconv.2 p p.2 q q.2
    ext z
    rw [mem_preimage, Causal.Causality.mem_diamond, hle, hle, ← Causal.Causality.mem_diamond,
      diamond_eq_of_subset h.causallyArcConnected hsub]
  have hemb : IsOpenEmbedding (Subtype.val : A → X) := A.isOpen.isOpenEmbedding_subtypeVal
  have hT : D.Tarentin := by
    intro x U hU
    have hU' : Subtype.val '' U ∈ 𝓝 (x : X) := hemb.image_mem_nhds.2 hU
    obtain ⟨p, ⟨p', hp', rfl⟩, q, ⟨q', hq', rfl⟩, hx⟩ := h.tarentin x.1 _ hU'
    refine ⟨p', hp', q', hq', ?_⟩
    show x ∈ interior (D.diamond ⊤ p' q')
    rw [hdiam]
    exact preimage_interior_subset_interior_preimage continuous_subtype_val hx
  have hSC := hD.stronglyCausal hT
  intro p hp U hU
  obtain ⟨V, hV, hVU, hVconv⟩ := hSC ⟨p, hp⟩ (Subtype.val ⁻¹' U)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hU)
  refine ⟨Subtype.val '' V, hemb.image_mem_nhds.2 hV, image_subset_iff.2 hVU,
    fun z ⟨w, _, hw⟩ => hw ▸ w.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
  have hzA : z ∈ A := C.le_mem_right (Causal.Causality.mem_diamond.1 hz).1
  refine ⟨⟨z, hzA⟩, hVconv.2 a ha b hb ?_, rfl⟩
  rw [Causal.Causality.mem_diamond, hle, hle]
  exact Causal.Causality.mem_diamond.1 hz

/-- **B21 Cor 2.15** (`cor:GH_causal`, `BTZ_1.tex:1038–1039`; open-set form, abstract): a
BTZ-extension of a globally hyperbolic open set `A` with no closed causal loop OUTSIDE `A`
(`hloop`, explicit) is causal. A loop meeting `A` lies in `A` (Lemma 2.13(b): `A` causally convex,
so the diamond `J(x, x)` through the loop is in `A`) and `A` is causal; a loop outside `A` is
BTZ (`Aᶜ ⊆ sing₀`) and excluded by `hloop`. The unconditional `𝔼₀` form is `cor_GH_causal_e0`. -/
theorem cor_GH_causal (h : C.SingularFlatAxioms sing) {A : Opens X}
    (hA : (A : Set X)ᶜ ⊆ sing 0) (hG : C.GloballyHyperbolicOn A)
    (hloop : NoCausalLoopIn C ((A : Set X)ᶜ)) : C.IsCausal := by
  have hconv := btzExt_causallyConvexIn_of_globallyHyperbolicOn h hA hG
  have hin : ∀ {x y : X}, x ∈ A → C.le ⊤ x y → C.le ⊤ y x → C.le A x y ∧ C.le A y x := by
    intro x y hx hxy hyx
    have hsub : C.diamond ⊤ x x ⊆ A := hconv.2 x hx x hx
    have hxD : x ∈ C.diamond ⊤ x x :=
      Causal.Causality.mem_diamond.2 ⟨C.le_refl trivial, C.le_refl trivial⟩
    have hyD : y ∈ C.diamond ⊤ x x := Causal.Causality.mem_diamond.2 ⟨hxy, hyx⟩
    exact ⟨le_of_diamond_subset h.causallyArcConnected hsub hxD hyD hxy,
      le_of_diamond_subset h.causallyArcConnected hsub hyD hxD hyx⟩
  intro x y hxy hyx
  by_cases hx : x ∈ A
  · obtain ⟨h1, h2⟩ := hin hx hxy hyx
    exact hG.1 h1 h2
  by_cases hy : y ∈ A
  · obtain ⟨h1, h2⟩ := hin hy hyx hxy
    exact (hG.1 h1 h2).symm
  exact hloop x hx y hy hxy hyx

/-- **The causality bullet of B21 Prop 2.17's proof** (`BTZ_1.tex:1099`, the instance of Cor 2.15
it uses), in open-set form: a spacetime covered by opens `A ⊇ sing₀` and `B` regular with
`Bᶜ ⊆ sing₀`, `A` and `B` globally hyperbolic, is causal. No closed BTZ loop arises: a loop through
BTZ points lies in `sing₀ ⊆ A`. -/
theorem isCausal_of_twoOpens (h : C.SingularFlatAxioms sing) {A B : Opens X}
    (hsA : sing 0 ⊆ A) (hBc : (B : Set X)ᶜ ⊆ sing 0) (hGA : C.GloballyHyperbolicOn A)
    (hGB : C.GloballyHyperbolicOn B) : C.IsCausal := by
  haveI := h.t2
  have hBreg : ∀ z, z ∉ sing 0 → z ∈ B := fun z hz => by_contra fun h' => hz (hBc h')
  have hconvB := btzExt_causallyConvexIn_of_globallyHyperbolicOn h hBc hGB
  intro x y hxy hyx
  by_cases hx : x ∈ sing 0
  · have hy : y ∈ sing 0 := h.mem_sing_zero_of_le hx hyx
    have hsub : ∀ a b, b ∈ sing 0 → C.diamond ⊤ a b ⊆ A := fun a b hb z hz =>
      hsA (h.mem_sing_zero_of_le hb (Causal.Causality.mem_diamond.1 hz).2)
    have hxD : x ∈ C.diamond ⊤ x y := Causal.Causality.mem_diamond.2 ⟨C.le_refl trivial, hxy⟩
    have hyD : y ∈ C.diamond ⊤ x y := Causal.Causality.mem_diamond.2 ⟨hxy, C.le_refl trivial⟩
    have hxD' : x ∈ C.diamond ⊤ y x := Causal.Causality.mem_diamond.2 ⟨hyx, C.le_refl trivial⟩
    have hyD' : y ∈ C.diamond ⊤ y x := Causal.Causality.mem_diamond.2 ⟨C.le_refl trivial, hyx⟩
    exact hGA.1 (le_of_diamond_subset h.causallyArcConnected (hsub x y hy) hxD hyD hxy)
      (le_of_diamond_subset h.causallyArcConnected (hsub y x hx) hyD' hxD' hyx)
  · have hy : y ∉ sing 0 := fun hy => hx (h.mem_sing_zero_of_le hy hxy)
    exact hGB.1
      ((Causal.Causality.le_iff_of_causallyConvexIn h.causallyArcConnected hconvB (hBreg y hy)
        (hBreg x hx)).2 hxy)
      ((Causal.Causality.le_iff_of_causallyConvexIn h.causallyArcConnected hconvB (hBreg x hx)
        (hBreg y hy)).2 hyx)

/-- **The diamond bullet of B21 Prop 2.17's proof** (`BTZ_1.tex:1100–1102`), in open-set form: in
the situation of `isCausal_of_twoOpens`, every diamond `J(p, q)` is compact once the mixed
diamonds (`p` BTZ, `q` regular) are. A diamond with a regular lower tip is a diamond of `B`
(BTZ points precede), one with a BTZ upper tip a diamond of `A`. -/
theorem isCompact_diamond_of_twoOpens (h : C.SingularFlatAxioms sing) {A B : Opens X}
    (hsA : sing 0 ⊆ A) (hBc : (B : Set X)ᶜ ⊆ sing 0) (hGA : C.GloballyHyperbolicOn A)
    (hGB : C.GloballyHyperbolicOn B)
    (hmix : ∀ p ∈ sing 0, ∀ q ∉ sing 0, IsCompact (C.diamond ⊤ p q)) (p q : X) :
    IsCompact (C.diamond ⊤ p q) := by
  have hBreg : ∀ z, z ∉ sing 0 → z ∈ B := fun z hz => by_contra fun h' => hz (hBc h')
  by_cases hp : p ∈ sing 0
  · by_cases hq : q ∈ sing 0
    · have hsub : C.diamond ⊤ p q ⊆ A := fun z hz =>
        hsA (h.mem_sing_zero_of_le hq (Causal.Causality.mem_diamond.1 hz).2)
      rw [← diamond_eq_of_subset h.causallyArcConnected hsub]
      exact hGA.2 p q
    · exact hmix p hp q hq
  · have hsub : C.diamond ⊤ p q ⊆ B := fun z hz =>
      hBreg z fun hzs => hp (h.mem_sing_zero_of_le hzs (Causal.Causality.mem_diamond.1 hz).1)
    rw [← diamond_eq_of_subset h.causallyArcConnected hsub]
    exact hGB.2 p q

/-- **B21 Prop 2.17's proof, global hyperbolicity of the push-out** (`BTZ_1.tex:1098–1102`), in
open-set form. -/
theorem globallyHyperbolic_of_twoOpens (h : C.SingularFlatAxioms sing) {A B : Opens X}
    (hsA : sing 0 ⊆ A) (hBc : (B : Set X)ᶜ ⊆ sing 0) (hGA : C.GloballyHyperbolicOn A)
    (hGB : C.GloballyHyperbolicOn B)
    (hmix : ∀ p ∈ sing 0, ∀ q ∉ sing 0, IsCompact (C.diamond ⊤ p q)) : C.GloballyHyperbolic :=
  ⟨isCausal_of_twoOpens h hsA hBc hGA hGB, isCompact_diamond_of_twoOpens h hsA hBc hGA hGB hmix⟩

/-- **The regular part of a globally hyperbolic `𝔼≥0`-spacetime is globally hyperbolic** (first
assertion of B21 Prop 2.17, its GH part, open-set form): `Reg = sing₀ᶜ` is causally convex
(`causallyConvexIn_reg`), and Remark 1 applies. -/
theorem globallyHyperbolicOn_reg (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic)
    {R : Opens X} (hR : (R : Set X) = (sing 0)ᶜ) : C.GloballyHyperbolicOn R :=
  globallyHyperbolicOn_of_causallyConvexIn hG h.causallyArcConnected (hR ▸ causallyConvexIn_reg h)

/-- **The regular points near a BTZ point `z` above `p` on its line are in `I⁺(p)`** (B21
l.1352–1355, `Iplus_of_lt`, in neighbourhood form): `SingularPastAt` at `z` gives `u ≤ z` on the
line, `p ≤ u ≠ p`, with `z ∈ Int J⁺(u)`. -/
theorem exists_nhds_diff_sing_subset_Iplus (h : C.SingularFlatAxioms sing) {p z : X}
    (hp : p ∈ sing 0) (hz : z ∈ sing 0) (hpz : C.le ⊤ p z) (hne : p ≠ z) :
    ∃ V ∈ 𝓝 z, V \ sing 0 ⊆ C.Iplus ⊤ {p} := by
  haveI := h.t2
  obtain ⟨u, hu, hmono, hint, h0⟩ := (h.singularPastAt z hz).2 p hpz hne
  have hpu : C.le ⊤ p (u 0) :=
    Causal.Precausality.mem_Jminus_singleton.1 (Causal.interiorWithin_subset h0)
  obtain ⟨n, hn⟩ := (hu.eventually (isOpen_compl_singleton.mem_nhds hne.symm)).exists
  have hpn : C.le ⊤ p (u n) := C.le_trans hpu (hmono 0 n (Nat.zero_le n))
  have hnz : C.le ⊤ (u n) z :=
    Causal.Precausality.mem_Jplus_singleton.1 (interior_subset (hint n))
  have hns : u n ∈ sing 0 := h.mem_sing_zero_of_le hz hnz
  refine ⟨interior (C.Jplus ⊤ {u n}), isOpen_interior.mem_nhds (hint n), ?_⟩
  rintro x ⟨hx, hxs⟩
  exact h.Iplus_of_lt p hp (u n) hns hpn (fun e => hn e.symm) ⟨interior_subset hx, hxs⟩

/-- **A chronological relation from a regular point holds inside the regular part** (a chronal
curve from a regular point stays regular: `I⁺` avoids `sing₀`). -/
theorem lt_reg_of_lt (h : C.SingularFlatAxioms sing) {R : Opens X} (hR : (R : Set X) = (sing 0)ᶜ)
    {x y : X} (hx : x ∉ sing 0) (hxy : C.lt ⊤ x y) : C.lt R x y := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (h.causallyArcConnected ⊤ le_rfl x y).2.1 hxy
  have hγR : ∀ σ ∈ Icc (0 : ℝ) 1, γ σ ∈ R := by
    intro σ hσ
    rw [← SetLike.mem_coe, hR]
    rcases hσ.1.eq_or_lt with e | e
    · rw [← e, hγ0]; exact hx
    · have hl := hγ.lt_of_lt le_rfl e hσ.2
      rw [hγ0] at hl
      exact notMem_sing_of_lt h hl
  have hγ' : C.ChronalCurveOn R γ 0 1 := Causal.CurveOn.restrict hγ le_rfl le_rfl le_top hγR
  have := hγ'.lt_of_lt le_rfl zero_lt_one le_rfl
  rwa [hγ0, hγ1] at this

/-- **What a closed BTZ loop gives order-theoretically** (WP-44f; the part of B21 l.1035–1036
that `SingularFlatAxioms` does carry): if `x ≤ y ≤ x` for BTZ points `x ≠ y`, a neighbourhood
of `x` has ALL its regular points in `I⁺(x)` — those below `x` in a chart included (the loop
comes back from below). `exists_nhds_diff_sing_subset_Iplus` at `y < x` puts them in `I⁺(y)`,
and `Iplus_of_lt` at `x < y` moves them to `I⁺(x)`. What it does not give is a relation between
two REGULAR points near the loop (regular points never precede BTZ points), which is what strong
causality of `A` needs to be contradicted: that is the tube of the paper, built for
`𝔼₀`-manifolds in §2b (`shadowRel_of_curve`, `sing_eq_of_le_of_le_of_stronglyCausalOn_e0`). -/
theorem exists_nhds_diff_sing_subset_Iplus_self_of_loop (h : C.SingularFlatAxioms sing)
    {x y : X} (hx : x ∈ sing 0) (hy : y ∈ sing 0) (hxy : C.le ⊤ x y) (hyx : C.le ⊤ y x)
    (hne : x ≠ y) : ∃ V ∈ 𝓝 x, V \ sing 0 ⊆ C.Iplus ⊤ {x} := by
  obtain ⟨V, hV, hVs⟩ := exists_nhds_diff_sing_subset_Iplus h hy hx hyx (Ne.symm hne)
  refine ⟨V, hV, fun w hw => ?_⟩
  have hyw : C.lt ⊤ y w := Causal.Precausality.mem_Iplus_singleton.1 (hVs hw)
  exact h.Iplus_of_lt x hx y hy hxy hne
    ⟨Causal.Precausality.mem_Jplus_singleton.2 (C.le_of_lt hyw), hw.2⟩

end SFA

/-! ### §2b `𝔼₀`-manifolds: the closed BTZ loop of B21 Lemma 2.14 (WP-47f fixer, DEC-126)

B21's proof (`BTZ_1.tex:1035–1036`): « from a finite covering of `c` by charts and using
Lemma `prop:isom`, one can construct a neighborhood `𝒰` of `c` isomorphic to
`⟨γ⟩\{r < r*}`, `γ : (τ, r, θ) ↦ (τ + τ₀, r, θ + θ₀)` […] the future causal curve
`t ↦ (t, r₁, θ₁)` is in `ι(M₀)` and is either closed or passes infinitely many times in any
neighborhood of any of its points ». Built here in four steps, none assuming the tube.

* **`prop:isom` near the axis** (`e0Loop_localForm`): every element of `G = e0Groupoid` reads,
  on a ball around an axis point, `(τ, z) ↦ (τ + a, R z)` with `R` a linear isometry of `ℂ`.
  Rigid's local core (copied as `e0Loop_core_of_region` to export the axis-preserving isometry
  `F`, `F P = Pᵏ F`, `k² = 1`), then **`λ = 1`** (`e0Loop_lam_eq_one`: the angle of `D⁻¹ F D` is
  `λ(ν + κθ)` with `κ² = 1` by the null form, and one turn gives `λκ = k`), then the paper's
  coordinates (`e0Loop_paper_form`) and rigidity of `G` (`e0_rigid`).
* **The shadow relation** `ShadowRel a b` between BTZ points: the horizontal disc of the preferred
  chart at `a` precedes, point by point up to an isometry `R`, the one at `b`. It is reflexive,
  transitive, holds along a short rising piece of the axis of one chart (vertical lines are null,
  `chart_le_vertical`; transitions at axis points, `exists_transition_axis`), hence along every
  BTZ causal curve (`shadowRel_of_curve`, a supremum argument on the parameter): this replaces
  the paper's « finite covering of `c` by charts ».
* **Return of the shadow** (`exists_iterate_near`): the iterates of an isometry of `ℂ` return
  arbitrarily close to their start (the rotation case `θ₀ ∉ ℚπ` of the paper, and its closed
  case; a reflection returns after two turns).
* **The contradiction** (`sing_eq_of_le_of_le_of_stronglyCausalOn_e0`, in §3): a regular `p` near
  `x` precedes a point `q` of its shadow near `y`, which precedes points of `p`'s shadow back near
  `x` arbitrarily close to `p`; causal convexity in `A` of a small neighbourhood of `p` would put
  `q` near `x`. -/

section LoopModel

open scoped Real

attribute [local instance] btzE0Structure


/-- **The local core of B21 `prop:isom_strong` with its automorphism made explicit** (WP-47f
fixer; `GX.btzE0_localUnique_core_of_region`'s proof verbatim, its conclusion extended by the
axis-preserving isometry `Fa`, the conjugation `Fa P = Pᵏ Fa`, `k² = 1` and `ψ = D⁻¹ Fa D`, all
of which that proof constructs and does not export). -/
theorem e0Loop_core_of_region {B : Set (ℂ × ℝ)} (hBo : IsOpen B) (hBc : Convex ℝ B)
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
    ∃ (Ψ : BTZE0 ≃ₜ BTZE0) (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (g : Causal.Flat.isom 2)
      (Fa : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (lam s₀ : ℝ) (kk : ℤ),
      IsAxisAff Fa lam s₀ ∧ Fa * btzParab = btzParab ^ kk * Fa ∧ kk * kk = 1 ∧
      (∀ y, ψ y = btzConj Fa y) ∧
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
  refine ⟨btzE0Descend ψ h₁ h₂, ψ, g, Fg, lam, s₀, k.toInt, hax, hc, hk1, fun y => rfl,
    fun y => rfl, hax.mem_cylPos_iff, fun y _ => ?_,
    orbitMk (GammaA (2 * π)) '' range σ, isOpenMap_quotient_mk'_mul _ hσemb.isOpen_range,
    ⟨_, ⟨σ a₀, ⟨a₀, rfl⟩, rfl⟩⟩, ?_, ?_⟩
  · show btzDevM 0 btzV0 (btzConj Fg y) = g • btzDevM 0 btzV0 y
    rw [btzDevM, btzDevM, hax.btzDev_btzConj, ← hgF, ← nullToMink_smul]; rfl
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩; exact hσU a
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [hFσ]; rfl


/-- The angle of `D⁻¹ F D` at a regular point, for an axis-preserving `F`: `λ (ν + κθ)` with
`κ = (F.linear e_c)_c` and `ν = (F.linear e_b)_c`. -/
theorem e0Loop_theta_btzConj {Fa : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ}
    (hax : IsAxisAff Fa lam s₀) (y : DInfty × ℝ) (hy : 0 < y.1.r) :
    (btzConj Fa y).1.θ = lam * ((Fa.linear ((0 : ℝ), (1 : ℝ), (0 : ℝ))).2.2 +
      y.1.θ * (Fa.linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.2) := by
  have hm := (hax.image_mem y).1 hy
  set w := btzDev 0 btzV0 y with hw
  have hdec : w = w.1 • nullU + w.2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
      w.2.2 • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [nullU]
  have hFw : Fa w = Fa.linear w + s₀ • nullU := hax.apply w
  have hc : (Fa w).2.2 = w.2.1 * (Fa.linear ((0 : ℝ), (1 : ℝ), (0 : ℝ))).2.2 +
      w.2.2 * (Fa.linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.2 := by
    rw [hFw]
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul, hax.linear_nullU]
    simp [nullU]
  have hb : lam * (Fa w).2.1 = w.2.1 := by
    have := hax.b_linear w
    rw [hFw]; simpa [nullU] using this
  have hwb : w.2.1 = y.1.r := btzDev_e0_b y
  have hwc : w.2.2 = y.1.r * y.1.θ := by rw [hw, btzDev_e0_apply]
  rw [btzConj, btzDevInv, dif_pos hm]
  simp only [DInfty.posEmb_θ]
  have hl := hax.pos
  have hb0 : (Fa w).2.1 ≠ 0 := hm.ne'
  rw [hc, hwb, hwc]
  have hFb : (Fa w).2.1 = y.1.r / lam := by
    field_simp; rw [mul_comm]; linarith [hb, hwb]
  rw [hFb]
  field_simp

/-- **An automorphism of `𝔼₀` has no boost along the axis** (WP-47f): for an axis-preserving
`F` with `F P = Pᵏ F` and `k² = 1`, `λ = 1`, and the angle of `D⁻¹ F D` is `kθ + ν`. -/
theorem e0Loop_lam_eq_one {Fa : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} {kk : ℤ}
    (hax : IsAxisAff Fa lam s₀) (hc : Fa * btzParab = btzParab ^ kk * Fa) (hk : kk * kk = 1) :
    lam = 1 ∧ ∃ ν : ℝ, ∀ y : DInfty × ℝ, 0 < y.1.r → (btzConj Fa y).1.θ = kk * y.1.θ + ν := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hl := hax.pos
  set κ := (Fa.linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.2 with hκ
  set ν := (Fa.linear ((0 : ℝ), (1 : ℝ), (0 : ℝ))).2.2 with hν
  -- `(L e_c)_b = 0` and `κ² = 1`
  have hβ : (Fa.linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.1 = 0 := by
    have := hax.b_linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))
    simp only at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hl.ne'
    · exact h
  have hκ2 : κ ^ 2 = 1 := by
    have := hax.Q_linear ((0 : ℝ), (0 : ℝ), (1 : ℝ))
    simp only [nullQ, hβ, mul_zero, sub_zero] at this
    rw [hκ]; simpa using this
  -- the deck relation on one regular point
  set y₀ : DInfty × ℝ := (DInfty.posEmb ⟨((1 : ℝ), (0 : ℝ)), one_pos⟩, 0) with hy₀
  have hr0 : 0 < y₀.1.r := by simp [hy₀]
  have h1 := hax.btzConj_smul hc (GammaA.ofInt 1) y₀
  have hθs : ∀ (j : ℤ) (z : DInfty × ℝ), 0 < z.1.r →
      ((GammaA.ofInt j : GammaA (2 * π)) • z).1.θ = z.1.θ + j * (2 * π) := by
    intro j z hz
    rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_of_pos hz, GammaA.toInt_ofInt]
  have hrs : ∀ (j : ℤ) (z : DInfty × ℝ), ((GammaA.ofInt j : GammaA (2 * π)) • z).1.r = z.1.r := by
    intro j z
    rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_r]
  have hθ1 := congrArg (fun z : DInfty × ℝ => z.1.θ) h1
  have hr1 : 0 < ((GammaA.ofInt 1 : GammaA (2 * π)) • y₀).1.r := by rw [hrs]; exact hr0
  have hr2 : 0 < (btzConj Fa y₀).1.r := by rw [hax.r_btzConj]; exact div_pos hr0 hl
  rw [e0Loop_theta_btzConj hax _ hr1, hθs _ _ hr2, e0Loop_theta_btzConj hax _ hr0,
    hθs _ _ hr0, GammaA.toInt_ofInt, mul_one] at hθ1
  have hlk : lam * κ = kk := by
    have : lam * κ * (2 * π) = kk * (2 * π) := by
      push_cast at hθ1 ⊢; linear_combination hθ1
    exact mul_right_cancel₀ (by positivity) this
  have hkk : ((kk : ℝ)) ^ 2 = 1 := by
    have : ((kk * kk : ℤ) : ℝ) = 1 := by rw [hk]; simp
    push_cast at this; nlinarith
  have hlam : lam = 1 := by
    have : lam ^ 2 = 1 := by
      have : (lam * κ) ^ 2 = 1 := by rw [hlk]; exact hkk
      rw [mul_pow, hκ2, mul_one] at this; exact this
    nlinarith
  refine ⟨hlam, ν, fun y hy => ?_⟩
  rw [e0Loop_theta_btzConj hax y hy, hlam, ← hlk, hlam]
  ring

theorem e0Loop_toPaper_mk (y : DInfty × ℝ) :
    E0.toPaper (orbitMk (GammaA (2 * π)) y) =
      (y.2 / 2, (starRingEnd ℂ) (DInfty.cplx (2 * π) y.1)) := by
  show E0.paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _) = _
  rw [cylHomeomorph_apply]; rfl

/-- **An automorphism of `𝔼₀`, in the paper's coordinates** (WP-47f): `D⁻¹ F D` descends to
`(τ, z) ↦ (τ + s₀/2, R z)` for a linear isometry `R` of `ℂ` (a rotation, or a rotation after
`z ↦ z̄`), by `λ = 1` (`e0Loop_lam_eq_one`). -/
theorem e0Loop_paper_form {Fa : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)} {lam s₀ : ℝ} {kk : ℤ}
    (hax : IsAxisAff Fa lam s₀) (hc : Fa * btzParab = btzParab ^ kk * Fa) (hk : kk * kk = 1) :
    ∃ R : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ y : DInfty × ℝ,
      E0.toPaper (orbitMk (GammaA (2 * π)) (btzConj Fa y)) =
        ((E0.toPaper (orbitMk (GammaA (2 * π)) y)).1 + s₀ / 2,
          R (E0.toPaper (orbitMk (GammaA (2 * π)) y)).2) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨hlam, ν, hθ⟩ := e0Loop_lam_eq_one hax hc hk
  have hk' : kk = 1 ∨ kk = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hk with h | h <;> simp [h]
  set a : Circle := Circle.exp (-ν) with ha
  set R : ℂ ≃ₗᵢ[ℝ] ℂ := if kk = 1 then rotation a else Complex.conjLIE.trans (rotation a) with hR
  refine ⟨R, fun y => ?_⟩
  rw [e0Loop_toPaper_mk, e0Loop_toPaper_mk]
  have hr : (btzConj Fa y).1.r = y.1.r := by rw [hax.r_btzConj, hlam, div_one]
  have ht : (btzConj Fa y).2 = y.2 + s₀ := by rw [hax.t_btzConj, hlam]; ring
  refine Prod.ext ?_ ?_
  · simp only; rw [ht]; ring
  · simp only
    rcases y.1.pos_or_eq_apex with hy | hy
    · have hθy := hθ y hy
      simp only [DInfty.cplx, hr, hθy]
      have e2 : 2 * π / (2 * π) = (1 : ℝ) := by field_simp
      rw [e2, one_mul, one_mul]
      rcases hk' with h1 | h1
      · have hRa : ∀ z, R z = a * z := fun z => by rw [hR, if_pos h1, rotation_apply]
        rw [hRa, h1, ha, Circle.coe_exp]
        simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
        push_cast
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2; ring
      · have hRa : ∀ z, R z = a * (starRingEnd ℂ) z := fun z => by
          rw [hR, if_neg (by rw [h1]; decide), LinearIsometryEquiv.trans_apply, rotation_apply,
            Complex.conjLIE_apply]
        rw [hRa, h1, ha, Circle.coe_exp]
        simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
        push_cast
        ring_nf
        simp only [map_neg, Complex.conj_I, neg_neg]
        rw [mul_assoc, ← Complex.exp_add]
        congr 2; ring
    · have hb : (btzConj Fa y).1 = DInfty.apex := by
        refine DInfty.eq_apex_of_not_pos ?_
        rw [hr, hy, DInfty.apex_r]; exact lt_irrefl 0
      rw [hb, hy, DInfty.cplx_apex, map_zero, map_zero]


/-- **Every element of `G` is, near an axis point, an automorphism of `𝔼₀` in the paper's form**
`(τ, z) ↦ (τ + a, R z)`, `R` a linear isometry of `ℂ` (WP-47f; B21 `prop:isom` read near the
axis): Rigid's local core (`e0Loop_core_of_region`), `λ = 1` (`e0Loop_paper_form`), and the
rigidity of `G` (`e0_rigid`) on a ball. -/
theorem e0Loop_localForm {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) {τ₀ : ℝ}
    (h0 : E0.paperInY ((τ₀, 0) : E0) ∈ e.source) :
    ∃ δ > 0, ∃ a : ℝ, ∃ R : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ u : E0, dist u (τ₀, 0) < δ →
      E0.paperInY u ∈ e.source ∧ e (E0.paperInY u) = E0.paperInY (u.1 + a, R u.2) := by
  set y₀ : E0Y := E0.paperInY ((τ₀, 0) : E0) with hy₀
  have hy₀s : y₀ ∈ e0SingY 0 :=
    E0LM.mem_e0SingY_zero_iff.2 ⟨_, rfl, by simp [E0.axis]⟩
  have hey₀ : e y₀ ∈ range (Sum.inr : BTZE0 → E0Y) := by
    obtain ⟨x, hx, -⟩ := E0LM.mem_e0SingY_zero_iff.1 ((e0_sing_mem e he y₀ h0 0 le_rfl).1 hy₀s)
    exact ⟨x, hx.symm⟩
  -- a ball of the paper coordinates inside `e.source ∩ e⁻¹(range inr)`
  have hO : IsOpen (e.source ∩ e ⁻¹' range (Sum.inr : BTZE0 → E0Y)) :=
    e.isOpen_inter_preimage isOpen_range_inr
  have hN : E0.paperInY ⁻¹' (e.source ∩ e ⁻¹' range (Sum.inr : BTZE0 → E0Y)) ∈
      𝓝 ((τ₀, 0) : E0) :=
    E0Spear.continuous_paperInY.continuousAt.preimage_mem_nhds (hO.mem_nhds ⟨h0, hey₀⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hN
  set U : Set E0Y := E0.paperInY '' Metric.ball ((τ₀, 0) : E0) δ with hUdef
  have hUo : IsOpen U := E0Spear.isOpen_paperInY_image Metric.isOpen_ball
  have hUc : IsPreconnected U :=
    (Metric.isConnected_ball hδ).isPreconnected.image _ E0Spear.continuous_paperInY.continuousOn
  have hUO : U ⊆ e.source ∩ e ⁻¹' range (Sum.inr : BTZE0 → E0Y) := by
    rintro _ ⟨u, hu, rfl⟩; exact hball hu
  have hUr : U ⊆ range (Sum.inr : BTZE0 → E0Y) := by
    rintro _ ⟨u, -, rfl⟩; exact ⟨_, rfl⟩
  -- the map read on `𝔼₀`
  set U' : Set BTZE0 := Sum.inr ⁻¹' U with hU'
  have hU'o : IsOpen U' := hUo.preimage continuous_inr
  set F : BTZE0 → BTZE0 := fun x => e0Inr.symm (e (Sum.inr x)) with hFdef
  have hfF : ∀ x ∈ U', e (Sum.inr x) = Sum.inr (F x) := fun x hx => by
    obtain ⟨z, hz⟩ := (hUO hx).2
    simp only [F, ← hz, e0Inr_symm_inr]
  have hFc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ContinuousAt F x := by
    rintro x ⟨hx, -⟩
    have hxe : Sum.inr x ∈ e.source := (hUO hx).1
    have h1 : ContinuousAt e0Inr.symm (e (Sum.inr x)) :=
      e0Inr.symm.continuousAt (by rw [e0Inr_symm_source, hfF x hx]; exact ⟨_, rfl⟩)
    exact ContinuousAt.comp (g := e0Inr.symm) (f := fun x : BTZE0 => e (Sum.inr x)) h1
      (ContinuousAt.comp (g := e) (f := Sum.inr) (e.continuousAt hxe) continuous_inr.continuousAt)
  have hFreg : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rintro x ⟨hx, hxr⟩
    have := mapsTo_e0Reg_of_mem he (hUO hx).1 (inr_mem_e0Reg_iff.2 hxr)
    rw [hfF x hx] at this
    exact inr_mem_e0Reg_iff.1 this
  have hFloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z := by
    rintro x ⟨hx, hxr⟩
    have hxe : Sum.inr x ∈ e.source := (hUO hx).1
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
    obtain ⟨c', hc', hFxc⟩ := mem_support.1 (hFreg x ⟨hx, hxr⟩)
    have hex : e (Sum.inr x) = Sum.inr (F x) := hfF x hx
    obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hxe).2 (inr_mem_e0Reg_iff.2 hxr)
    obtain ⟨h, hh⟩ := hch _ (e0InrChart_mem_e0Atlas hc) _ (e0InrChart_mem_e0Atlas hc')
      (mem_e0InrChart_source.2 ⟨x, hxc, rfl⟩)
      (by rw [hex]; exact mem_e0InrChart_source.2 ⟨_, hFxc, rfl⟩)
    refine ⟨c, hc, hxc, c', hc', hFxc, h, ?_⟩
    have hS' : U' ∈ 𝓝 x := hU'o.mem_nhds hx
    filter_upwards [continuous_inr.continuousAt.eventually hh, hS'] with z hz hzS
    rw [hfF z hzS, e0InrChart_inr, e0InrChart_inr] at hz
    exact hz
  have hFinj : InjOn F (U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) := by
    rintro x ⟨hx, -⟩ x' ⟨hx', -⟩ hxx'
    have := e.injOn (hUO hx).1 (hUO hx').1
      (by rw [hfF x hx, hfF x' hx', show F x = F x' from hxx'])
    exact Sum.inr_injective this
  -- the box around the axis point, and the explicit automorphism
  set x₀ : BTZE0 := E0.toPaper.symm ((τ₀, 0) : E0) with hx₀
  have hx₀r : x₀ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := fun h =>
    hy₀s.2 (inr_mem_e0Reg_iff.2 h)
  have hx₀U : x₀ ∈ U' := ⟨(τ₀, 0), Metric.mem_ball_self hδ, rfl⟩
  obtain ⟨t₀, ε₁, ε₂, hε₁, hε₂, hbox⟩ := btzE0_exists_box hx₀r hU'o hx₀U
  obtain ⟨Ψ, ψ, g, Fa, lam, s₀, kk, hax, hc, hk, hψ, hlift, hpos, hD, W, hWo, hWne, hWU,
      hWeq⟩ := e0Loop_core_of_region (isOpen_e0Box (Real.log ε₁) t₀ ε₂) (convex_e0Box _ _ _)
    ⟨(((Real.log ε₁ - 1 : ℝ) : ℂ), t₀), by simp [e0Box, hε₂]⟩ (fun w hw s => mem_e0Box_add hw s)
    (fun w hw => hbox _ ((Real.lt_log_iff_exp_lt hε₁).1 hw.1) hw.2) hFc hFreg hFloc hFinj
  have he' := e0Lift_mem Ψ ψ g hlift hpos hD
  have hrig : EqOn e (e0Lift Ψ) U := by
    refine e0_rigid e he _ he' U hUo hUc (fun y hy => (hUO hy).1)
      (by rw [e0Lift_source]; exact hUr) (Sum.inr '' W) ?_ (isOpenMap_inr _ hWo)
      (hWne.image _) ?_
    · rintro _ ⟨w, hw, rfl⟩; exact (hWU hw).1
    · rintro _ ⟨w, hw, rfl⟩
      rw [hfF w (hWU hw).1, e0Lift_apply, hWeq hw]
  obtain ⟨R, hR⟩ := e0Loop_paper_form hax hc hk
  refine ⟨δ, hδ, s₀ / 2, R, fun u hu => ⟨(hball hu).1, ?_⟩⟩
  have huU : E0.paperInY u ∈ U := ⟨u, hu, rfl⟩
  rw [hrig huU]
  obtain ⟨y, hy⟩ := Quotient.exists_rep (E0.toPaper.symm u)
  have hy' : orbitMk (GammaA (2 * π)) y = E0.toPaper.symm u := hy
  have hu' : E0.toPaper (orbitMk (GammaA (2 * π)) y) = u := by rw [hy']; simp
  rw [E0.paperInY_apply, E0.paperInY_apply, e0Lift_apply, ← hy', hlift, hψ]
  congr 1
  apply E0.toPaper.injective
  rw [Homeomorph.apply_symm_apply, hR, hu']

end LoopModel

/-! ### The closed BTZ loop of B21 Lemma 2.14 in an `𝔼₀`-manifold: the shadow of the loop -/

section LoopManifold

open E0CBG E0Spear

/-- A causal relation from a regular point is realised inside any open `A ⊇ Reg` (a causal curve
from a regular point stays regular: BTZ points are preceded only by BTZ points). -/
theorem le_of_le_of_notMem_sing {X : Type*} [TopologicalSpace X] {C : Causal.Causality X}
    {sing : ℝ → Set X} (h : C.SingularFlatAxioms sing) {A : Opens X} (hA : (A : Set X)ᶜ ⊆ sing 0)
    {x y : X} (hx : x ∉ sing 0) (hxy : C.le ⊤ x y) : C.le A x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := (h.causallyArcConnected ⊤ le_rfl x y).1.1 hxy
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ A := fun s hs => by
    by_contra hcs
    have h1 : C.le ⊤ x (c s) := by rw [← hc0]; exact hc.le_of_le le_rfl hs.1 hs.2
    exact hx (h.mem_sing_zero_of_le (hA hcs) h1)
  exact (h.causallyArcConnected A le_top x y).1.2
    ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

/-- **Pigeonhole on a circle** (WP-47f): the iterates of a linear isometry `R` of `ℂ` come back
arbitrarily close to their starting point (the orbit lies in a compact disc, and `R` is an
isometry). -/
theorem exists_iterate_near (R : ℂ ≃ₗᵢ[ℝ] ℂ) (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 ≤ n ∧ ‖(⇑R)^[n] z - z‖ < δ := by
  have hnorm : ∀ n : ℕ, ‖(⇑R)^[n] z‖ = ‖z‖ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]
  have hdist : ∀ (n : ℕ) (a b : ℂ), dist ((⇑R)^[n] a) ((⇑R)^[n] b) = dist a b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
      intro a b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', R.isometry.dist_eq, ih]
  have hmem : ∀ n : ℕ, (⇑R)^[n] z ∈ Metric.closedBall (0 : ℂ) ‖z‖ := fun n => by
    rw [mem_closedBall_zero_iff, hnorm]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) ‖z‖).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (δ / 2) (by linarith)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  simp only [comp_apply] at h1 h2
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, by omega, ?_⟩
  have e : (⇑R)^[φ (N + 1)] z = (⇑R)^[φ N] ((⇑R)^[φ (N + 1) - φ N] z) := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [← dist_eq_norm, ← hdist (φ N), ← e]
  calc dist ((⇑R)^[φ (N + 1)] z) ((⇑R)^[φ N] z)
      ≤ dist ((⇑R)^[φ (N + 1)] z) a + dist a ((⇑R)^[φ N] z) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by rw [dist_comm a]; exact add_lt_add h2 h1
    _ = δ := by ring

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The BTZ locus read in any chart of the atlas. -/
theorem chart_mem_e0SingY_iff (w : M) {q : M} (hq : q ∈ (chartAt E0Y w).source) :
    chartAt E0Y w q ∈ e0SingY 0 ↔ q ∈ S0 M := by
  have he : (chartAt E0Y w).symm.trans (chartAt E0Y q) ∈ e0Groupoid :=
    e0Groupoid.compatible (chart_mem_atlas E0Y w) (chart_mem_atlas E0Y q)
  have hmem : chartAt E0Y w q ∈ ((chartAt E0Y w).symm.trans (chartAt E0Y q)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source]
    exact ⟨(chartAt E0Y w).map_source hq, by
      rw [(chartAt E0Y w).left_inv hq]; exact mem_chart_source E0Y q⟩
  have h := e0_sing_mem _ he _ hmem 0 le_rfl
  have h2 : ((chartAt E0Y w).symm.trans (chartAt E0Y q)) (chartAt E0Y w q) = chartAt E0Y q q := by
    simp [(chartAt E0Y w).left_inv hq]
  rw [h2] at h
  exact h

/-- A point of `Y` in `e0SingY 0` which is `paperInY u` has `u` on the axis. -/
theorem e0Loop_paperInY_mem_sing_iff (u : E0) : E0.paperInY u ∈ e0SingY 0 ↔ u.2 = 0 := by
  rw [E0LM.mem_e0SingY_zero_iff]
  constructor
  · rintro ⟨x, hx, hax⟩
    rw [E0.paperInY_apply] at hx
    have := Sum.inr_injective hx
    rw [← this] at hax
    simpa [E0.axis] using hax
  · intro h
    exact ⟨_, rfl, by simpa [E0.axis] using h⟩

omit [HasGroupoid M e0Groupoid] in
/-- The preferred chart of a BTZ point sends it to the axis. -/
theorem exists_chart_axis {a : M} (ha : a ∈ S0 M) :
    ∃ τ : ℝ, chartAt E0Y a a = E0.paperInY ((τ, 0) : E0) := by
  obtain ⟨x, hx, hax⟩ := E0LM.mem_e0SingY_zero_iff.1 (show chartAt E0Y a a ∈ e0SingY 0 from ha)
  refine ⟨(E0.toPaper x).1, ?_⟩
  rw [hx, E0.paperInY_apply]
  congr 1
  apply E0.toPaper.injective
  rw [Homeomorph.apply_symm_apply]
  exact Prod.ext rfl hax

/-- **The shadow relation between two BTZ points** (WP-47f): the horizontal disc of the preferred
chart at `a` is causally below, point by point up to a linear isometry `R` of `ℂ`, the horizontal
disc of the preferred chart at `b` — the regular points `κ_a⁻¹(τ_a, z)` near `a` precede the
points `κ_b⁻¹(τ_b, R z)` near `b`. -/
def ShadowRel (a b : M) : Prop :=
  ∃ (τa τb ρ : ℝ) (R : ℂ ≃ₗᵢ[ℝ] ℂ), 0 < ρ ∧ chartAt E0Y a a = E0.paperInY ((τa, 0) : E0) ∧
    chartAt E0Y b b = E0.paperInY ((τb, 0) : E0) ∧ ∀ z : ℂ, ‖z‖ < ρ →
      (CE M).le ⊤ ((chartAt E0Y a).symm (E0.paperInY (τa, z)))
        ((chartAt E0Y b).symm (E0.paperInY (τb, R z)))

theorem paperInY_axis_injective {τ τ' : ℝ}
    (h : E0.paperInY ((τ, 0) : E0) = E0.paperInY ((τ', 0) : E0)) : τ = τ' := by
  rw [E0.paperInY_apply, E0.paperInY_apply] at h
  have := E0.toPaper.symm.injective (Sum.inr_injective h)
  exact congrArg Prod.fst this

omit [HasGroupoid M e0Groupoid] in
theorem shadowRel_refl {a : M} (ha : a ∈ S0 M) : ShadowRel a a := by
  obtain ⟨τ, hτ⟩ := exists_chart_axis ha
  exact ⟨τ, τ, 1, LinearIsometryEquiv.refl ℝ ℂ, one_pos, hτ, hτ, fun z _ =>
    (CE M).le_refl trivial⟩

omit [HasGroupoid M e0Groupoid] in
theorem ShadowRel.trans {a b c : M} (h₁ : ShadowRel a b) (h₂ : ShadowRel b c) :
    ShadowRel a c := by
  obtain ⟨τa, τb, ρ₁, R₁, hρ₁, ha, hb, h1⟩ := h₁
  obtain ⟨τb', τc, ρ₂, R₂, hρ₂, hb', hc, h2⟩ := h₂
  have e : τb' = τb := paperInY_axis_injective (hb'.symm.trans hb)
  subst e
  refine ⟨τa, τc, min ρ₁ ρ₂, R₁.trans R₂, lt_min hρ₁ hρ₂, ha, hc, fun z hz => ?_⟩
  have hz1 : ‖z‖ < ρ₁ := hz.trans_le (min_le_left _ _)
  have hz2 : ‖R₁ z‖ < ρ₂ := by rw [LinearIsometryEquiv.norm_map]; exact hz.trans_le (min_le_right _ _)
  exact (CE M).le_trans (h1 z hz1) (h2 _ hz2)

/-- **Transition at an axis point** (WP-47f): read in the chart `κ` at `w`, the horizontal disc
through the BTZ point `w₁` is the horizontal disc of `w₁`'s own chart, up to a linear isometry of
`ℂ` (`e0Loop_localForm` applied to the transition `κ⁻¹ ≫ κ₁ ∈ G`). -/
theorem exists_transition_axis (w : M) {w₁ : M} (hw₁ : w₁ ∈ (chartAt E0Y w).source) {τ₁ v₁ : ℝ}
    (h₁ : chartAt E0Y w w₁ = E0.paperInY ((τ₁, 0) : E0))
    (hv₁ : chartAt E0Y w₁ w₁ = E0.paperInY ((v₁, 0) : E0)) :
    ∃ ρ > 0, ∃ R : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, ‖z‖ < ρ →
      E0.paperInY (τ₁, z) ∈ (chartAt E0Y w).target ∧
      (chartAt E0Y w).symm (E0.paperInY (τ₁, z)) =
        (chartAt E0Y w₁).symm (E0.paperInY (v₁, R z)) := by
  set κ := chartAt E0Y w
  set κ₁ := chartAt E0Y w₁
  have he : κ.symm.trans κ₁ ∈ e0Groupoid :=
    e0Groupoid.compatible (chart_mem_atlas E0Y w) (chart_mem_atlas E0Y w₁)
  have h0 : E0.paperInY ((τ₁, 0) : E0) ∈ (κ.symm.trans κ₁).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source]
    rw [← h₁]
    exact ⟨κ.map_source hw₁, by rw [κ.left_inv hw₁]; exact mem_chart_source E0Y w₁⟩
  obtain ⟨δ, hδ, a, R, hR⟩ := e0Loop_localForm he h0
  have hτ : τ₁ + a = v₁ := by
    have := (hR (τ₁, 0) (by simp [hδ])).2
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply] at this
    rw [← h₁, κ.left_inv hw₁, hv₁, map_zero] at this
    exact (paperInY_axis_injective this).symm
  refine ⟨δ, hδ, R, fun z hz => ?_⟩
  have hd : dist ((τ₁, z) : E0) (τ₁, 0) < δ := by
    rw [Prod.dist_eq, dist_self, dist_zero_right]; simpa using hz
  obtain ⟨hs, he'⟩ := hR _ hd
  simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.symm_source] at hs
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply, hτ] at he'
  refine ⟨hs.1, ?_⟩
  rw [← he', κ₁.left_inv hs.2]

/-- **Vertical lines of a chart are future causal in `M`.** -/
theorem chart_le_vertical (w : M) {τ τ' : ℝ} {z : ℂ} (h : τ ≤ τ')
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, E0.paperInY ((τ + s * (τ' - τ), z) : E0) ∈ (chartAt E0Y w).target) :
    (CE M).le ⊤ ((chartAt E0Y w).symm (E0.paperInY (τ, z)))
      ((chartAt E0Y w).symm (E0.paperInY (τ', z))) := by
  set U : Opens E0 := ⟨E0.paperInY ⁻¹' (chartAt E0Y w).target,
    (chartAt E0Y w).open_target.preimage continuous_paperInY⟩
  exact le_of_isE0Mor_paper (chartAt E0Y w).open_target (isE0Mor_chartAt_symm w)
    (U := U) subset_rfl (le_vertical h hseg)

/-- **The shadow propagates along a short piece of a BTZ causal curve** (WP-47f): around every
parameter `t`, the curve lies on the axis of one chart cylinder at `γ t`, rising (`chart_le_iff`,
`calculus_le`); the vertical lines of that chart carry the horizontal disc at `γ s₁` up to the one
at `γ s₂` (`chart_le_vertical`), and the two discs are the preferred ones up to isometries
(`exists_transition_axis`). -/
theorem shadowRel_local {γ : ℝ → M} (hγ : (CE M).CausalCurveOn ⊤ γ 0 1)
    (hS : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ S0 M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ l u, l < t ∧ t < u ∧ ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, l < s₁ → s₁ ≤ s₂ →
      s₂ < u → ShadowRel (γ s₁) (γ s₂) := by
  set w := γ t with hwdef
  set κ := chartAt E0Y w with hκ
  obtain ⟨v, hv⟩ := exists_chart_axis (hS t ht)
  have hT : IsOpen (E0.paperInY ⁻¹' κ.target) := κ.open_target.preimage continuous_paperInY
  have hvT : ((v, 0) : E0) ∈ E0.paperInY ⁻¹' κ.target := by
    show E0.paperInY (v, 0) ∈ κ.target
    rw [← hv]; exact κ.map_source (mem_chart_source E0Y w)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT _ hvT
  set ε := δ / 2 with hε
  have hεpos : 0 < ε := by linarith
  set A : Opens E0 := ⟨cyl (v - ε) (v + ε) ε, isOpen_cyl _ _ _⟩ with hAdef
  have hA : E0.paperInY '' (A : Set E0) ⊆ κ.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact hball (cyl_subset_ball (w := ((v, 0) : E0)) rfl (by linarith) hy)
  have hvA : ((v, 0) : E0) ∈ A := vertex_mem_cyl hεpos
  have hwN : w ∈ chartOpen w A := by
    have := mem_chartOpen hA hvA
    rwa [← hv, κ.left_inv (mem_chart_source E0Y w)] at this
  obtain ⟨l, u, hl, hu, hrel⟩ := hγ.rel t ht (chartOpen w A) le_top hwN
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, l < s → s < u → γ s ∈ chartOpen w A := by
    intro s hs hls hsu
    rcases lt_trichotomy s t with h | h | h
    · exact (CE M).le_mem_left (hrel s hs t ht hls h hu)
    · rw [h]; exact hwN
    · exact (CE M).le_mem_right (hrel t ht s hs hl h hsu)
  have hcoord : ∀ s ∈ Icc (0 : ℝ) 1, l < s → s < u → ∃ τs : ℝ, ((τs, 0) : E0) ∈ A ∧
      κ.symm (E0.paperInY (τs, 0)) = γ s ∧ κ (γ s) = E0.paperInY (τs, 0) := by
    intro s hs hls hsu
    have hN := hmem s hs hls hsu
    obtain ⟨ξ, hξA, hξ⟩ := exists_of_mem_chartOpen hN
    have hκγ : κ (γ s) = E0.paperInY ξ := by
      rw [← hξ, κ.right_inv (hA ⟨ξ, hξA, rfl⟩)]
    have hsing : E0.paperInY ξ ∈ e0SingY 0 := by
      rw [← hκγ]; exact (chart_mem_e0SingY_iff w hN.1).2 (hS s hs)
    have hξ2 : ξ.2 = 0 := (e0Loop_paperInY_mem_sing_iff ξ).1 hsing
    have hξe : ξ = (ξ.1, 0) := Prod.ext rfl hξ2
    refine ⟨ξ.1, ?_, ?_, ?_⟩
    · rw [← hξe]; exact hξA
    · rw [← hξe]; exact hξ
    · rw [← hξe]; exact hκγ
  refine ⟨l, u, hl, hu, fun s₁ hs₁ s₂ hs₂ hl₁ h12 hu₂ => ?_⟩
  rcases eq_or_lt_of_le h12 with h | h
  · rw [h]; exact shadowRel_refl (hS s₂ hs₂)
  obtain ⟨τ₁, hτ₁A, hτ₁, hκ₁⟩ := hcoord s₁ hs₁ hl₁ (h.trans hu₂)
  obtain ⟨τ₂, hτ₂A, hτ₂, hκ₂⟩ := hcoord s₂ hs₂ (hl₁.trans h) hu₂
  have hle := hrel s₁ hs₁ s₂ hs₂ hl₁ h hu₂
  rw [← hτ₁, ← hτ₂, chart_le_iff w hA hτ₁A hτ₂A] at hle
  have hτ12 : τ₁ ≤ τ₂ := (E0.calculus_le hle).2.2.1
  obtain ⟨v₁, hv₁⟩ := exists_chart_axis (hS s₁ hs₁)
  obtain ⟨v₂, hv₂⟩ := exists_chart_axis (hS s₂ hs₂)
  obtain ⟨ρ₁, hρ₁, R₁, hR₁⟩ := exists_transition_axis w (hmem s₁ hs₁ hl₁ (h.trans hu₂)).1 hκ₁ hv₁
  obtain ⟨ρ₂, hρ₂, R₂, hR₂⟩ := exists_transition_axis w (hmem s₂ hs₂ (hl₁.trans h) hu₂).1 hκ₂ hv₂
  refine ⟨v₁, v₂, min (min ρ₁ ρ₂) ε, R₁.symm.trans R₂,
    lt_min (lt_min hρ₁ hρ₂) hεpos, hv₁, hv₂, fun z₁ hz₁ => ?_⟩
  set z := R₁.symm z₁ with hz
  have hzn : ‖z‖ = ‖z₁‖ := LinearIsometryEquiv.norm_map _ _
  have hz1 : ‖z‖ < ρ₁ := by
    rw [hzn]; exact hz₁.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : ‖z‖ < ρ₂ := by
    rw [hzn]; exact hz₁.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hzε : ‖z‖ < ε := by rw [hzn]; exact hz₁.trans_le (min_le_right _ _)
  have e1 : (chartAt E0Y (γ s₁)).symm (E0.paperInY (v₁, z₁)) =
      κ.symm (E0.paperInY (τ₁, z)) := by
    rw [(hR₁ z hz1).2, hz, LinearIsometryEquiv.apply_symm_apply]
  have e2 : (chartAt E0Y (γ s₂)).symm (E0.paperInY (v₂, (R₁.symm.trans R₂) z₁)) =
      κ.symm (E0.paperInY (τ₂, z)) := by
    rw [(hR₂ z hz2).2, LinearIsometryEquiv.trans_apply]
  rw [e1, e2]
  refine chart_le_vertical w hτ12 fun s hs => hA ⟨_, ?_, rfl⟩
  have h1 := hτ₁A.1
  have h2 := hτ₂A.2.1
  have hs0 := hs.1
  have hs1 := hs.2
  refine ⟨?_, ?_, ?_⟩
  · show v - ε < τ₁ + s * (τ₂ - τ₁)
    have : 0 ≤ s * (τ₂ - τ₁) := mul_nonneg hs0 (by linarith)
    simp only at h1; linarith
  · show τ₁ + s * (τ₂ - τ₁) < v + ε
    have : s * (τ₂ - τ₁) ≤ 1 * (τ₂ - τ₁) := mul_le_mul_of_nonneg_right hs1 (by linarith)
    simp only at h2; linarith
  · show ‖z‖ < ε
    exact hzε

/-- **The shadow along a whole BTZ causal curve** (WP-47f): by a supremum argument on the
parameter (`shadowRel_local`, `ShadowRel.trans`). -/
theorem shadowRel_of_curve {γ : ℝ → M} (hγ : (CE M).CausalCurveOn ⊤ γ 0 1)
    (hS : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ S0 M) : ShadowRel (γ 0) (γ 1) := by
  set T : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ ShadowRel (γ 0) (γ s)} with hT
  have h0 : (0 : ℝ) ∈ T :=
    ⟨left_mem_Icc.2 zero_le_one, shadowRel_refl (hS 0 (left_mem_Icc.2 zero_le_one))⟩
  have hne : T.Nonempty := ⟨0, h0⟩
  have hbdd : BddAbove T := ⟨1, fun s hs => hs.1.2⟩
  set m := sSup T with hm
  have hm0 : 0 ≤ m := le_csSup hbdd h0
  have hm1 : m ≤ 1 := csSup_le hne fun s hs => hs.1.2
  have hmI : m ∈ Icc (0 : ℝ) 1 := ⟨hm0, hm1⟩
  obtain ⟨l, u, hl, hu, hloc⟩ := shadowRel_local hγ hS hmI
  obtain ⟨s, hsT, hls⟩ := exists_lt_of_lt_csSup hne hl
  have hsm : s ≤ m := le_csSup hbdd hsT
  have hext : ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → s' < u → s' ∈ T := fun s' hs' h1 h2 =>
    ⟨hs', hsT.2.trans (hloc s hsT.1 s' hs' hls h1 h2)⟩
  have hm1' : m = 1 := by
    by_contra hne1
    have hlt : m < 1 := lt_of_le_of_ne hm1 hne1
    set s' := min ((m + u) / 2) 1 with hs'
    have hs'm : m < s' := lt_min (by linarith) hlt
    have hs'T : s' ∈ T := hext s' ⟨by linarith, min_le_right _ _⟩ (by linarith)
      ((min_le_left _ _).trans_lt (by linarith))
    exact absurd (le_csSup hbdd hs'T) (not_le.2 hs'm)
  exact (hext 1 (right_mem_Icc.2 zero_le_one) (hsm.trans hm1'.le) (hm1' ▸ hu)).2


end LoopManifold

/-! ### §3 `𝔼₀`-manifolds: `E₀`-maximality and B21 Prop 2.16 through lemma K -/

section E0

open E0CBG E0Spear

/-- **Cauchy-compact** (B21 l.226, gx l.2224; `Causal.Flat.CauchyComplete`'s topological form):
a compact acausal Cauchy surface. -/
def E0CauchyCompact (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Prop :=
  ∃ S : Set M, (CE M).IsCauchySurface S ∧ IsCompact S ∧ (CE M).IsAcausal S

/-- **`E_A`-maximality, `A = {0}`** (B21 `sec:Abs_max`, l.1043–1046): every injective
`𝔼₀`-morphism of `M` into a globally hyperbolic `𝔼₀`-manifold (Hausdorff, connected, second
countable, as in `IsE0CauchyMaximal`) is bijective. -/
def IsE0Maximal (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Prop :=
  ∀ (N : Type) [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
    [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid] (f : M → N),
    (CE N).GloballyHyperbolic → IsE0Mor f univ → Injective f → Bijective f

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))

include hLine in
/-- `SingularFlatAxioms` of an `𝔼₀`-manifold, from (O2) (`E0LM.e0_singularFlatAxioms_of`). -/
theorem e0_sfa (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] :
    (CE M).SingularFlatAxioms (Causal.CBG.chartedSing e0SingY M) :=
  E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)

/-- **`SingularFlatAxioms` of every `𝔼₀`-manifold, unconditionally** (WP-43c): (O2) is now the
sorry-free `E0LM.e0_globalBTZ` (WP-43d), so `hLine` is dischargeable; the `hLine`-forms above are
kept for their callers. -/
theorem e0_sfa_of_globalBTZ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] :
    (CE M).SingularFlatAxioms (Causal.CBG.chartedSing e0SingY M) :=
  E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)

/-- **(O2) for every `𝔼₀`-manifold**: this file's `hLine` hypothesis, discharged by the sorry-free
`E0LM.e0_globalBTZ` (WP-43d). Callers of the `hLine`-forms pass `e0_hLine`. -/
theorem e0_hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0) :=
  fun M _ _ _ _ _ _ => E0LM.e0_globalBTZ M

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **B21 Lemma 2.13 (a)** for `𝔼₀`-manifolds, with no model-fact hypothesis (`SingularFlatAxioms`
from `e0_sfa_of_globalBTZ`): for an open `A` whose complement is BTZ, `A` is causally convex iff the
BTZ part of the future of each BTZ point of `A` lies in `A`. -/
theorem btzExt_causallyConvexIn_iff_e0 {A : Opens M} (hA : (A : Set M)ᶜ ⊆ S0 M) :
    (CE M).CausallyConvexIn (A : Set M) ⊤ ↔
      ∀ x ∈ S0 M, x ∈ A → ∀ y ∈ S0 M, (CE M).le ⊤ x y → y ∈ A :=
  btzExt_causallyConvexIn_iff (e0_sfa_of_globalBTZ M) hA

/-- **B21 Lemma 2.13 (b)** for `𝔼₀`-manifolds, with no model-fact hypothesis: a globally
hyperbolic open `A` whose complement is BTZ is causally convex. -/
theorem btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0 {A : Opens M}
    (hA : (A : Set M)ᶜ ⊆ S0 M) (hG : (CE M).GloballyHyperbolicOn A) :
    (CE M).CausallyConvexIn (A : Set M) ⊤ :=
  btzExt_causallyConvexIn_of_globallyHyperbolicOn (e0_sfa_of_globalBTZ M) hA hG

/-- **The closed BTZ loop of B21 Lemma 2.14's proof, for `𝔼₀`-manifolds** (`BTZ_1.tex:1031,
1035–1036`; DEC-126, WP-47f fixer): in an `𝔼₀`-manifold `M`, for an open `A` with BTZ complement
(a BTZ-extension `A ↪ M`) which is strongly causal, two BTZ points causal to each other are equal
— no closed future causal curve lies in `sing₀(M)`. The shadow of the loop (§2b) breaks strong
causality of `A` at a regular point near `x`. -/
theorem sing_eq_of_le_of_le_of_stronglyCausalOn_e0 {A : Opens M} (hA : (A : Set M)ᶜ ⊆ S0 M)
    (hSC : StronglyCausalOn (CE M) A) {x y : M} (hx : x ∈ S0 M) (hy : y ∈ S0 M)
    (hxy : (CE M).le ⊤ x y) (hyx : (CE M).le ⊤ y x) : x = y := by
  have h := e0_sfa_of_globalBTZ M
  by_contra hne
  -- the shadows of the two halves of the loop
  have hcurve : ∀ {a b : M}, b ∈ S0 M → (CE M).le ⊤ a b → ShadowRel a b := by
    intro a b hb hab
    obtain ⟨c, hc, hc0, hc1⟩ := (h.causallyArcConnected ⊤ le_rfl a b).1.1 hab
    have hS : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ S0 M := fun s hs =>
      h.mem_sing_zero_of_le hb (by rw [← hc1]; exact hc.le_of_le hs.1 hs.2 le_rfl)
    have := shadowRel_of_curve hc hS
    rwa [hc0, hc1] at this
  obtain ⟨τx, τy, ρ₁, R₁, hρ₁, hτx, hτy, h1⟩ := hcurve hy hxy
  obtain ⟨τy', τx', ρ₂, R₂, hρ₂, hτy', hτx', h2⟩ := hcurve hx hyx
  have ey : τy' = τy := paperInY_axis_injective (hτy'.symm.trans hτy)
  have ex : τx' = τx := paperInY_axis_injective (hτx'.symm.trans hτx)
  subst ey ex
  set κx := chartAt E0Y x with hκx
  set κy := chartAt E0Y y with hκy
  set shx : ℂ → M := fun z => κx.symm (E0.paperInY (τx', z)) with hshx
  set shy : ℂ → M := fun z => κy.symm (E0.paperInY (τy', z)) with hshy
  set ρ := min ρ₁ ρ₂ with hρ
  set R := R₁.trans R₂ with hR
  have hstep : ∀ z : ℂ, ‖z‖ < ρ →
      (CE M).le ⊤ (shx z) (shy (R₁ z)) ∧ (CE M).le ⊤ (shy (R₁ z)) (shx (R z)) := by
    intro z hz
    refine ⟨h1 z (hz.trans_le (min_le_left _ _)), ?_⟩
    have := h2 (R₁ z) (by rw [LinearIsometryEquiv.norm_map]; exact hz.trans_le (min_le_right _ _))
    rwa [hR, LinearIsometryEquiv.trans_apply]
  have hnorm : ∀ (n : ℕ) (z : ℂ), ‖(⇑R)^[n] z‖ = ‖z‖ := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih => intro z; rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]
  have hiter : ∀ (n : ℕ) (z : ℂ), ‖z‖ < ρ → (CE M).le ⊤ (shx z) (shx ((⇑R)^[n] z)) := by
    intro n
    induction n with
    | zero => intro z _; exact (CE M).le_refl trivial
    | succ n ih =>
      intro z hz
      have hs := hstep ((⇑R)^[n] z) (by rw [hnorm]; exact hz)
      rw [Function.iterate_succ_apply']
      exact (CE M).le_trans (ih z hz) ((CE M).le_trans hs.1 hs.2)
  -- continuity of the two horizontal discs at their centres
  have hxT : E0.paperInY ((τx', 0) : E0) ∈ κx.target := by
    rw [← hτx]; exact κx.map_source (mem_chart_source E0Y x)
  have hyT : E0.paperInY ((τy', 0) : E0) ∈ κy.target := by
    rw [← hτy]; exact κy.map_source (mem_chart_source E0Y y)
  have hlinx : Continuous fun z : ℂ => E0.paperInY ((τx', z) : E0) :=
    continuous_paperInY.comp (continuous_const.prodMk continuous_id)
  have hliny : Continuous fun z : ℂ => E0.paperInY ((τy', z) : E0) :=
    continuous_paperInY.comp (continuous_const.prodMk continuous_id)
  have hcx : ∀ z : ℂ, E0.paperInY ((τx', z) : E0) ∈ κx.target → ContinuousAt shx z :=
    fun z hz => ContinuousAt.comp (g := κx.symm) (f := fun z : ℂ => E0.paperInY ((τx', z) : E0))
      (κx.continuousAt_symm hz) hlinx.continuousAt
  have hcy : ∀ z : ℂ, E0.paperInY ((τy', z) : E0) ∈ κy.target → ContinuousAt shy z :=
    fun z hz => ContinuousAt.comp (g := κy.symm) (f := fun z : ℂ => E0.paperInY ((τy', z) : E0))
      (κy.continuousAt_symm hz) hliny.continuousAt
  have hshx0 : shx 0 = x := by
    show κx.symm (E0.paperInY (τx', 0)) = x
    rw [← hτx, κx.left_inv (mem_chart_source E0Y x)]
  have hshy0 : shy 0 = y := by
    show κy.symm (E0.paperInY (τy', 0)) = y
    rw [← hτy, κy.left_inv (mem_chart_source E0Y y)]
  obtain ⟨Nx, Ny, hNx, hNy, hxN, hyN, hdisj⟩ := t2_separation hne
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), shx z ∈ Nx ∧ shy z ∈ Ny ∧
      E0.paperInY ((τx', z) : E0) ∈ κx.target := by
    have e1 : ∀ᶠ z in 𝓝 (0 : ℂ), shx z ∈ Nx :=
      (hcx 0 hxT).preimage_mem_nhds (hNx.mem_nhds (by rw [hshx0]; exact hxN))
    have e2 : ∀ᶠ z in 𝓝 (0 : ℂ), shy z ∈ Ny :=
      (hcy 0 hyT).preimage_mem_nhds (hNy.mem_nhds (by rw [hshy0]; exact hyN))
    have e3 : ∀ᶠ z in 𝓝 (0 : ℂ), E0.paperInY ((τx', z) : E0) ∈ κx.target :=
      hlinx.continuousAt.preimage_mem_nhds (κx.open_target.mem_nhds hxT)
    exact e1.and (e2.and e3)
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hev
  -- a regular point `p` near `x`, and `q` on its shadow near `y`
  set r₀ := min η ρ / 2 with hr₀
  have hr₀pos : 0 < r₀ := by
    have : 0 < min η ρ := lt_min hη (lt_min hρ₁ hρ₂)
    linarith
  have hr₀η : r₀ < η := by have := min_le_left η ρ; linarith
  have hr₀ρ : r₀ < ρ := by have := min_le_right η ρ; linarith
  set z₀ : ℂ := (r₀ : ℂ) with hz₀
  have hz₀n : ‖z₀‖ = r₀ := by rw [hz₀, Complex.norm_real, Real.norm_of_nonneg hr₀pos.le]
  have hz₀η : dist z₀ 0 < η := by rw [dist_zero_right, hz₀n]; exact hr₀η
  have hRz₀η : dist (R₁ z₀) 0 < η := by
    rw [dist_zero_right, LinearIsometryEquiv.norm_map, hz₀n]; exact hr₀η
  obtain ⟨hpN, -, hpT⟩ := hηb hz₀η
  have hqN : shy (R₁ z₀) ∈ Ny := (hηb hRz₀η).2.1
  set p := shx z₀ with hp
  set q := shy (R₁ z₀) with hq
  have hpS : p ∉ S0 M := by
    intro hpS
    have hsrc : p ∈ κx.source := κx.map_target hpT
    have h0 := (chart_mem_e0SingY_iff x hsrc).2 hpS
    rw [hp, κx.right_inv hpT, e0Loop_paperInY_mem_sing_iff] at h0
    have : r₀ = 0 := by simpa [hz₀] using h0
    linarith
  have hpA : p ∈ A := by_contra fun h' => hpS (hA h')
  have hpq : (CE M).le ⊤ p q := (hstep z₀ (by rw [hz₀n]; exact hr₀ρ)).1
  have hqS : q ∉ S0 M := fun hqS => hpS (h.mem_sing_zero_of_le hqS hpq)
  -- strong causality at `p`, and the return of the shadow into `V`
  obtain ⟨V, hV, hVN, hconv⟩ := hSC p hpA Nx (hNx.mem_nhds hpN)
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 ((hcx z₀ hpT).preimage_mem_nhds hV)
  obtain ⟨n, hn1, hnδ⟩ := exists_iterate_near R z₀ hδ
  have hbV : shx ((⇑R)^[n] z₀) ∈ V := hδV (by rw [Metric.mem_ball, dist_eq_norm]; exact hnδ)
  have hqb : (CE M).le ⊤ q (shx ((⇑R)^[n] z₀)) := by
    have hRz : ‖R z₀‖ < ρ := by rw [LinearIsometryEquiv.norm_map, hz₀n]; exact hr₀ρ
    have e : (⇑R)^[n] z₀ = (⇑R)^[n - 1] (R z₀) := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [e]
    exact (CE M).le_trans (hstep z₀ (by rw [hz₀n]; exact hr₀ρ)).2 (hiter (n - 1) (R z₀) hRz)
  have hpqA := le_of_le_of_notMem_sing h hA hpS hpq
  have hqbA := le_of_le_of_notMem_sing h hA hqS hqb
  have hqV : q ∈ V := hconv.2 p (mem_of_mem_nhds hV) _ hbV
    (Causal.Causality.mem_diamond.2 ⟨hpqA, hqbA⟩)
  exact hdisj.le_bot ⟨hVN hqV, hqN⟩

/-- **B21 Lemma 2.14 for `𝔼₀`-manifolds** (`BTZ_1.tex:1026–1037`; open-set form, no model-fact
hypothesis): a BTZ-extension `A ↪ M` of a strongly causal `A` is causal. -/
theorem btzExt_isCausal_of_stronglyCausalOn_e0 {A : Opens M} (hA : (A : Set M)ᶜ ⊆ S0 M)
    (hSC : StronglyCausalOn (CE M) A) : (CE M).IsCausal :=
  btzExt_isCausal_of_stronglyCausalOn (e0_sfa_of_globalBTZ M) hA hSC
    fun _ hx _ hy hxy hyx => sing_eq_of_le_of_le_of_stronglyCausalOn_e0 hA hSC hx hy hxy hyx

/-- **B21 Cor 2.15 for `𝔼₀`-manifolds** (`cor:GH_causal`, `BTZ_1.tex:1038–1039`; open-set form,
no model-fact hypothesis): a BTZ-extension `A ↪ M` of a globally hyperbolic `A` is causal. A loop
outside `A` is excluded through Lemma 2.14's loop lemma, `A` being strongly causal
(`stronglyCausalOn_of_globallyHyperbolicOn`). -/
theorem cor_GH_causal_e0 {A : Opens M} (hA : (A : Set M)ᶜ ⊆ S0 M)
    (hG : (CE M).GloballyHyperbolicOn A) : (CE M).IsCausal :=
  cor_GH_causal (e0_sfa_of_globalBTZ M) hA hG fun _ hx _ hy hxy hyx =>
    sing_eq_of_le_of_le_of_stronglyCausalOn_e0 hA
      (stronglyCausalOn_of_globallyHyperbolicOn (e0_sfa_of_globalBTZ M) hA hG) (hA hx) (hA hy)
      hxy hyx

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- An `𝔼₀`-morphism on `univ` is continuous (no groupoid hypothesis on either side: a local
structomorphism is continuous within its domain at every point). The one continuity lemma of an
`𝔼₀`-morphism (T-gx-btz-cleanup: `GX.continuous_of_isE0Mor'` of `GX.BTZ.Embeddings` is this). -/
theorem continuous_of_isE0Mor {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    {f : M → N} (hf : IsE0Mor f univ) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact (continuousWithinAt_univ f x).1 (hf x (mem_univ x)).1

/-- **A compact acausal Cauchy surface of a connected globally hyperbolic `𝔼₀`-manifold is
connected** (implicit in B21 Prop 2.16, whose Cauchy surface is "a closed surface of genus g",
gx l.2215; the hypothesis `IsConnected S` of lemma K): `isConnected_of_isCauchySurface_abstract`
with tarentin, causal arc-connectedness and Levin's `CurvesExtend`. -/
theorem isConnected_of_isCauchySurface (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S) :
    IsConnected S :=
  isConnected_of_isCauchySurface_abstract E0LM.e0_tarentin hGH E0LM.e0_causallyArcConnected
    (E0LM.e0_curvesExtend hGH) hS hSc hSac

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Relations along an injective `𝔼₀`-morphism**: onto its image, an injective `𝔼₀`-morphism is
an isomorphism of the charted causalities (strong morphism forwards; backwards
`Causal.Flat.LocalIso.rel_of_image`, the charted causality being absolutely minimal on every open
set). -/
theorem le_iff_of_isE0Mor {Z : Type} [TopologicalSpace Z] [ChartedSpace E0Y Z]
    [HasGroupoid Z e0Groupoid] {φ : M → Z} (hf : IsE0Mor φ univ) (hinj : Injective φ)
    {U : Opens Z} (hU : (U : Set Z) = range φ) (x y : M) :
    (CE Z).le U (φ x) (φ y) ↔ (CE M).le ⊤ x y := by
  have hE := isEMorphismOn_of_isE0Mor (W := ⊤) hf
  have hloc := (Causal.isEMorphism_iff.1 hE).2
  have hU' : (U : Set Z) = φ '' ((⊤ : Opens M) : Set M) := by rw [hU, Opens.coe_top, image_univ]
  refine ⟨fun h => (Causal.Flat.LocalIso.rel_of_image hloc hinj
    (Causal.CBG.chartedCausality_absolutelyMinimalOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ) ⊤ U hU' x y).1 h, fun h => ?_⟩
  exact hE.map_le ⊤ U le_rfl (fun z _ => by rw [hU]; exact ⟨z, rfl⟩) h

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **B21 Remark 1 in its literal embedding form, for `𝔼₀`-manifolds** (`BTZ_1.tex:994–996`,
WP-46f): if `ι : M → N` is an injective `𝔼₀`-morphism (an embedding of `𝔼₀`-manifolds) into a
globally hyperbolic `N` with `ι(M)` causally convex, then `M` is globally hyperbolic. Causality and
diamonds pull back along `le_iff_of_isE0Mor` and causal convexity of the open image (an injective
`𝔼₀`-morphism is an open embedding). -/
theorem globallyHyperbolic_of_isE0Mor_of_causallyConvexIn {N : Type} [TopologicalSpace N]
    [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid] {ι : M → N} (hι : IsE0Mor ι univ)
    (hinj : Injective ι) (hG : (CE N).GloballyHyperbolic)
    (hconv : (CE N).CausallyConvexIn (range ι) ⊤) : (CE M).GloballyHyperbolic := by
  have hE := isEMorphismOn_of_isE0Mor (W := ⊤) hι
  have hopen : IsOpenMap ι := fun V hV => by
    have := hE.isOpen_image ⟨V, hV⟩ le_top
    simpa using this
  have hemb : IsOpenEmbedding ι :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_of_isE0Mor hι) hinj hopen
  let R : Opens N := ⟨range ι, hemb.isOpen_range⟩
  have hR : (CE N).CausallyConvexIn (R : Set N) ⊤ := hconv
  have hle : ∀ x y, (CE N).le ⊤ (ι x) (ι y) ↔ (CE M).le ⊤ x y := fun x y => by
    rw [← le_iff_of_isE0Mor hι hinj (U := R) rfl x y]
    exact (Causal.Causality.le_iff_of_causallyConvexIn E0LM.e0_causallyArcConnected hR
      (show ι y ∈ R from ⟨y, rfl⟩) (show ι x ∈ R from ⟨x, rfl⟩)).symm
  refine ⟨fun {x y} hxy hyx => hinj (hG.1 ((hle x y).2 hxy) ((hle y x).2 hyx)), fun x y => ?_⟩
  have hD : (CE M).diamond ⊤ x y = ι ⁻¹' (CE N).diamond ⊤ (ι x) (ι y) := by
    ext z
    simp only [mem_preimage, Causal.Causality.mem_diamond, hle]
  have hsub : (CE N).diamond ⊤ (ι x) (ι y) ⊆ range ι := hconv.2 _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [hD]
  exact (hemb.isInducing.isCompact_preimage_iff hsub).2 (hG.2 _ _)

/-- **Small local Cauchy charts of a Cauchy surface** (the intrinsic content of
`isLocallyCauchy_image`; **proved**, WP-46f): in a globally hyperbolic `𝔼₀`-manifold, a Cauchy
surface `S` is locally Cauchy with ARBITRARILY SMALL charts — every `s ∈ S` and every neighbourhood
`O` of `s` admit an open `W ∋ s` inside `O`, causally convex in `M`, in which `S ∩ W` is a Cauchy
surface. `W` is §1b's local Cauchy domain `cauchyDomain (CE M) S (interior O)`
(`exists_small_cauchyChart_abstract`: SFA's tarentin and causal arc-connectedness, Levin's time
function `E0LM.e0_timeFunction`, R1 `E0LM.sfa_isCompact_Jplus_inter_Jminus` and its past form).
Acausality of `S` is not used (it is derived). -/
theorem exists_small_cauchyChart (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (_hSac : (CE M).IsAcausal S) {s : M} (hs : s ∈ S)
    {O : Set M} (hO : O ∈ 𝓝 s) :
    ∃ W : Opens M, s ∈ W ∧ (W : Set M) ⊆ O ∧ (CE M).CausallyConvexIn (W : Set M) ⊤ ∧
      (CE M).IsCauchySurfaceOn W (S ∩ W) := by
  have h := e0_sfa_of_globalBTZ M
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
  exact exists_small_cauchyChart_abstract h.tarentin hGH h.causallyArcConnected hTc hT
    (E0LM.sfa_isCompact_Jplus_inter_Jminus h hGH hTc hT hS)
    (E0LM.sfa_isCompact_Jminus_inter_Jplus h hGH hTc hT hS) hS hs hO

/-- **The image of an acausal Cauchy surface is locally Cauchy** — the "spacelike hypersurface"
input of lemma K, for an injective `𝔼₀`-morphism between globally hyperbolic `𝔼₀`-manifolds: every
point `f s` has an open `U ∋ f s`, causally convex in `N`, in which `f(S) ∩ U` is a Cauchy
surface of `U`. **Reduced to the intrinsic `exists_small_cauchyChart` (WP-44f)**: strong
causality of `N` gives `V ∋ f s` causally convex in `N` inside the open `f(M)`; a small chart `W`
of `S` in `f⁻¹(V)` has `f(W)` causally convex in `N` (a diamond of `N` between points of `V` lies
in `V ⊆ f(M)` and pulls back by `le_iff_of_isE0Mor` into a diamond of `M`, inside `W`) and
`f(S ∩ W)` Cauchy in `f(W)` (`Causal.IsEMorphismOn.isCauchySurfaceOn_image_iff`). The flat
analogue is `Causal.Flat.Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding`. -/
theorem isLocallyCauchy_image {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]
    (hGH : (CE M).GloballyHyperbolic) (hGN : (CE N).GloballyHyperbolic) {f : M → N}
    (hf : IsE0Mor f univ) (hinj : Injective f) {S : Set M} (hS : (CE M).IsCauchySurface S)
    (hSac : (CE M).IsAcausal S) : (CE N).IsLocallyCauchy (f '' S) := by
  rintro _ ⟨s, hs, rfl⟩
  have hE := isEMorphismOn_of_isE0Mor (W := ⊤) hf
  have hR : IsOpen (range f) := by
    have := hE.isOpen_image ⊤ le_rfl
    rwa [Opens.coe_top, image_univ] at this
  let R : Opens N := ⟨range f, hR⟩
  obtain ⟨V, hV, hVR, hVconv⟩ := (hGN.stronglyCausal (E0LM.e0_tarentin (M := N))) (f s) (R : Set N)
    (hR.mem_nhds ⟨s, rfl⟩)
  have hO : f ⁻¹' V ∈ 𝓝 s := (continuous_of_isE0Mor hf).continuousAt.preimage_mem_nhds hV
  obtain ⟨W, hsW, hWO, hWconv, hSW⟩ := exists_small_cauchyChart hGH hS hSac hs hO
  have hWopen : IsOpen (f '' (W : Set M)) := hE.isOpen_image W le_top
  let U : Opens N := ⟨f '' (W : Set M), hWopen⟩
  refine ⟨U, ⟨s, hsW, rfl⟩, ⟨subset_univ _, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
    have hsub : (CE N).diamond ⊤ (f a) (f b) ⊆ R := fun w hw => hVR (hVconv.2 (f a) (hWO ha)
      (f b) (hWO hb) hw)
    obtain ⟨hz1, hz2⟩ := Causal.Causality.mem_diamond.1 hz
    obtain ⟨z', rfl⟩ := hsub hz
    have hfa : f a ∈ (CE N).diamond ⊤ (f a) (f b) :=
      Causal.Causality.mem_diamond.2 ⟨(CE N).le_refl trivial, (CE N).le_trans hz1 hz2⟩
    have hfb : f b ∈ (CE N).diamond ⊤ (f a) (f b) :=
      Causal.Causality.mem_diamond.2 ⟨(CE N).le_trans hz1 hz2, (CE N).le_refl trivial⟩
    have h1 := (le_iff_of_isE0Mor hf hinj (U := R) rfl a z').1
      (le_of_diamond_subset E0LM.e0_causallyArcConnected hsub hfa hz hz1)
    have h2 := (le_iff_of_isE0Mor hf hinj (U := R) rfl z' b).1
      (le_of_diamond_subset E0LM.e0_causallyArcConnected hsub hz hfb hz2)
    exact ⟨z', hWconv.2 a ha b hb (Causal.Causality.mem_diamond.2 ⟨h1, h2⟩), rfl⟩
  · have himg : f '' S ∩ (U : Set N) = f '' (S ∩ (W : Set M)) := (image_inter hinj).symm
    rw [himg]
    exact (hE.isCauchySurfaceOn_image_iff hinj.injOn le_top rfl inter_subset_right).1 hSW

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **B21 Prop 2.16, (ii) ⇒ (i)** (`BTZ_1.tex:1055`): `E₀`-maximal ⇒ Cauchy-maximal (a Cauchy
embedding is an injective `𝔼₀`-morphism into a globally hyperbolic manifold). -/
theorem isE0CauchyMaximal_of_isE0Maximal (h : IsE0Maximal M) : IsE0CauchyMaximal M :=
  fun N _ _ _ _ _ _ f hf hfm => h N f hf.globallyHyperbolic_target hfm hf.injective

include hLine in
/-- **B21 Prop 2.16, (i) ⇒ (ii)** (`BTZ_1.tex:1056–1075`), through lemma K
(`Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus`) in place of the
paper's smooth splitting, O'Neill's Lemma 45 and intersection theory: for `ι : M → N` injective,
the image `ι(S)` of a compact acausal Cauchy surface is compact, connected
(`isConnected_of_isCauchySurface`) and locally Cauchy (`isLocallyCauchy_image`), and `N` has every hypothesis of lemma K — tarentin, causally
arc-connected, `J^±(p) ≠ {p}`, push-up, `Z⁺ = N`, `J⁺(V)` open at BTZ points included
(`E0LM.sfa_isOpen_Jplus`), curves extending (Levin, `E0LM.e0_curvesExtend`) — so `ι(S)` is a
Cauchy surface of `N`, `ι` a Cauchy embedding, and Cauchy-maximality makes it bijective. -/
theorem isE0Maximal_of_isE0CauchyMaximal (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) : IsE0Maximal M := by
  intro N _ _ _ _ _ _ f hGN hf hinj
  have hN := e0_sfa hLine N
  have hfc := continuous_of_isE0Mor hf
  have himage : (CE N).IsCauchySurface (f '' S) :=
    Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus hN.tarentin hGN
      hN.causallyArcConnected hN.Jminus_ne_singleton hN.Jplus_ne_singleton
      (E0LM.e0_curvesExtend hGN) hN.pushUp hN.mem_Zplus
      (fun V => E0LM.sfa_isOpen_Jplus hN V.isOpen) (hSc.image hfc)
      ((isConnected_of_isCauchySurface hGH hS hSc hSac).image f hfc.continuousOn) (isLocallyCauchy_image hGH hGN hf hinj hS hSac)
  exact hmax N f ⟨hGH, hGN, isEMorphismOn_of_isE0Mor (W := ⊤) hf, hinj, S, hS, himage⟩ hf

include hLine in
/-- **B21 Prop 2.16** (`BTZ_1.tex:1048–1075`), for `𝔼₀`-manifolds: a globally hyperbolic
`𝔼₀`-manifold with a compact acausal Cauchy surface is Cauchy-maximal iff it is
`E₀`-maximal. -/
theorem prop_cauchy_abs_max (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S) :
    IsE0CauchyMaximal M ↔ IsE0Maximal M :=
  ⟨isE0Maximal_of_isE0CauchyMaximal hLine hGH hS hSc hSac,
    isE0CauchyMaximal_of_isE0Maximal⟩

include hLine in
/-- **B21 Prop 2.16** (`BTZ_1.tex:1048–1075`) as printed, for `𝔼₀`-manifolds: GH and
Cauchy-compact ⇒ (Cauchy-maximal ⇔ `E₀`-maximal). -/
theorem prop_cauchy_abs_max_of_cauchyCompact (hGH : (CE M).GloballyHyperbolic)
    (hCC : E0CauchyCompact M) : IsE0CauchyMaximal M ↔ IsE0Maximal M := by
  obtain ⟨S, hS, hSc, hSac⟩ := hCC
  exact prop_cauchy_abs_max hLine hGH hS hSc hSac


/-! ### §5 `Reg M` globally hyperbolic as a flat spacetime (B21 Prop 2.17, first assertion) -/

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The charted causality of an open subset is the restriction** (the `𝔼₀` instance of
`Causal.CBG.Geometry.causality_restrict`, proved without the CBG geometry's named hypotheses):
`CE ↥W = ((CE M).restrict W).toSubtype`. -/
theorem ce_opens_eq (W : Opens M) : CE W = ((CE M).restrict W).toSubtype := by
  have hval : Causal.IsEMorphism (CE W) (CE M) Subtype.val :=
    isEMorphismOn_of_isE0Mor (W := ⊤) (isE0Mor_val W)
  have hloc := (Causal.isEMorphism_iff.1 hval).2
  have hmaps : ∀ V : Opens W, MapsTo Subtype.val (V : Set W) (Causal.imageOpens V : Set M) :=
    fun V x hx => ⟨x, hx, rfl⟩
  have hA := Causal.CBG.chartedCausality_absolutelyMinimalOn (M := M) E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ
  apply Causal.Causality.ext_toPrecausality
  ext V x y
  · exact ⟨fun h => hval.map_le V (Causal.imageOpens V) le_top (hmaps V) h, fun h =>
      (Causal.Flat.LocalIso.rel_of_image hloc Subtype.val_injective hA V (Causal.imageOpens V) rfl
        x y).1 h⟩
  · exact ⟨fun h => hval.map_lt V (Causal.imageOpens V) le_top (hmaps V) h, fun h =>
      (Causal.Flat.LocalIso.rel_of_image hloc Subtype.val_injective hA V (Causal.imageOpens V) rfl
        x y).2 h⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **B21 Remark 1** (`BTZ_1.tex:994–996`) for an open subset of an `𝔼₀`-manifold: a causally
convex open subset of a globally hyperbolic `𝔼₀`-manifold is a globally hyperbolic `𝔼₀`-manifold
(`globallyHyperbolicOn_of_causallyConvexIn`, read on `↥W` through `ce_opens_eq`). -/
theorem globallyHyperbolic_opens_of_causallyConvexIn (hGH : (CE M).GloballyHyperbolic)
    {W : Opens M} (hW : (CE M).CausallyConvexIn (W : Set M) ⊤) : (CE W).GloballyHyperbolic := by
  rw [ce_opens_eq]
  exact Causal.Causality.globallyHyperbolic_toSubtype
    (globallyHyperbolicOn_of_causallyConvexIn hGH E0LM.e0_causallyArcConnected hW)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- The flat charts of `Reg M` are its `𝔼₀` charts followed by regular charts of `Y`. -/
theorem regChart_subtypeRestr_eq (y : E0LM.e0RegM M) :
    (E0LM.regChartM y).subtypeRestr ⟨y⟩ = (chartAt E0Y y).trans (E0LM.regAtlasChart y) := by
  rw [OpenPartialHomeomorph.subtypeRestr_def, E0LM.regChartM, ← OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.subtypeRestr_def]
  rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The flat causality of `Reg M` is its `𝔼₀` causality** (`Causal.Flat.eq_flatCausality`): every
chart of the flat atlas is a chart isomorphism (`𝔼₀` chart, then a regular chart of `Y`,
`E0.chartIso_e0Atlas`), hence every chart of the maximal flat atlas
(`Causal.chartIso_of_mem_maximalAtlas`), and the charted causality is absolutely minimal. -/
theorem flatCausality_e0RegM_eq :
    Causal.Flat.flatCausality 2 (E0LM.e0RegM M) = CE (E0LM.e0RegM M) := by
  have hmin : (CE (E0LM.e0RegM M)).AbsolutelyMinimal :=
    Causal.CBG.chartedCausality_absolutelyMinimal E0.absolutelyMinimalOn_YBTZ
  have hatlas : ∀ e ∈ atlas (Causal.Minkowski 2) (E0LM.e0RegM M),
      Causal.ChartIso (CE (E0LM.e0RegM M)) (Causal.minkowski 2) e := by
    rintro _ ⟨y, rfl⟩
    show Causal.ChartIso _ _ ((E0LM.regChartM y).subtypeRestr ⟨y⟩)
    rw [regChart_subtypeRestr_eq]
    exact E0.chartIso_trans
      (Causal.CBG.chartedCausality_chartIso E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ y)
      (E0.chartIso_e0Atlas (E0LM.regAtlasChart_mem y))
  exact (Causal.Flat.eq_flatCausality _ (fun e he =>
    Causal.chartIso_of_mem_maximalAtlas Causal.minkowski_causallyArcConnected
      Causal.Flat.isom_strongMorphism hatlas hmin he) hmin).symm

include hLine in
/-- **`Reg M` is globally hyperbolic** (B21 Prop 2.17, first assertion, its GH part; `Reg M` as
`e0RegMFlat M`, the flat spacetime WP-39m's holonomy consumes): `Reg M = sing₀ᶜ` is causally
convex in the globally hyperbolic `M` (BTZ points precede), so globally hyperbolic in `M`
(Remark 1), and its flat causality is the restricted one. -/
theorem gh_e0RegMFlat (hGH : (CE M).GloballyHyperbolic) : Causal.Flat.GH (e0RegMFlat M) := by
  have hR : (CE M).GloballyHyperbolicOn (E0LM.e0RegM M) :=
    globallyHyperbolicOn_reg (e0_sfa hLine M) hGH rfl
  have h := Causal.Causality.globallyHyperbolic_toSubtype hR
  rw [← ce_opens_eq] at h
  show (Causal.Flat.flatCausality 2 (E0LM.e0RegM M)).GloballyHyperbolic
  rw [flatCausality_e0RegM_eq]
  exact h

/-! ### §4a B21 Lemma 2.12 in the case Prop 2.17 uses: the push-out is Hausdorff

B21 l.957–988. For `(p, q)` in the closure of the graph of `f : Reg M → N`, `p` regular gives
`q = f p`. If `p` were a BTZ point: a decreasing chronological sequence `bₙ → p` of regular
points (`exists_seq_lt_tendsto`) has `f(bₙ)` decreasing in the compact `J(q, f b₀)`, with a
cluster point `q'` ≤ every `f(bₙ)` and ≤ `f(I⁺(p))` (`le_image_of_graphCluster`); the diamonds
`J(q', f bₙ)` shrink into any neighbourhood `O` of `q'`. A BTZ point `z` above `p` close to `p`
(`exists_sing_above`) has a neighbourhood whose regular part lies in `I⁺(p) ∩ I⁻(bₙ)`
(`exists_nhds_diff_sing_subset_Iplus`), mapped by `f` into `J(q', f bₙ) ⊆ O`. With `O` a small
chart ball of `N`, `f` read in a chart of `M` at `z` and a chart of the maximal a.e. atlas of
`𝔼₀` is an injective local `G`-structomorphism of the regular part of a connected neighbourhood
of the BTZ point `κ z` into `𝔼₀` (`exists_nhds_not_mapsTo`), which `GX.e0_localUnique_sing` (B21
`prop:isom_strong`, the paper's « nontrivial parabolic holonomy » step) extends across `κ z` by
an element of `G`: the extension sends the singular `κ z` into the compact regular closure of
the image — impossible. -/

open E0 in
omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **BTZ points above `p` arbitrarily close to `p`**: the axis of a chart cylinder at `p`. -/
theorem exists_sing_above {p : M} (hp : p ∈ S0 M) {V : Set M} (hV : V ∈ 𝓝 p) :
    ∃ z ∈ V, z ∈ S0 M ∧ (CE M).le ⊤ p z ∧ z ≠ p := by
  obtain ⟨v, ε, W, ψ, hε, hW, hcyl, hψ, hinj, hψp⟩ := exists_cyl_chart hp
  have hax : ∀ t : ℝ, 0 ≤ t → t < ε → yAxis v t ∈ W := fun t ht0 ht =>
    hcyl ⟨((v + t, 0) : E0), ⟨by linarith, by linarith, by rw [rad_eq_zero.2 rfl]; exact hε⟩, rfl⟩
  have hψc : ContinuousAt ψ (yAxis v 0) :=
    (hψ _ (hax 0 le_rfl hε)).continuousWithinAt.continuousAt (hW.mem_nhds (hax 0 le_rfl hε))
  have hlim : Tendsto (fun t => ψ (yAxis v t)) (𝓝 0) (𝓝 p) := by
    have := hψc.tendsto.comp ((continuous_yAxis v).tendsto 0)
    rwa [yAxis_zero, hψp] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hlim.eventually hV)
  set t : ℝ := min δ ε / 2 with ht
  have ht0 : 0 < t := by have := lt_min hδ hε; positivity
  have htδ : t < δ := by have := min_le_left δ ε; linarith
  have htε : t < ε := by have := min_le_right δ ε; linarith
  refine ⟨ψ (yAxis v t), hball (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ),
    ?_, ?_, ?_⟩
  · refine (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem hW hψ (hax t ht0.le htε)
      le_rfl).1 ?_
    show chartAt E0Y (yAxis v t) (yAxis v t) ∈ e0SingY 0
    rw [chartAt_self_eq]
    exact yAxis_mem_e0SingY v t
  · have : (CE M).le ⊤ (ψ (yAxis v 0)) (ψ (yAxis v t)) := by
      set U : Opens E0 := ⟨paperInY ⁻¹' W, hW.preimage continuous_paperInY⟩
      refine le_of_isE0Mor_paper hW hψ (U := U) subset_rfl ?_
      refine le_vertical (by linarith) fun r hr => ?_
      show paperInY ((v + 0 + r * (v + t - (v + 0)), 0) : E0) ∈ W
      have e : v + 0 + r * (v + t - (v + 0)) = v + r * t := by ring
      rw [e]
      exact hax _ (by nlinarith [hr.1]) (by nlinarith [hr.1, hr.2])
    rwa [yAxis_zero, hψp] at this
  · intro he
    have h1 : yAxis v t = yAxis v 0 :=
      hinj (hax t ht0.le htε) (hax 0 le_rfl hε) (by rw [he, yAxis_zero, hψp])
    exact ht0.ne' (yAxis_injective v h1)

/-- **A decreasing chronological sequence of `I⁺(p)` converging to `p`** (`Z⁺ = M`). -/
theorem exists_seq_lt_tendsto {p : M} :
    ∃ b : ℕ → M, (∀ n, (CE M).lt ⊤ p (b n)) ∧ (∀ n, (CE M).lt ⊤ (b (n + 1)) (b n)) ∧
      Tendsto b atTop (𝓝 p) := by
  have hsfa := e0_sfa_of_globalBTZ M
  haveI := hsfa.metrizable
  have hp := hsfa.mem_Zplus p
  obtain ⟨V, hV⟩ := (𝓝 p).exists_antitone_basis
  have hstep : ∀ (n : ℕ) (c : M), (CE M).lt ⊤ p c →
      ∃ c', (CE M).lt ⊤ p c' ∧ (CE M).lt ⊤ c' c ∧ c' ∈ V n := by
    intro n c hc
    obtain ⟨c', hc'I, hc'U⟩ := hp _ (inter_mem (hV.mem n)
      ((CE M).isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hc)))
    exact ⟨c', Causal.Precausality.mem_Iplus_singleton.1 hc'I,
      Causal.Precausality.mem_Iminus_singleton.1 hc'U.2, hc'U.1⟩
  obtain ⟨c₀, hc₀, hc₀V⟩ := hp _ (hV.mem 0)
  choose! s hs using hstep
  let b : ℕ → M := fun n => Nat.rec c₀ (fun n c => s (n + 1) c) n
  have hb : ∀ n, (CE M).lt ⊤ p (b n) ∧ b n ∈ V n := by
    intro n
    induction n with
    | zero => exact ⟨Causal.Precausality.mem_Iplus_singleton.1 hc₀, hc₀V⟩
    | succ n ih => exact ⟨(hs (n + 1) (b n) ih.1).1, (hs (n + 1) (b n) ih.1).2.2⟩
  exact ⟨b, fun n => (hb n).1, fun n => (hs (n + 1) (b n) (hb n).1).2.1,
    hV.tendsto fun n => (hb n).2⟩

/-- An isometric embedding of `Reg M` maps the chronological relation of `M` between regular
points to that of `N` (`lt_reg_of_lt`, `ce_opens_eq`, `flatCausality_e0RegM_eq`). -/
theorem lt_image_of_lt {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) {w x : E0LM.e0RegM M}
    (hwx : (CE M).lt ⊤ (w : M) x) : (Causal.Flat.flatCausality 2 N).lt ⊤ (f w) (f x) := by
  have hR := lt_reg_of_lt (e0_sfa_of_globalBTZ M) (R := E0LM.e0RegM M) rfl w.2 hwx
  have h1 : (CE (E0LM.e0RegM M)).lt ⊤ w x := by
    rw [ce_opens_eq]
    show (CE M).lt (Causal.imageOpens (⊤ : Opens (E0LM.e0RegM M))) w x
    rw [Causal.imageOpens_top]; exact hR
  rw [← flatCausality_e0RegM_eq] at h1
  exact hf.strongMorphism.lt_of_mapsTo (V := ⊤) (U := ⊤) (fun _ _ => trivial) h1

/-- `(p, r)` lies in the closure of the graph of `f : Reg M → N`, in neighbourhood form. -/
def GraphCluster {N : Causal.Flat.FlatSpacetime.{0} 2} (f : e0RegMFlat M → N) (p : M) (r : N) :
    Prop :=
  ∀ U ∈ 𝓝 p, ∀ V ∈ 𝓝 r, ∃ w : E0LM.e0RegM M, (w : M) ∈ U ∧ f w ∈ V

/-- B21 l.964–973 in the form used: for `(p, r)` in the closure of the graph, `r ≤ f x` for every
regular `x ≫ p` (`I⁻(x)` is a neighbourhood of `p`, and `J⁻(f x)` is closed in the GH `N`). -/
theorem le_image_of_graphCluster {N : Causal.Flat.FlatSpacetime.{0} 2} (hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) {p : M} {r : N}
    (hr : GraphCluster f p r) {x : E0LM.e0RegM M} (hpx : (CE M).lt ⊤ p x) :
    (Causal.Flat.flatCausality 2 N).le ⊤ r (f x) := by
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hcl := hN'.isClosed_Jminus_singleton Causal.Flat.flatCausality_tarentin (f x)
  have hmem : r ∈ closure ((Causal.Flat.flatCausality 2 N).Jminus ⊤ {f x}) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨w, hw, hwV⟩ := hr _ ((CE M).isOpen_Iminus.mem_nhds
      (Causal.Precausality.mem_Iminus_singleton.2 hpx)) V hV
    refine ⟨f w, hwV, Causal.Precausality.mem_Jminus_singleton.2 ?_⟩
    exact (Causal.Flat.flatCausality 2 N).le_of_lt
      (lt_image_of_lt hf (Causal.Precausality.mem_Iminus_singleton.1 hw))
  rw [hcl.closure_eq] at hmem
  exact Causal.Precausality.mem_Jminus_singleton.1 hmem

attribute [local instance] btzE0Structure in
omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The holonomy step of B21 Lemma 2.12** (`BTZ_1.tex:980–984`, « `𝒲` contains a non trivial
loop of parabolic holonomy »), through `GX.e0_localUnique_sing`: every point `q'` of a flat
spacetime `N` has a neighbourhood `O` such that an isometric embedding `f : Reg M → N` maps the
regular part of no neighbourhood of a BTZ point of `M` into `O`. `O` is a chart ball small
enough to be carried by a translation into a chart of the maximal a.e. atlas of `𝔼₀`; `f` read
in a chart of `M` at `z` then extends, by `e0_localUnique_sing`, to an element of `G` at the
singular `κ z`, which it must send into the compact regular closure of the image. -/
theorem exists_nhds_not_mapsTo {N : Causal.Flat.FlatSpacetime.{0} 2} [T2Space M] [ConnectedSpace M]
    {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) (q' : N) :
    ∃ O ∈ 𝓝 q', ∀ z ∈ S0 M, ∀ V ∈ 𝓝 z, ∃ w : E0LM.e0RegM M, (w : M) ∈ V ∧ f w ∉ O := by
  classical
  -- a chart `c'` of the maximal a.e. atlas of `𝔼₀`, and a ball in its target
  obtain ⟨x₀, hx₀⟩ : (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0).Nonempty :=
    (isPortly_reg _ _ _).dense.nonempty
  obtain ⟨c', hc', hx₀c'⟩ := mem_support.1 hx₀
  set m₁ := c' x₀ with hm₁
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 c'.open_target m₁ (c'.map_source hx₀c')
  set χ := chartAt (Causal.Minkowski 2) q' with hχ
  set m₀ := χ q' with hm₀
  set h : Causal.Flat.isom 2 :=
    ⟨AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) (m₁ - m₀), Causal.Flat.constVAdd_mem_isom _⟩
    with hhdef
  have hsmul : ∀ m, h • m = (m₁ - m₀) + m := fun m => rfl
  set O : Set N := χ.source ∩ χ ⁻¹' Metric.ball m₀ (ρ / 2) with hO
  have hOn : O ∈ 𝓝 q' := (χ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
    ⟨mem_chart_source _ q', Metric.mem_ball_self (by linarith)⟩
  have hhO : ∀ n ∈ O, h • χ n ∈ Metric.ball m₁ (ρ / 2) := by
    intro n hn
    have := hn.2
    rw [mem_preimage, Metric.mem_ball] at this
    rw [Metric.mem_ball, hsmul, dist_eq_norm]
    have e : m₁ - m₀ + χ n - m₁ = χ n - m₀ := by abel
    rw [e, ← dist_eq_norm]; exact this
  have hKt : Metric.closedBall m₁ (ρ / 2) ⊆ c'.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨O, hOn, fun z hz V hV => ?_⟩
  by_contra hcon
  push Not at hcon
  set κ := chartAt E0Y z with hκ
  have hzκ : z ∈ κ.source := mem_chart_source E0Y z
  have hy₀ : κ z ∈ e0SingY 0 := hz
  set A : Set E0Y := κ.target ∩ κ.symm ⁻¹' interior V with hA
  have hAo : IsOpen A := κ.isOpen_inter_preimage_symm isOpen_interior
  have hy₀A : κ z ∈ A := ⟨κ.map_source hzκ, by
    rw [mem_preimage, κ.left_inv hzκ]; exact mem_interior_iff_mem_nhds.2 hV⟩
  set U' := connectedComponentIn A (κ z) with hU'
  have hU'o : IsOpen U' := hAo.connectedComponentIn
  have hU'c : IsConnected U' := isConnected_connectedComponentIn_iff.2 hy₀A
  have hy₀U' : κ z ∈ U' := mem_connectedComponentIn hy₀A
  have hU'A : U' ⊆ A := connectedComponentIn_subset A (κ z)
  set R' : Set E0Y := U' ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} with hR'
  have hreg : ∀ y ∈ R', κ.symm y ∈ E0LM.e0RegM M := fun y hy =>
    (E0LM.mem_e0RegM_iff (κ.map_target (hU'A hy.1).1)).2
      (by rw [κ.right_inv (hU'A hy.1).1, ← e0RegSet_eq]; exact hy.2)
  have hfO : ∀ y (hy : y ∈ R'), f ⟨κ.symm y, hreg y hy⟩ ∈ O := fun y hy =>
    hcon ⟨κ.symm y, hreg y hy⟩ (interior_subset (hU'A hy.1).2)
  let F : M → N := fun m => if hm : m ∈ E0LM.e0RegM M then f ⟨m, hm⟩ else q'
  have hF : ∀ (m : M) (hm : m ∈ E0LM.e0RegM M), F m = f ⟨m, hm⟩ := fun m hm => dif_pos hm
  let g' : E0Y → E0Y := fun y => Sum.inr (c'.symm (h • χ (F (κ.symm y))))
  have hg' : ∀ y (hy : y ∈ R'), g' y = Sum.inr (c'.symm (h • χ (f ⟨κ.symm y, hreg y hy⟩))) :=
    fun y hy => by simp only [g', hF _ (hreg y hy)]
  -- injectivity
  have hinj : InjOn g' R' := by
    intro y₁ hy₁ y₂ hy₂ he
    rw [hg' y₁ hy₁, hg' y₂ hy₂] at he
    have he1 := Sum.inr_injective he
    have hb1 := hKt (Metric.ball_subset_closedBall (hhO _ (hfO y₁ hy₁)))
    have hb2 := hKt (Metric.ball_subset_closedBall (hhO _ (hfO y₂ hy₂)))
    have he2 := c'.symm.injOn (by rwa [c'.symm_source]) (by rwa [c'.symm_source]) he1
    rw [smul_left_cancel_iff] at he2
    have he3 := χ.injOn (hfO y₁ hy₁).1 (hfO y₂ hy₂).1 he2
    have he4 := congrArg Subtype.val (hf.2 he3)
    exact κ.symm.injOn (by rw [κ.symm_source]; exact (hU'A hy₁.1).1)
      (by rw [κ.symm_source]; exact (hU'A hy₂.1).1) he4
  -- the image lies in `𝔼₀`
  have hmaps : MapsTo g' R' (connectedComponent (κ z)) := by
    obtain ⟨x, hx⟩ : ∃ x, κ z = Sum.inr x := by
      rcases hk : κ z with m | x
      · rw [hk] at hy₀; exact absurd (inl_mem_e0Reg m) hy₀.2
      · exact ⟨x, rfl⟩
    intro y _
    rw [hx, connectedComponent_inr_eq]
    exact ⟨_, rfl⟩
  -- the local structomorphism property
  have hloc : ∀ y ∈ R', e0Groupoid.IsLocalStructomorphWithinAt g' R' y := by
    intro y hy _
    have hyt : y ∈ κ.target := (hU'A hy.1).1
    set m := κ.symm y with hm
    set w : E0LM.e0RegM M := ⟨m, hreg y hy⟩ with hw
    have hwO : f w ∈ O := hfO y hy
    obtain ⟨γ, hγ⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hf.1).2 w
    set χw := chartAt (Causal.Minkowski 2) (f w) with hχw
    have hτN : χw.symm.trans χ ∈ Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2) :=
      HasGroupoid.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    have ha₀ : χw (f w) ∈ (χw.symm.trans χ).source := by
      refine ⟨χw.map_source (mem_chart_source _ _), ?_⟩
      have e1 : χw.symm (χw (f w)) = f w := χw.left_inv (mem_chart_source _ _)
      show χw.symm (χw (f w)) ∈ χ.source
      rw [e1]; exact hwO.1
    obtain ⟨γ₂, hγ₂⟩ := (Causal.mem_gxGroupoid_iff.1 hτN).1 _ ha₀
    have hχf : ∀ᶠ w' : E0LM.e0RegM M in 𝓝 w,
        χ (f w') = (γ₂ * γ) • E0LM.regAtlasChart w (chartAt E0Y m (w' : M)) := by
      have hcf : ContinuousAt (fun w' => χw (f w')) w :=
        (χw.continuousAt (mem_chart_source _ _)).comp hf.continuous.continuousAt
      filter_upwards [hγ, hcf.eventually hγ₂, hf.continuous.continuousAt.eventually
        (χw.open_source.mem_nhds (mem_chart_source _ (f w)))] with w' h1 h2 h3
      have h4 : (χw.symm.trans χ) (χw (f w')) = χ (f w') := by
        simp only [OpenPartialHomeomorph.coe_trans, comp_apply, χw.left_inv h3]
      rw [← h4, h2, h1, mul_smul]
      rfl
    have hP : ∀ᶠ m' in 𝓝 m, ∀ hm' : m' ∈ E0LM.e0RegM M,
        χ (f ⟨m', hm'⟩) = (γ₂ * γ) • E0LM.regAtlasChart w (chartAt E0Y m m') := by
      have hmap := ((E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq w
      rw [← hmap, eventually_map]
      filter_upwards [hχf] with w' hw' hm'
      exact hw'
    set Pset : Set E0Y := {y' | y' ∈ κ.target ∧ κ.symm y' ∈ (chartAt E0Y m).source ∧
      ∀ hm' : κ.symm y' ∈ E0LM.e0RegM M,
        χ (f ⟨κ.symm y', hm'⟩) = (γ₂ * γ) • E0LM.regAtlasChart w (chartAt E0Y m (κ.symm y'))}
      with hPset
    have hyev : Pset ∈ 𝓝 y := by
      have hc := κ.continuousAt_symm hyt
      filter_upwards [κ.open_target.mem_nhds hyt,
        hc.eventually ((chartAt E0Y m).open_source.mem_nhds (mem_chart_source E0Y m)),
        hc.eventually hP] with y' h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hτ' : κ.symm.trans (chartAt E0Y m) ∈ e0Groupoid :=
      HasGroupoid.compatible (chart_mem_atlas E0Y z) (chart_mem_atlas E0Y m)
    set G₀ : Causal.Flat.isom 2 := h * (γ₂ * γ) with hG₀
    set ρw := E0LM.regAtlasChart w with hρw
    set σ₂ : OpenPartialHomeomorph E0Y E0Y := ρw.trans
      ((Homeomorph.smul G₀).toOpenPartialHomeomorph.trans (c'.symm.trans e0Inr)) with hσ₂
    have hσ₂src : ∀ y', y' ∈ σ₂.source ↔ y' ∈ ρw.source ∧ G₀ • ρw y' ∈ c'.target := by
      intro y'
      simp [σ₂]
    have hσ₂app : ∀ y', σ₂ y' = Sum.inr (c'.symm (G₀ • ρw y')) := fun y' => rfl
    have hσ₂mem : σ₂ ∈ e0Groupoid := by
      refine mem_e0Groupoid_of_chart_eq (E0LM.regAtlasChart_mem w) (e0InrChart_mem_e0Atlas hc')
        (fun y' hy' => ((hσ₂src y').1 hy').1) ?_ G₀ ?_
      · intro y' hy'
        have hs := σ₂.map_target hy'
        obtain ⟨-, h2⟩ := (hσ₂src _).1 hs
        rw [← σ₂.right_inv hy', hσ₂app]
        exact mem_e0InrChart_source.2 ⟨_, c'.map_target h2, rfl⟩
      · intro y' hy'
        obtain ⟨-, h2⟩ := (hσ₂src y').1 hy'
        rw [hσ₂app, e0InrChart_inr, c'.right_inv h2]
    have hσ := e0Groupoid.trans hτ' hσ₂mem
    refine ⟨((κ.symm.trans (chartAt E0Y m)).trans σ₂).restr (interior Pset),
      closedUnderRestriction' hσ isOpen_interior, ?_, ?_⟩
    · rintro y' ⟨hy'R, hy'e⟩
      rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_interior] at hy'e
      have hP' := (interior_subset hy'e.2 : y' ∈ Pset).2.2 (hreg y' hy'R)
      rw [hg' y' hy'R]
      show _ = σ₂ (chartAt E0Y m (κ.symm y'))
      rw [hσ₂app, hP']
      simp only [hG₀, mul_smul]
      rfl
    · rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_interior]
      refine ⟨⟨⟨hyt, mem_chart_source E0Y m⟩, ?_⟩,
        mem_interior_iff_mem_nhds.2 hyev⟩
      have hw1 := hχf.self_of_nhds
      refine (hσ₂src _).2 ⟨E0LM.mem_regAtlasChart_source w, ?_⟩
      have e1 : G₀ • ρw (chartAt E0Y m m) = h • χ (f w) := by
        rw [hG₀, mul_smul]; congr 1; exact hw1.symm
      show G₀ • ρw (chartAt E0Y m (κ.symm y)) ∈ c'.target
      rw [← hm, e1]
      exact hKt (Metric.ball_subset_closedBall (hhO _ hwO))
  -- `e0_localUnique_sing` extends `g'` across the singular `κ z`
  obtain ⟨e, he, hsrc, heq⟩ :=
    e0_localUnique_sing U' hU'o hU'c (κ z) hy₀U' 0 le_rfl hy₀ g' hloc hinj hmaps
  have hy₀e : κ z ∈ e.source := hsrc mem_connectedComponent
  have hey₀ : e (κ z) ∈ e0SingY 0 := (e0_sing_mem e he (κ z) hy₀e 0 le_rfl).1 hy₀
  have hcl : κ z ∈ closure R' := e0_dense_regY.open_subset_closure_inter hU'o hy₀U'
  have hK : IsCompact (Sum.inr '' (c'.symm '' Metric.closedBall m₁ (ρ / 2)) : Set E0Y) :=
    ((isCompact_closedBall m₁ (ρ / 2)).image_of_continuousOn
      (c'.continuousOn_symm.mono hKt)).image continuous_inr
  have hsub : e '' R' ⊆ Sum.inr '' (c'.symm '' Metric.closedBall m₁ (ρ / 2)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← heq hy, hg' y hy]
    exact ⟨_, ⟨_, Metric.ball_subset_closedBall (hhO _ (hfO y hy)), rfl⟩, rfl⟩
  have hmem := closure_minimal hsub hK.isClosed (mem_closure_image (e.continuousAt hy₀e) hcl)
  obtain ⟨_, ⟨k, hk, rfl⟩, hek⟩ := hmem
  apply hey₀.2
  rw [← hek, inr_mem_e0Reg_iff]
  exact mem_support.2 ⟨c', hc', c'.map_target (hKt hk)⟩

/-! ### §4 The push-out of B21 Prop 2.17 and absolute maximality of `Reg M` -/

/-- **B21 Lemma 2.12** (`lem:extension_hausdorff`, `BTZ_1.tex:941–991`), in the case Prop 2.17
uses: `M₀ = Reg M`, `M₁ = M` (`Reg M ↪ M` is a BTZ-extension), `M₂ = N` a globally hyperbolic flat
spacetime (`sing₀ N = ∅ = j(sing₀ Reg M)`), `j = f`: the topological push-out
`(M ⊔ N)/Reg M` (`Causal.Gluing`) is Hausdorff. **Proved** (WP-43c, §4a): the graph of `f` is
closed (`Causal.Gluing.t2Space_iff`); a BTZ limit point is excluded by B21's monotone sequence,
the shrinking diamonds of `N` and the holonomy step `exists_nhds_not_mapsTo`. -/
theorem lem_extension_hausdorff {N : Causal.Flat.FlatSpacetime.{0} 2} (hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    T2Space (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) := by
  have hsfa := e0_sfa_of_globalBTZ M
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hT := Causal.Flat.flatCausality_tarentin (d := 2) (X := N)
  have hj₁ : IsOpenEmbedding (Subtype.val : E0LM.e0RegM M → M) :=
    (E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal
  rw [Causal.Gluing.t2Space_iff hj₁ hf.isOpenEmbedding]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [← closure_subset_iff_isClosed]
  rintro ⟨p, q⟩ hpq
  have hcl : GraphCluster f p q := by
    intro U hU V hV
    obtain ⟨_, ⟨hxU, hxV⟩, w, rfl⟩ := mem_closure_iff_nhds.1 hpq _ (prod_mem_nhds hU hV)
    exact ⟨w, hxU, hxV⟩
  by_cases hp : p ∈ E0LM.e0RegM M
  · -- a regular `p`: `q = f p` (continuity of `f`, Hausdorffness of `N`)
    refine ⟨⟨p, hp⟩, ?_⟩
    refine Prod.ext rfl ?_
    show f ⟨p, hp⟩ = q
    by_contra hne
    obtain ⟨V₁, V₂, hV₁, hV₂, h1, h2, hdis⟩ := t2_separation hne
    have hU : Subtype.val '' (f ⁻¹' V₁) ∈ 𝓝 p :=
      (hj₁.isOpenMap _ (hV₁.preimage hf.continuous)).mem_nhds ⟨⟨p, hp⟩, h1, rfl⟩
    obtain ⟨w, ⟨w', hw', hw'w⟩, hwV⟩ := hcl _ hU _ (hV₂.mem_nhds h2)
    have : w' = w := Subtype.ext hw'w
    subst this
    exact Set.disjoint_left.1 hdis hw' hwV
  · -- a BTZ `p` is impossible
    exfalso
    have hpS : p ∈ S0 M := by_contra fun h => hp h
    obtain ⟨b, hpb, hbb, hblim⟩ := exists_seq_lt_tendsto (M := M) (p := p)
    have hbreg : ∀ n, b n ∈ E0LM.e0RegM M := fun n => notMem_sing_of_lt hsfa (hpb n)
    set y : ℕ → N := fun n => f ⟨b n, hbreg n⟩ with hy
    have hyy : ∀ n, (Causal.Flat.flatCausality 2 N).le ⊤ (y (n + 1)) (y n) := fun n =>
      (Causal.Flat.flatCausality 2 N).le_of_lt
        (lt_image_of_lt hf (w := ⟨b (n + 1), hbreg (n + 1)⟩) (x := ⟨b n, hbreg n⟩) (hbb n))
    have hymono : ∀ m n, m ≤ n → (Causal.Flat.flatCausality 2 N).le ⊤ (y n) (y m) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact (Causal.Flat.flatCausality 2 N).le_refl trivial
      | succ n _ ih => exact (Causal.Flat.flatCausality 2 N).le_trans (hyy n) ih
    have hqy : ∀ n, (Causal.Flat.flatCausality 2 N).le ⊤ q (y n) := fun n =>
      le_image_of_graphCluster hN hf hcl (x := ⟨b n, hbreg n⟩) (hpb n)
    -- the cluster point `q'` of the decreasing `f(bₙ)`
    obtain ⟨q', -, hq'⟩ := (hN'.2 q (y 0)).exists_mapClusterPt (f := atTop) (u := y)
      (by
        rw [le_principal_iff, mem_map]
        exact univ_mem' fun n =>
          Causal.Causality.mem_diamond.2 ⟨hqy n, hymono 0 n (Nat.zero_le n)⟩)
    have hq'y : ∀ n, (Causal.Flat.flatCausality 2 N).le ⊤ q' (y n) := fun n =>
      Causal.Precausality.mem_Jminus_singleton.1 (mem_of_mapClusterPt_of_eventually
        (hN'.isClosed_Jminus_singleton hT (y n)) hq'
        (eventually_atTop.2 ⟨n, fun m hm =>
          Causal.Precausality.mem_Jminus_singleton.2 (hymono n m hm)⟩))
    have hcl' : GraphCluster f p q' := by
      intro U hU V hV
      obtain ⟨n, hn1, hn2⟩ :=
        ((mapClusterPt_iff_frequently.1 hq' V hV).and_eventually (hblim.eventually hU)).exists
      exact ⟨⟨b n, hbreg n⟩, hn2, hn1⟩
    -- the neighbourhood `O` of `q'` of the holonomy step
    obtain ⟨O, hO, hOz⟩ := exists_nhds_not_mapsTo hf q'
    -- some diamond `J(q', f bₙ)` lies in `O`
    obtain ⟨n, hn⟩ : ∃ n, (Causal.Flat.flatCausality 2 N).diamond ⊤ q' (y n) ⊆ O := by
      set D : ℕ → Set N := fun n => (Causal.Flat.flatCausality 2 N).diamond ⊤ q' (y n) with hD
      have hDsub : ∀ m n, m ≤ n → D n ⊆ D m := fun m n hmn x hx =>
        Causal.Causality.mem_diamond.2 ⟨(Causal.Causality.mem_diamond.1 hx).1,
          (Causal.Flat.flatCausality 2 N).le_trans (Causal.Causality.mem_diamond.1 hx).2
            (hymono m n hmn)⟩
      have hint : D 0 ∩ ⋂ i, (D i ∩ (interior O)ᶜ) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
        have hxi := mem_iInter.1 hx.2
        have hle : ∀ i, (Causal.Flat.flatCausality 2 N).le ⊤ x (y i) := fun i =>
          (Causal.Causality.mem_diamond.1 (hxi i).1).2
        have hxq : (Causal.Flat.flatCausality 2 N).le ⊤ x q' :=
          Causal.Precausality.mem_Jplus_singleton.1 (mem_of_mapClusterPt_of_eventually
            (hN'.isClosed_Jplus_singleton hT x) hq'
            (Eventually.of_forall fun i => Causal.Precausality.mem_Jplus_singleton.2 (hle i)))
        have hxe : x = q' := hN'.1 hxq (Causal.Causality.mem_diamond.1 (hxi 0).1).1
        exact (hxi 0).2 (hxe ▸ mem_interior_iff_mem_nhds.2 hO)
      obtain ⟨u, hu⟩ := (hN'.2 q' (y 0)).elim_finite_subfamily_closed
        (fun i => D i ∩ (interior O)ᶜ)
        (fun i => (hN'.2 q' (y i)).isClosed.inter isOpen_interior.isClosed_compl) hint
      refine ⟨u.sup id, fun x hx => ?_⟩
      by_contra hxO
      have hxO' : x ∉ interior O := fun h => hxO (interior_subset h)
      have hmem : x ∈ D 0 ∩ ⋂ i ∈ u, (D i ∩ (interior O)ᶜ) :=
        ⟨hDsub 0 _ (Nat.zero_le _) hx, mem_iInter₂.2 fun i hi =>
          ⟨hDsub i _ (Finset.le_sup (f := id) hi) hx, hxO'⟩⟩
      rw [hu] at hmem
      exact hmem
    -- a BTZ point `z` above `p` in `I⁻(bₙ)`, and a neighbourhood whose regular part is in
    -- `I⁺(p) ∩ I⁻(bₙ)`
    obtain ⟨z, hzI, hzS, hpz, hzp⟩ := exists_sing_above hpS
      ((CE M).isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 (hpb n)))
    obtain ⟨V₁, hV₁, hV₁I⟩ := exists_nhds_diff_sing_subset_Iplus hsfa hpS hzS hpz hzp.symm
    obtain ⟨w, hwV, hwO⟩ := hOz z hzS (V₁ ∩ (CE M).Iminus ⊤ {b n})
      (inter_mem hV₁ ((CE M).isOpen_Iminus.mem_nhds hzI))
    have hpw : (CE M).lt ⊤ p w := Causal.Precausality.mem_Iplus_singleton.1 (hV₁I ⟨hwV.1, w.2⟩)
    have hwb : (CE M).lt ⊤ (w : M) (b n) := Causal.Precausality.mem_Iminus_singleton.1 hwV.2
    exact hwO (hn (Causal.Causality.mem_diamond.2 ⟨le_image_of_graphCluster hN hf hcl' hpw,
      (Causal.Flat.flatCausality 2 N).le_of_lt (lt_image_of_lt hf (x := ⟨b n, hbreg n⟩) hwb)⟩))

/-! ### §4b A flat spacetime as an `𝔼₀`-manifold, and the `𝔼₀`-atlas of the push-out -/

/-- **A flat spacetime read as an `𝔼₀`-manifold** (the type `N`, its charts followed by
`inl : 𝕄 → Y = 𝕄 ⊕ 𝔼₀`). -/
def FlatE0 (N : Causal.Flat.FlatSpacetime.{0} 2) : Type := N

namespace FlatE0

variable (N : Causal.Flat.FlatSpacetime.{0} 2)

instance instTop : TopologicalSpace (FlatE0 N) := inferInstanceAs (TopologicalSpace N)
instance instT2 : T2Space (FlatE0 N) := inferInstanceAs (T2Space N)
instance instConn : ConnectedSpace (FlatE0 N) := inferInstanceAs (ConnectedSpace N)
instance instSC : SecondCountableTopology (FlatE0 N) :=
  inferInstanceAs (SecondCountableTopology N)
instance instNonempty : Nonempty (FlatE0 N) := inferInstanceAs (Nonempty N)

noncomputable instance instCharted : ChartedSpace E0Y (FlatE0 N) where
  atlas := (fun e : OpenPartialHomeomorph N (Causal.Minkowski 2) => e.trans e0Inl) ''
    atlas (Causal.Minkowski 2) N
  chartAt y := (chartAt (Causal.Minkowski 2) (show N from y)).trans e0Inl
  mem_chart_source y := by
    simp only [OpenPartialHomeomorph.trans_source, e0Inl_source, preimage_univ, inter_univ]
    exact mem_chart_source (Causal.Minkowski 2) (show N from y)
  chart_mem_atlas y := ⟨_, chart_mem_atlas _ _, rfl⟩

end FlatE0

/-- The conjugate `inl ∘ t ∘ inl⁻¹` of an element of the flat groupoid is a.e. regular at every
point of its source. -/
theorem e0RegAt_inlConj {t : OpenPartialHomeomorph (Causal.Minkowski 2) (Causal.Minkowski 2)}
    (ht : t ∈ Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) :
    ∀ x ∈ (e0Inl.symm.trans (t.trans e0Inl)).source,
      E0RegAt (e0Inl.symm.trans (t.trans e0Inl)) x := by
  intro x hx
  have hx' := hx
  simp only [OpenPartialHomeomorph.trans_source, e0Inl_source, preimage_univ, inter_univ,
    mem_inter_iff, mem_preimage] at hx'
  obtain ⟨⟨m, -, rfl⟩, hm⟩ := hx'
  rw [e0Inl_symm_inl] at hm
  refine e0RegAt_of_exists ((e0Inl.symm.trans (t.trans e0Inl)).continuousAt hx)
    ⟨e0Inl.symm, e0Inl_symm_mem_e0Atlas, e0Inl.symm, e0Inl_symm_mem_e0Atlas,
      by rw [e0Inl_symm_source]; exact ⟨m, rfl⟩, ?_, ?_⟩
  · rw [e0Inl_symm_source]
    exact ⟨t m, by simp [OpenPartialHomeomorph.coe_trans]⟩
  · obtain ⟨g, hg⟩ := (Causal.mem_gxGroupoid_iff.1 ht).1 m hm
    refine ⟨g, ?_⟩
    rw [← IsOpenEmbedding.inl.map_nhds_eq m, eventually_map]
    filter_upwards [hg] with m' hm'
    simp [OpenPartialHomeomorph.coe_trans, hm']

/-- **`inl ∘ t ∘ inl⁻¹ ∈ G`** for `t` in the flat groupoid. -/
theorem inlConj_mem {t : OpenPartialHomeomorph (Causal.Minkowski 2) (Causal.Minkowski 2)}
    (ht : t ∈ Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) :
    e0Inl.symm.trans (t.trans e0Inl) ∈ e0Groupoid := by
  have hsymm : (e0Inl.symm.trans (t.trans e0Inl)).symm = e0Inl.symm.trans (t.symm.trans e0Inl) := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
  refine mem_e0Groupoid_iff.2 ⟨e0RegAt_inlConj ht, fun x hx => ?_⟩
  rw [← OpenPartialHomeomorph.symm_source, hsymm] at hx
  rw [hsymm]
  exact e0RegAt_inlConj ((Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)).symm ht) x hx

instance FlatE0.instHasGroupoid (N : Causal.Flat.FlatSpacetime.{0} 2) :
    HasGroupoid (FlatE0 N) e0Groupoid where
  compatible := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    have h := inlConj_mem (HasGroupoid.compatible (G := Causal.gxGroupoid (Causal.Flat.isom 2)
      (Causal.Minkowski 2)) hc hc')
    have e : (c.trans e0Inl).symm.trans (c'.trans e0Inl) =
        e0Inl.symm.trans ((c.symm.trans c').trans e0Inl) := by
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
    show (c.trans e0Inl).symm.trans (c'.trans e0Inl) ∈ e0Groupoid
    exact e ▸ h

/-- The chart of `N` at `y`, as a chart of the type `FlatE0 N`. -/
noncomputable def FlatE0.chart (N : Causal.Flat.FlatSpacetime.{0} 2) (y : N) :
    OpenPartialHomeomorph (FlatE0 N) (Causal.Minkowski 2) :=
  chartAt (M := N) (Causal.Minkowski 2) y

/-- The chart of `N` at `y` is a chart isomorphism of the charted causality of `FlatE0 N`: it is
the chart of `FlatE0 N` at `y` followed by `inl⁻¹`. -/
theorem flatE0_chartIso (N : Causal.Flat.FlatSpacetime.{0} 2) (y : N) :
    Causal.ChartIso (CE (FlatE0 N)) (Causal.minkowski 2) (FlatE0.chart N y) := by
  have h := E0.chartIso_trans
    (Causal.CBG.chartedCausality_chartIso (M := FlatE0 N) E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ (show FlatE0 N from y))
    (E0.chartIso_e0Atlas e0Inl_symm_mem_e0Atlas)
  have e : (chartAt E0Y (show FlatE0 N from y)).trans e0Inl.symm = FlatE0.chart N y := by
    refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun x => ?_) ?_
    · show e0Inl.symm (e0Inl (FlatE0.chart N y x)) = _
      rw [e0Inl_apply, e0Inl_symm_inl]
    · show (FlatE0.chart N y).symm (e0Inl.symm (e0Inl x)) = _
      rw [e0Inl_apply, e0Inl_symm_inl]
    · show ((FlatE0.chart N y).trans e0Inl).source ∩
          ((FlatE0.chart N y).trans e0Inl) ⁻¹' e0Inl.symm.source = _
      rw [e0Inl_symm_source]
      ext x
      simp [OpenPartialHomeomorph.coe_trans]
  rw [e] at h
  exact h

/-- **The charted causality of `FlatE0 N` is the flat causality of `N`** (on every open set; the
two are absolutely minimal and agree on every chart domain, as in
`Causal.Flat.chartedCausality_eq_flatCausality`). -/
theorem flatE0_rel_iff (N : Causal.Flat.FlatSpacetime.{0} 2) (V : Opens N) (x y : N) :
    ((CE (FlatE0 N)).le V x y ↔ (Causal.Flat.flatCausality 2 N).le V x y) ∧
      ((CE (FlatE0 N)).lt V x y ↔ (Causal.Flat.flatCausality 2 N).lt V x y) := by
  set C₁ : Causal.Causality N := CE (FlatE0 N) with hC₁
  have hagree : ∀ z : N, Causal.AgreeOn C₁ (Causal.Flat.flatCausality 2 N)
      (Causal.chartSource (chartAt (Causal.Minkowski 2) z)) := fun z W hW a b =>
    (flatE0_chartIso N z).agree (Causal.Flat.flatCausality_chartIso_chartAt z) hW a b
  have hA1 : C₁.AbsolutelyMinimalOn ⊤ :=
    Causal.CBG.chartedCausality_absolutelyMinimalOn (M := FlatE0 N) E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ ⊤
  have hA2 := Causal.Flat.flatCausality_absolutelyMinimalOn (d := 2) (M := N) ⊤
  have i1 := Causal.imp_of_agree_locally hA1 (fun z _ => ⟨_, mem_chart_source _ z, hagree z⟩)
    (le_top : V ≤ ⊤) (x := x) (y := y)
  have i2 := Causal.imp_of_agree_locally hA2
    (fun z _ => ⟨_, mem_chart_source _ z, (hagree z).symm⟩) (le_top : V ≤ ⊤) (x := x) (y := y)
  exact ⟨⟨i1.1, i2.1⟩, ⟨i1.2, i2.2⟩⟩

/-- A map of `Y` which near `y₀` (on `s`) reads `c₂⁻¹ ∘ (g • ·) ∘ c₁` for two regular charts is a
local `G`-structomorphism at `y₀`. -/
theorem isLocalStructomorphWithinAt_of_eventually {Φ : E0Y → E0Y} {s : Set E0Y} {y₀ : E0Y}
    {c₁ c₂ : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} (hc₁ : c₁ ∈ e0Atlas)
    (hc₂ : c₂ ∈ e0Atlas) (g : Causal.Flat.isom 2) (hy₀ : y₀ ∈ c₁.source)
    (hg : g • c₁ y₀ ∈ c₂.target) (hΦ : ∀ᶠ y in 𝓝 y₀, y ∈ s → Φ y = c₂.symm (g • c₁ y)) :
    e0Groupoid.IsLocalStructomorphWithinAt Φ s y₀ := by
  intro _
  set σ : OpenPartialHomeomorph E0Y E0Y :=
    c₁.trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans c₂.symm) with hσ
  have hσsrc : ∀ y, y ∈ σ.source ↔ y ∈ c₁.source ∧ g • c₁ y ∈ c₂.target := by
    intro y; simp [σ]
  have hσapp : ∀ y, σ y = c₂.symm (g • c₁ y) := fun y => rfl
  have hσmem : σ ∈ e0Groupoid := by
    refine mem_e0Groupoid_of_chart_eq hc₁ hc₂ (fun y hy => ((hσsrc y).1 hy).1) ?_ g ?_
    · intro y hy
      have hs := σ.map_target hy
      rw [← σ.right_inv hy, hσapp]
      exact c₂.map_target ((hσsrc _).1 hs).2
    · intro y hy
      rw [hσapp, c₂.right_inv ((hσsrc y).1 hy).2]
  refine ⟨σ.restr (interior {y | y ∈ s → Φ y = c₂.symm (g • c₁ y)}),
    closedUnderRestriction' hσmem isOpen_interior, ?_, ?_⟩
  · rintro y ⟨hys, hye⟩
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_interior] at hye
    show Φ y = σ y
    rw [hσapp]
    exact (interior_subset hye.2 : y ∈ {y | y ∈ s → Φ y = c₂.symm (g • c₁ y)}) hys
  · rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_interior]
    exact ⟨(hσsrc y₀).2 ⟨hy₀, hg⟩, mem_interior_iff_mem_nhds.2 hΦ⟩

omit [SecondCountableTopology M] in
/-- **An isometric embedding of `Reg M` read in the charts of `M`**: near a regular `w`,
`chart_N(f w) ∘ f = γ • ρ_w ∘ chart_M(w)`, `ρ_w = regAtlasChart w`. -/
theorem exists_eventually_chart_eq {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) (w : E0LM.e0RegM M) :
    ∃ γ : Causal.Flat.isom 2, ∀ᶠ m in 𝓝 (w : M), ∀ hm : m ∈ E0LM.e0RegM M,
      chartAt (Causal.Minkowski 2) (f w) (f ⟨m, hm⟩) =
        γ • E0LM.regAtlasChart w (chartAt E0Y (w : M) m) := by
  obtain ⟨γ, hγ⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hf.1).2 w
  refine ⟨γ, ?_⟩
  have hmap := ((E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq w
  rw [← hmap, eventually_map]
  filter_upwards [hγ] with w' hw' hm'
  exact hw'

open Classical in
/-- `f : Reg M → N` extended to `M` by a point `y₀` off `Reg M`, as a map into `FlatE0 N`. -/
noncomputable def regExt {N : Causal.Flat.FlatSpacetime.{0} 2} (f : e0RegMFlat M → N) (y₀ : N) :
    M → FlatE0 N :=
  fun m => if hm : m ∈ E0LM.e0RegM M then f ⟨m, hm⟩ else y₀

omit [SecondCountableTopology M] in
theorem regExt_apply {N : Causal.Flat.FlatSpacetime.{0} 2} (f : e0RegMFlat M → N) (y₀ : N)
    (m : M) (hm : m ∈ E0LM.e0RegM M) : regExt f y₀ m = f ⟨m, hm⟩ := by
  simp [regExt, hm]

omit [SecondCountableTopology M] in
/-- **`f` is an `𝔼₀`-morphism `Reg M → FlatE0 N`.** -/
theorem isE0Mor_regExt {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) (y₀ : N) :
    IsE0Mor (regExt f y₀) (E0LM.e0RegM M) := by
  intro x hx
  set w : E0LM.e0RegM M := ⟨x, hx⟩ with hw
  have hj : IsOpenEmbedding (Subtype.val : E0LM.e0RegM M → M) :=
    (E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal
  refine ⟨?_, ?_⟩
  · have hcomp : regExt f y₀ ∘ Subtype.val = fun w' : E0LM.e0RegM M => (f w' : FlatE0 N) := by
      funext w'; exact regExt_apply f y₀ w' w'.2
    have : ContinuousAt (regExt f y₀ ∘ Subtype.val) w := by
      rw [hcomp]; exact hf.continuous.continuousAt
    exact (hj.continuousAt_iff.1 this).continuousWithinAt
  · set κ := chartAt E0Y x with hκ
    have hxκ : x ∈ κ.source := mem_chart_source E0Y x
    obtain ⟨γ, hγ⟩ := exists_eventually_chart_eq hf w
    have hρ := E0LM.regAtlasChart_mem w
    have hx₀ : κ x ∈ (E0LM.regAtlasChart w).source := E0LM.mem_regAtlasChart_source w
    have hFx : regExt f y₀ x = f w := regExt_apply f y₀ x hx
    rw [hFx]
    refine isLocalStructomorphWithinAt_of_eventually hρ e0Inl_symm_mem_e0Atlas γ hx₀
      (by rw [OpenPartialHomeomorph.symm_target, e0Inl_source]; exact mem_univ _) ?_
    have hc := κ.continuousAt_symm (κ.map_source hxκ)
    rw [ContinuousAt, κ.left_inv hxκ] at hc
    filter_upwards [κ.open_target.mem_nhds (κ.map_source hxκ), hc.eventually hγ] with y hyt hy hys
    have hys' : κ.symm y ∈ E0LM.e0RegM M := hys
    show e0Inl (chartAt (Causal.Minkowski 2) (f w) (regExt f y₀ (κ.symm y))) = _
    rw [regExt_apply f y₀ _ hys', hy hys', κ.right_inv hyt]
    rfl

/-- A point of `e0RegMFlat M`, as a point of `Reg M`. -/
abbrev toRegM (w : e0RegMFlat M) : E0LM.e0RegM M := w

/-- The inverse of `f` on its range, as a map `FlatE0 N → M`. -/
noncomputable def regInv {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) : FlatE0 N → M :=
  fun n => (toRegM ((hf.isOpenEmbedding.toOpenPartialHomeomorph f).symm n) : M)

omit [SecondCountableTopology M] in
theorem regInv_apply {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) (w : E0LM.e0RegM M) : regInv hf (f w) = w := by
  show (toRegM ((hf.isOpenEmbedding.toOpenPartialHomeomorph f).symm (f w)) : M) = w
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

omit [SecondCountableTopology M] in
/-- **`f⁻¹` is an `𝔼₀`-morphism `f(Reg M) → M`.** -/
theorem isE0Mor_regInv {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    IsE0Mor (regInv hf) (range f : Set N) := by
  set fe := hf.isOpenEmbedding.toOpenPartialHomeomorph f with hfe
  have hfet : fe.target = range f := IsOpenEmbedding.toOpenPartialHomeomorph_target _ _
  have hinv : ∀ n ∈ range f, f (fe.symm n) = n := fun n hn => fe.right_inv (hfet ▸ hn)
  rintro _ ⟨w₀, rfl⟩
  set w : E0LM.e0RegM M := toRegM w₀ with hw
  refine ⟨?_, ?_⟩
  · have : ContinuousOn (fun n : N => (toRegM (fe.symm n) : M)) (range f) :=
      continuous_subtype_val.comp_continuousOn (hfet ▸ fe.continuousOn_symm)
    exact this _ ⟨w, rfl⟩
  · set χ := chartAt (Causal.Minkowski 2) (f w) with hχ
    set κ := chartAt E0Y (w : M) with hκ
    set ρ := E0LM.regAtlasChart w with hρdef
    obtain ⟨γ, hγ⟩ := exists_eventually_chart_eq hf w
    have hρ := E0LM.regAtlasChart_mem w
    have hw0 := hγ.self_of_nhds w.2
    have hρw : κ w ∈ ρ.source := E0LM.mem_regAtlasChart_source w
    rw [regInv_apply]
    have hy0 : chartAt E0Y (show FlatE0 N from f w) (f w) = Sum.inl (χ (f w)) := rfl
    rw [hy0]
    refine isLocalStructomorphWithinAt_of_eventually e0Inl_symm_mem_e0Atlas hρ γ⁻¹
      (by rw [e0Inl_symm_source]; exact ⟨_, rfl⟩) ?_ ?_
    · rw [e0Inl_symm_inl]
      have e1 : γ⁻¹ • χ (f w) = ρ (κ w) := by
        rw [show f w = f ⟨(w : M), w.2⟩ from rfl, hw0, inv_smul_smul]
      rw [e1]; exact ρ.map_source hρw
    · -- the eventual identity, from `M` to `N` to `Y`
      have hQ : ∀ᶠ m in 𝓝 (w : M), κ m ∈ ρ.source ∧ ∀ hm : m ∈ E0LM.e0RegM M,
          χ (f ⟨m, hm⟩) = γ • ρ (κ m) := by
        filter_upwards [(κ.continuousAt (mem_chart_source E0Y (w : M))).eventually
          (ρ.open_source.mem_nhds hρw), hγ] with m h1 h2
        exact ⟨h1, h2⟩
      have hQN : ∀ᶠ n in 𝓝 (f w), κ (regInv hf n) ∈ ρ.source ∧
          ∀ hm : regInv hf n ∈ E0LM.e0RegM M,
            χ (f ⟨regInv hf n, hm⟩) = γ • ρ (κ (regInv hf n)) := by
        have hc : ContinuousAt (regInv hf) (f w) := by
          have := (continuous_subtype_val.continuousAt).comp
            (fe.continuousAt_symm (by rw [hfet]; exact ⟨w, rfl⟩))
          exact this
        have hc' := hc.tendsto
        rw [regInv_apply] at hc'
        exact hc'.eventually hQ
      set Ψ := chartAt E0Y (show FlatE0 N from f w) with hΨ
      have hΨt : Sum.inl (χ (f w)) ∈ Ψ.target := Ψ.map_source (mem_chart_source E0Y _)
      have hcΨ := Ψ.continuousAt_symm hΨt
      have hΨl : Ψ.symm (Sum.inl (χ (f w))) = f w := Ψ.left_inv (mem_chart_source E0Y _)
      rw [ContinuousAt, hΨl] at hcΨ
      filter_upwards [Ψ.open_target.mem_nhds hΨt, hcΨ.eventually hQN] with y hyt hy hyr
      obtain ⟨h1, h2⟩ := hy
      obtain ⟨w₁, hw'⟩ := hyr
      set w' : E0LM.e0RegM M := toRegM w₁ with hw'def
      have hn : regInv hf (Ψ.symm y) = w' := by rw [← hw', regInv_apply]
      have hfw' : f ⟨regInv hf (Ψ.symm y), by rw [hn]; exact w'.2⟩ = Ψ.symm y := by
        have : (⟨regInv hf (Ψ.symm y), by rw [hn]; exact w'.2⟩ : E0LM.e0RegM M) = w' :=
          Subtype.ext hn
        rw [this]; exact hw'
      have hχy : χ (Ψ.symm y) = e0Inl.symm y := by
        have hy' : Ψ (Ψ.symm y) = y := Ψ.right_inv hyt
        calc χ (Ψ.symm y) = e0Inl.symm (e0Inl (χ (Ψ.symm y))) := (e0Inl_symm_inl _).symm
          _ = e0Inl.symm (Ψ (Ψ.symm y)) := rfl
          _ = e0Inl.symm y := by rw [hy']
      have h3 := h2 (by rw [hn]; exact w'.2)
      rw [hfw', hχy] at h3
      show κ (regInv hf (Ψ.symm y)) = ρ.symm (γ⁻¹ • e0Inl.symm y)
      rw [h3, inv_smul_smul, ρ.left_inv h1]

/-- The two pieces of the push-out `(M ⊔ N)/Reg M`: `true ↦ M`, `false ↦ FlatE0 N`. -/
def pushPiece (M : Type) (N : Causal.Flat.FlatSpacetime.{0} 2) : Bool → Type
  | true => M
  | false => FlatE0 N

instance pushPiece.instTop (M : Type) [TopologicalSpace M] (N : Causal.Flat.FlatSpacetime.{0} 2) :
    ∀ b, TopologicalSpace (pushPiece M N b)
  | true => inferInstanceAs (TopologicalSpace M)
  | false => inferInstanceAs (TopologicalSpace (FlatE0 N))

instance pushPiece.instNonempty (M : Type) [Nonempty M] (N : Causal.Flat.FlatSpacetime.{0} 2) :
    ∀ b, Nonempty (pushPiece M N b)
  | true => inferInstanceAs (Nonempty M)
  | false => inferInstanceAs (Nonempty (FlatE0 N))

noncomputable instance pushPiece.instCharted (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M]
    (N : Causal.Flat.FlatSpacetime.{0} 2) : ∀ b, ChartedSpace E0Y (pushPiece M N b)
  | true => inferInstanceAs (ChartedSpace E0Y M)
  | false => inferInstanceAs (ChartedSpace E0Y (FlatE0 N))

instance pushPiece.instHasGroupoid (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid] (N : Causal.Flat.FlatSpacetime.{0} 2) :
    ∀ b, HasGroupoid (pushPiece M N b) e0Groupoid
  | true => inferInstanceAs (HasGroupoid M e0Groupoid)
  | false => inferInstanceAs (HasGroupoid (FlatE0 N) e0Groupoid)

/-- The two embeddings of the pieces into the topological push-out. -/
noncomputable def pushEmb {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid] [T2Space M] [ConnectedSpace M] {N : Causal.Flat.FlatSpacetime.{0} 2}
    (f : e0RegMFlat M → N) :
    ∀ b, pushPiece M N b → Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f
  | true => Causal.Gluing.ι₁ _ f
  | false => Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f

/-- **The push-out of B21 Prop 2.17's proof** (`BTZ_1.tex:1094–1096`, via Lemma 2.12
`lem:extension_hausdorff`): for an isometric embedding `f : Reg M → N` into a flat spacetime, an
`𝔼₀`-manifold `M̄` (Hausdorff, connected, second countable) with an injective `𝔼₀`-morphism
`ι₁ : M → M̄` and an open embedding `ι₂ : N → M̄` (itself an `𝔼₀`-morphism on `FlatE0 N`,
`isE0Mor_ι₂`, T-gx-btz-cleanup) agreeing on `Reg M`, jointly onto, identifying only along `f`,
with `sing₀(M̄) = ι₁(sing₀ M)` and the flat causality of `N` read through `ι₂`.

The structure stands after `FlatE0`, whose `𝔼₀`-atlas `isE0Mor_ι₂` is read in. -/
structure E0Pushout (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] (N : Causal.Flat.FlatSpacetime.{0} 2)
    (f : e0RegMFlat M → N) where
  /-- The push-out `M̄ = (M ⊔ N)/Reg M`. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [conn : ConnectedSpace carrier]
  [sc : SecondCountableTopology carrier]
  [cs : ChartedSpace E0Y carrier]
  [gx : HasGroupoid carrier e0Groupoid]
  /-- `π₁ : M → M̄`. -/
  ι₁ : M → carrier
  /-- `π₂ : N → M̄`. -/
  ι₂ : N → carrier
  isE0Mor_ι₁ : IsE0Mor ι₁ univ
  injective_ι₁ : Injective ι₁
  isOpenEmbedding_ι₂ : IsOpenEmbedding ι₂
  /-- `ι₂` read on `FlatE0 N` (the atlas of `N` through `inl`) is an `𝔼₀`-morphism. -/
  isE0Mor_ι₂ : IsE0Mor (fun y : FlatE0 N => ι₂ y) univ
  comm : ∀ w : E0LM.e0RegM M, ι₁ w = ι₂ (f w)
  cover : ∀ z, (∃ x, ι₁ x = z) ∨ ∃ y, ι₂ y = z
  glue : ∀ x y, ι₁ x = ι₂ y → ∃ w : E0LM.e0RegM M, (w : M) = x ∧ f w = y
  sing_ι₁ : ∀ x, ι₁ x ∈ S0 carrier ↔ x ∈ S0 M
  sing_ι₂ : ∀ y, ι₂ y ∉ S0 carrier
  le_ι₂ : ∀ U : Opens carrier, (U : Set carrier) = range ι₂ → ∀ y y',
    (CE carrier).le U (ι₂ y) (ι₂ y') ↔ (Causal.Flat.flatCausality 2 N).le ⊤ y y'

attribute [instance] E0Pushout.top E0Pushout.t2 E0Pushout.conn E0Pushout.sc E0Pushout.cs
  E0Pushout.gx


/-- **The push-out exists** (B21 Prop 2.17, l.1094–1096): Lemma 2.12 makes `(M ⊔ N)/Reg M`
Hausdorff, and the atlases of `M` and of `N` (read in `Y = 𝕄 ⊕ 𝔼₀` through `inl`, `FlatE0`)
descend. **Proved** (WP-43c, §4b): `Causal.CBG.gluedChartedSpace` along `ι₁`, `ι₂`, its transitions
`f` (`isE0Mor_regExt`) and `f⁻¹` (`isE0Mor_regInv`); `le_ι₂` from `flatE0_rel_iff`. -/
theorem exists_e0Pushout {N : Causal.Flat.FlatSpacetime.{0} 2}
    (hN : Causal.Flat.GH N) {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    Nonempty (E0Pushout M N f) := by
  haveI hT2 := lem_extension_hausdorff hN hf
  have hj₁ : IsOpenEmbedding (Subtype.val : E0LM.e0RegM M → M) :=
    (E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal
  have hj₂ := hf.isOpenEmbedding
  have hinj₁ : Injective (Subtype.val : E0LM.e0RegM M → M) := Subtype.val_injective
  have he : ∀ b, IsOpenEmbedding (pushEmb f b) := by
    intro b; cases b
    · exact Causal.Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
    · exact Causal.Gluing.isOpenEmbedding_ι₁ hj₁ hj₂
  have hcov : ∀ z, ∃ b, z ∈ range (pushEmb f b) := by
    intro z
    rcases Causal.Gluing.exists_ι z with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨true, x, hx⟩
    · exact ⟨false, y, hy⟩
  have htrans : ∀ i j, ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt
      (Causal.CBG.glueTransition he i j) (pushEmb f i ⁻¹' range (pushEmb f j)) :=
    GluingTrans.liftPropOn_glueTransition_pair (X := pushPiece M N) (e := pushEmb f)
      (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f) he Causal.Gluing.ι₁_j₁
      (fun _ _ h => (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 h)
      (F := (regExt f (Classical.arbitrary N) : M → N))
      (by
        have h := isE0Mor_regExt hf (Classical.arbitrary N)
        rw [← Subtype.range_coe (s := (E0LM.e0RegM M : Set M))] at h
        exact h)
      (fun w => regExt_apply f _ w w.2) (isE0Mor_regInv hf) (regInv_apply hf)
  letI cs : ChartedSpace E0Y (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) :=
    Causal.CBG.gluedChartedSpace E0Y he hcov
  haveI gx : HasGroupoid (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) e0Groupoid :=
    Causal.CBG.gluedChartedSpace_hasGroupoid he hcov htrans
  have hι : ∀ b, IsE0Mor (pushEmb f b) univ := Causal.CBG.liftPropOn_glue he hcov htrans
  obtain ⟨x₀, hx₀⟩ := (E0LM.dense_e0RegM (M := M)).nonempty
  haveI hconn : ConnectedSpace (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) := by
    have h1 := isPreconnected_range
      (Causal.Gluing.continuous_ι₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f))
    have h2 := isPreconnected_range
      (Causal.Gluing.continuous_ι₂ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f))
    have h12 := IsPreconnected.union
      (s := range (Causal.Gluing.ι₁ (Subtype.val : E0LM.e0RegM M → M) f))
      (t := range (Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f))
      (Causal.Gluing.ι₁ _ f x₀) ⟨x₀, rfl⟩
      ⟨f ⟨x₀, hx₀⟩, (Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f)
        (⟨x₀, hx₀⟩ : E0LM.e0RegM M)).symm⟩ h1 h2
    have hU : (univ : Set (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f)) ⊆
        range (Causal.Gluing.ι₁ (Subtype.val : E0LM.e0RegM M → M) f) ∪
          range (Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f) := fun z _ =>
      (Causal.Gluing.exists_ι z).imp (fun ⟨x, hx⟩ => ⟨x, hx⟩) (fun ⟨y, hy⟩ => ⟨y, hy⟩)
    refine { isPreconnected_univ := ?_, toNonempty := ⟨Causal.Gluing.ι₁ _ f x₀⟩ }
    rw [← Set.eq_univ_of_univ_subset hU]
    exact h12
  haveI hsc : SecondCountableTopology (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) :=
    isQuotientMap_quot_mk.secondCountableTopology (Causal.Gluing.isOpenMap_mk hj₁ hj₂)
  refine ⟨{ carrier := Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f
            ι₁ := Causal.Gluing.ι₁ _ f
            ι₂ := Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f
            isE0Mor_ι₁ := hι true
            injective_ι₁ := Causal.Gluing.injective_ι₁ hinj₁ hf.2
            isOpenEmbedding_ι₂ := Causal.Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
            isE0Mor_ι₂ := hι false
            comm := fun w => Causal.Gluing.ι₁_j₁ w
            cover := Causal.Gluing.exists_ι
            glue := fun x y h => (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 h
            sing_ι₁ := fun x => (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem
              isOpen_univ (hι true) (mem_univ x) le_rfl).symm
            sing_ι₂ := fun y h => ?_
            le_ι₂ := fun U hU y y' => ?_ }⟩
  · have h' := (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem isOpen_univ (hι false)
      (mem_univ (show FlatE0 N from y)) le_rfl).2 h
    exact h'.2 (inl_mem_e0Reg _)
  · exact (le_iff_of_isE0Mor (hι false)
      (Causal.Gluing.injective_ι₂ hinj₁ hf.2) hU y y').trans (flatE0_rel_iff N ⊤ y y').1

omit [SecondCountableTopology M] in
/-- **The push-out's two pieces**: `ι₁(M)` is open and contains `sing₀(M̄)`; `ι₂(N)` is open, and
its complement consists of BTZ points. -/
theorem E0Pushout.pieces {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (P : E0Pushout M N f) :
    IsOpen (range P.ι₁) ∧ S0 P.carrier ⊆ range P.ι₁ ∧ (range P.ι₂)ᶜ ⊆ S0 P.carrier := by
  refine ⟨?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := (isEMorphismOn_of_isE0Mor (W := ⊤) P.isE0Mor_ι₁).isOpen_image ⊤ le_rfl
    rwa [Opens.coe_top, image_univ] at this
  · rcases P.cover z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨x, rfl⟩
    · exact absurd hz (P.sing_ι₂ y)
  · rcases P.cover z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · refine (P.sing_ι₁ x).2 (by_contra fun hx => hz ?_)
      exact ⟨f ⟨x, hx⟩, (P.comm ⟨x, hx⟩).symm⟩
    · exact absurd ⟨y, rfl⟩ hz

end E0

end E0AbsMax

/-! ### §4c The mixed diamonds of the push-out (WP-47f, DEC-126)

WP-47d's proof (`GX.BTZ.MixedDiamond` §0–§4), placed here above the leaf so that AbsMax
needs no import of a file that imports it (the two files would be circular). The namespace is
`GX.E0AbsMax.Mixed` so that `GX.BTZ.MixedDiamond` (which imports this file and keeps its
own copy in `GX.E0MixedDiamond`) still builds; at graduation its §0–§4 can be deleted and its §5
repointed here. Statements and proofs are WP-47d's, unchanged. -/

namespace E0AbsMax.Mixed

open scoped Real

/-! ### §0 A curve of a normed space that is locally affine with nonzero velocity diverges -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A locally affine curve with nonzero velocity has no limit at `+∞`.** If near every
`σ > σ₁` the curve `F` is `σ' ↦ F σ + (σ' − σ) • w` with `w ≠ 0` (the velocity may a priori vary
with `σ`), then the velocity is locally constant, hence constant on `]σ₁, +∞[`, so `F` is affine
there with nonzero velocity and diverges. -/
theorem affine_noLimit {F : ℝ → E} {σ₁ : ℝ}
    (hloc : ∀ σ, σ₁ < σ → ∃ w : E, w ≠ 0 ∧ ∀ᶠ σ' in 𝓝 σ, F σ' = F σ + (σ' - σ) • w)
    (L : E) : ¬ Tendsto F atTop (𝓝 L) := by
  intro hlim
  choose! w hw0 hw using hloc
  -- `F` has derivative `w σ'` at every `σ'` near `σ`
  have hder : ∀ σ, σ₁ < σ → ∀ᶠ σ' in 𝓝 σ, HasDerivAt F (w σ) σ' := by
    intro σ hσ
    filter_upwards [(hw σ hσ).eventually_nhds] with σ' hσ'
    have h1 : HasDerivAt (fun σ'' => F σ + (σ'' - σ) • w σ) (w σ) σ' := by
      have := (((hasDerivAt_id σ').sub_const σ).smul_const (w σ)).const_add (F σ)
      simpa using this
    exact h1.congr_of_eventuallyEq hσ'
  have hD : ∀ σ, σ₁ < σ → ∀ᶠ σ' in 𝓝 σ, deriv F σ' = w σ := fun σ hσ =>
    (hder σ hσ).mono fun σ' h => h.deriv
  -- the velocity `deriv F` is constant on `]σ₁, +∞[`
  have hDd : ∀ σ, σ₁ < σ → HasDerivAt (deriv F) 0 σ := fun σ hσ =>
    (hasDerivAt_const σ (w σ)).congr_of_eventuallyEq (hD σ hσ)
  have hconst : ∀ σ, σ₁ < σ → deriv F σ = deriv F (σ₁ + 1) := fun σ hσ =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hDd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hDd x hx).deriv) hσ (show σ₁ < σ₁ + 1 by linarith)
  set w₀ := deriv F (σ₁ + 1) with hw₀
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀, (hD (σ₁ + 1) (by linarith)).self_of_nhds]; exact hw0 _ (by linarith)
  have hFd : ∀ σ, σ₁ < σ → HasDerivAt F w₀ σ := fun σ hσ => by
    have h := (hder σ hσ).self_of_nhds
    rw [← hconst σ hσ, (hD σ hσ).self_of_nhds]; exact h
  -- `G = F − σ • w₀` is constant on `]σ₁, +∞[`
  set G : ℝ → E := fun σ => F σ - σ • w₀ with hG
  have hGd : ∀ σ, σ₁ < σ → HasDerivAt G 0 σ := fun σ hσ => by
    have := (hFd σ hσ).sub ((hasDerivAt_id σ).smul_const w₀)
    simp only [one_smul, sub_self] at this
    exact this
  have hGc : ∀ σ, σ₁ < σ → G σ = G (σ₁ + 1) := fun σ hσ =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hGd x hx).deriv) hσ (show σ₁ < σ₁ + 1 by linarith)
  -- so `‖F σ − G₀‖ = |σ| ‖w₀‖` diverges, against the limit
  have h1 : Tendsto (fun σ => ‖F σ - G (σ₁ + 1)‖) atTop (𝓝 ‖L - G (σ₁ + 1)‖) :=
    (hlim.sub_const _).norm
  have h2 : Tendsto (fun σ => ‖F σ - G (σ₁ + 1)‖) atTop atTop := by
    have h3 : Tendsto (fun σ : ℝ => σ * ‖w₀‖) atTop atTop :=
      tendsto_id.atTop_mul_const (norm_pos_iff.2 hw₀ne)
    refine h3.congr' (eventually_atTop.2 ⟨max σ₁ 0 + 1, fun σ hσ => ?_⟩)
    have hσ₁ : σ₁ < σ := by linarith [le_max_left σ₁ 0]
    have hσ0 : 0 ≤ σ := by linarith [le_max_right σ₁ 0]
    have : F σ - G (σ₁ + 1) = σ • w₀ := by
      rw [← hGc σ hσ₁, hG]; simp
    show σ * ‖w₀‖ = ‖F σ - G (σ₁ + 1)‖
    rw [this, norm_smul, Real.norm_of_nonneg hσ0]
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

end Affine

/-! ### §1 Spear charts in an `𝔼₀`-manifold, and their local isomorphism -/

section Chart

open E0CBG E0Spear E0

/-- **A spear chart of vertex `p`** (the data of B21 Def 2.1's spear neighbourhood, `E0Spear.IsSpearNbhd`,
transported to any `𝔼₀`-manifold `X`): an injective `𝔼₀`-morphism `φ` on an open `W ⊇ spearY v R`
sending the vertex `(v, 0)` to `p`. -/
structure SpearChart (X : Type) [TopologicalSpace X] [ChartedSpace E0Y X] (p : X) where
  v : ℝ
  R : ℝ
  pos : 0 < R
  W : Set E0Y
  φ : E0Y → X
  isOpen : IsOpen W
  sub : spearY v R ⊆ W
  mor : IsE0Mor φ W
  inj : InjOn φ W
  vertex : φ (yVertex v) = p

namespace SpearChart

variable {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X] {p : X} (S : SpearChart X p)

/-- The chart read in the paper's coordinates `(τ, z)`. -/
noncomputable def Φ (x : E0) : X := S.φ (paperInY x)

/-- Its domain in the paper's coordinates. -/
def O : Set E0 := paperInY ⁻¹' S.W

theorem isOpen_O : IsOpen S.O := S.isOpen.preimage continuous_paperInY

/-- `O` as an open set. -/
def OO : Opens E0 := ⟨S.O, S.isOpen_O⟩

theorem spear_subset_O {ρ : ℝ} (hρ : ρ ≤ S.R) : spear S.v ρ ⊆ S.O := fun x hx =>
  S.sub ⟨x, spear_mono le_rfl hρ hx, rfl⟩

theorem continuousOn_φ : ContinuousOn S.φ S.W := fun y hy => (S.mor y hy).continuousWithinAt

theorem continuousOn : ContinuousOn S.Φ S.O :=
  S.continuousOn_φ.comp continuous_paperInY.continuousOn fun _ hx => hx

theorem injOn : InjOn S.Φ S.O := fun x hx y hy h =>
  paperInY.injOn (by simp) (by simp) (S.inj hx hy h)

theorem Φ_vertex : S.Φ (S.v, 0) = p := S.vertex

variable [HasGroupoid X e0Groupoid]

/-- **Relations of the spear transfer to `X`.** -/
theorem le_of_le {x y : E0} (hx : x ∈ spear S.v S.R) (hy : y ∈ spear S.v S.R)
    (h : causality.le ⊤ x y) : (CE X).le ⊤ (S.Φ x) (S.Φ y) :=
  le_of_isE0Mor_paper S.isOpen S.mor (U := S.OO) subset_rfl
    (le_of_le_top_of_mem_spear (S.spear_subset_O le_rfl) hx hy h)

omit [HasGroupoid X e0Groupoid] in
/-- **The BTZ points of the chart are its axis points.** -/
theorem mem_S0_iff {x : E0} (hx : x ∈ S.O) : S.Φ x ∈ S0 X ↔ x ∈ axis := by
  have h := Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem S.isOpen S.mor hx
    (le_refl (0 : ℝ))
  show S.φ (paperInY x) ∈ _ ↔ _
  rw [← h]
  show chartAt E0Y (paperInY x) (paperInY x) ∈ e0SingY 0 ↔ _
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  constructor
  · intro h'
    by_contra hax
    exact h'.2 (paperInY_mem_e0Reg_iff.2 hax)
  · intro hax
    exact ⟨rfl, fun h' => paperInY_mem_e0Reg_iff.1 h' hax⟩

/-- The image of an open subset of `O` is open. -/
theorem isOpen_image {U : Set E0} (hU : IsOpen U) (hUO : U ⊆ S.O) : IsOpen (S.Φ '' U) := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨S.W, S.isOpen⟩) S.mor
  have h := hE.isOpen_image (Causal.chartImage paperInY ⟨U, hU⟩) (by
    intro y hy
    rw [← SetLike.mem_coe, Causal.coe_chartImage] at hy
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
    exact hUO hx)
  convert h using 1
  rw [Causal.coe_chartImage, paperInY_source, univ_inter, image_image]
  rfl

/-- **The local isomorphism of a spear chart** (`IsEMorphismOn.locally`, read in the paper's
coordinates): every point of `O` has an open neighbourhood `U₀ ⊆ O` such that, for every open
`U ⊆ U₀`, a relation of `X` inside `Φ(U)` between two points of `Φ(U)` is a relation of `𝔼₀`. -/
theorem exists_locIso {y₀ : E0} (hy₀ : y₀ ∈ S.O) :
    ∃ U₀ : Opens E0, y₀ ∈ U₀ ∧ (U₀ : Set E0) ⊆ S.O ∧ ∀ U : Opens E0, U ≤ U₀ →
      ∀ V : Opens X, (V : Set X) = S.Φ '' U → ∀ a ∈ U, ∀ b ∈ U,
        (CE X).le V (S.Φ a) (S.Φ b) → causality.le ⊤ a b := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨S.W, S.isOpen⟩) S.mor
  obtain ⟨V₀, hV₀W, hyV₀, -, hiso⟩ := hE.locally (paperInY y₀) hy₀
  refine ⟨⟨paperInY ⁻¹' V₀, V₀.isOpen.preimage continuous_paperInY⟩, hyV₀,
    fun x hx => hV₀W hx, fun U hU V hV a ha b hb hab => ?_⟩
  set V' : Opens E0Y := Causal.chartImage paperInY U with hV'
  have hV'V₀ : V' ≤ V₀ := by
    intro y hy
    rw [← SetLike.mem_coe, hV', Causal.coe_chartImage] at hy
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
    exact hU hx
  have hVimg : (V : Set X) = S.φ '' V' := by
    rw [hV, hV', Causal.coe_chartImage, paperInY_source, univ_inter, image_image]
    rfl
  have haV' : paperInY a ∈ V' := Causal.mem_chartImage_of_mem (by simp) ha
  have hbV' : paperInY b ∈ V' := Causal.mem_chartImage_of_mem (by simp) hb
  have h1 := ((hiso V' hV'V₀ V hVimg _ haV' _ hbV').1).2 hab
  have h2 := (ceY_le_iff haV' hbV').1 h1
  have h3 := ((chartIso_paperInY U (fun z _ => by simp [Causal.chartSource]) a ha b hb).1).2 h2
  exact causality.le_mono le_top h3

/-- **A causal curve of `X` inside the image of a local-isomorphism neighbourhood is a relation of
`𝔼₀`.** -/
theorem le_of_curve {U₀ : Opens E0} (hU₀O : (U₀ : Set E0) ⊆ S.O)
    (hU₀ : ∀ U : Opens E0, U ≤ U₀ → ∀ V : Opens X, (V : Set X) = S.Φ '' U → ∀ a ∈ U, ∀ b ∈ U,
      (CE X).le V (S.Φ a) (S.Φ b) → causality.le ⊤ a b)
    {c : ℝ → X} {s s' : ℝ} (hss' : s ≤ s') (hc : (CE X).CausalCurveOn ⊤ c s s')
    (hmem : ∀ σ ∈ Icc s s', c σ ∈ S.Φ '' U₀) {a b : E0} (ha : a ∈ U₀) (hb : b ∈ U₀)
    (hca : c s = S.Φ a) (hcb : c s' = S.Φ b) : causality.le ⊤ a b := by
  rcases hss'.eq_or_lt with h | h
  · subst h
    have : a = b := S.injOn (hU₀O ha) (hU₀O hb) (hca.symm.trans hcb)
    subst this
    exact causality.le_refl trivial
  set V : Opens X := ⟨S.Φ '' U₀, S.isOpen_image U₀.isOpen hU₀O⟩
  have hcV : (CE X).CausalCurveOn V c s s' := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
  have hle : (CE X).le V (c s) (c s') :=
    Causal.CurveOn.rel_of_lt (CE X).isRelFamily_le hcV le_rfl h le_rfl
  rw [hca, hcb] at hle
  exact hU₀ U₀ le_rfl V rfl a ha b hb hle

/-- **Exit from a truncated spear** (the curve-exit step of B21 l.1110–1113, repaired: the spear is
truncated at the lid `τ = T`, so that its image is compact, hence closed in `X`). Let
`𝒬 = spear(v, ρ) ∩ {τ ≤ T}`. A relation `Φ a ≤ b` from a point of `𝒬` to a point outside `Φ(𝒬)`
passes through a point `Φ e` of the wall `{r = ρ}` or of the lid `{τ = T}` of `𝒬`, with `a ≤ e` in
`𝔼₀`. Along a causal curve, the last point of the first stretch inside `Φ(𝒬)` is reached from `a`
inside `𝔼₀` (real induction with the local isomorphism `exists_locIso`); there, no point of the
interior or of the head can be left, since `f = τ − r/2` is non-decreasing. -/
theorem exit [T2Space X] {ρ T : ℝ} (hρ : ρ ≤ S.R) {a : E0}
    (ha : a ∈ spear S.v ρ ∩ {x : E0 | x.1 ≤ T}) {b : X}
    (hb : b ∉ S.Φ '' (spear S.v ρ ∩ {x : E0 | x.1 ≤ T})) (hab : (CE X).le ⊤ (S.Φ a) b) :
    ∃ e ∈ spear S.v ρ ∩ {x : E0 | x.1 ≤ T}, (rad e = ρ ∨ e.1 = T) ∧ causality.le ⊤ a e ∧
      (CE X).le ⊤ (S.Φ e) b := by
  set Q := spear S.v ρ ∩ {x : E0 | x.1 ≤ T} with hQ
  have hQc : IsCompact Q := isCompact_spear_inter_le _ _ _
  have hQO : Q ⊆ S.O := fun x hx => S.spear_subset_O hρ hx.1
  have hKc : IsCompact (S.Φ '' Q) := hQc.image_of_continuousOn (S.continuousOn.mono hQO)
  have hK : IsClosed (S.Φ '' Q) := hKc.isClosed
  obtain ⟨c, hc, hc0, hc1⟩ := (E0LM.e0_causallyArcConnected (M := X) ⊤ le_rfl _ _).1.1 hab
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn (CE X).isRelFamily_le
  -- the first exit time `s₁`
  set Sx : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ c s ∉ S.Φ '' Q} with hSx
  have h1S : (1 : ℝ) ∈ Sx := ⟨right_mem_Icc.2 zero_le_one, by rw [hc1]; exact hb⟩
  have hSne : Sx.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow Sx := ⟨0, fun t ht => ht.1.1⟩
  set s₁ := sInf Sx with hs₁
  have hs₁0 : 0 ≤ s₁ := le_csInf hSne fun t ht => ht.1.1
  have hs₁1 : s₁ ≤ 1 := csInf_le hSbdd h1S
  have hlow : ∀ s ∈ Ico (0 : ℝ) s₁, c s ∈ S.Φ '' Q := fun s hs => by
    by_contra hsK
    exact absurd (csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hs₁1⟩, hsK⟩) (not_le.2 hs.2)
  have hc0K : c 0 ∈ S.Φ '' Q := by rw [hc0]; exact ⟨a, ha, rfl⟩
  have hs₁K : c s₁ ∈ S.Φ '' Q := by
    rcases hs₁0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hc0K
    · have hcw : ContinuousWithinAt c (Ico 0 s₁) s₁ :=
        (hcont s₁ ⟨hs₁0, hs₁1⟩).mono fun s hs => ⟨hs.1, hs.2.le.trans hs₁1⟩
      have hcl : c s₁ ∈ closure (c '' Ico 0 s₁) :=
        hcw.mem_closure_image (by rw [closure_Ico h0.ne]; exact right_mem_Icc.2 h0.le)
      exact closure_minimal (by rintro _ ⟨s, hs, rfl⟩; exact hlow s hs) hK hcl
  have hs₁lt : s₁ < 1 := by
    refine lt_of_le_of_ne hs₁1 fun h => hb ?_
    rw [← hc1, ← h]; exact hs₁K
  -- the local isomorphism along the curve
  have hstep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ e ∈ S.O, c s = S.Φ e → ∀ U : Opens E0, e ∈ U →
      (U : Set E0) ⊆ S.O → ∃ ε > 0, ∀ σ ∈ Icc (0 : ℝ) 1, |σ - s| < ε → c σ ∈ S.Φ '' U := by
    intro s hs e he hce U heU hUO
    have hopen := S.isOpen_image U.isOpen hUO
    have hmem : S.Φ '' U ∈ 𝓝 (c s) := hopen.mem_nhds (by rw [hce]; exact ⟨e, heU, rfl⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hcont s hs hmem)
    exact ⟨ε, hε, fun σ hσ hσs => hball ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact hσs, hσ⟩⟩
  -- real induction: `c s` stays in `Φ(𝒬 ∩ J⁺(a))` up to `s₁`
  set KA := Q ∩ causality.Jplus ⊤ {a} with hKA
  have hKAc : IsCompact (S.Φ '' KA) :=
    (hQc.inter_right (E0.isClosed_Jplus a)).image_of_continuousOn
      (S.continuousOn.mono (inter_subset_left.trans hQO))
  set G : Set ℝ := {s | c s ∈ S.Φ '' KA} with hG
  have hGcl : IsClosed (G ∩ Icc 0 s₁) := by
    rw [inter_comm]
    exact (hcont.mono (Icc_subset_Icc le_rfl hs₁1)).preimage_isClosed_of_isClosed isClosed_Icc
      hKAc.isClosed
  have hG0 : (0 : ℝ) ∈ G := by
    rw [hG, mem_setOf_eq, hc0]
    exact ⟨a, ⟨ha, Causal.Precausality.mem_Jplus_singleton.2 (causality.le_refl trivial)⟩, rfl⟩
  have hGs₁ : Icc 0 s₁ ⊆ G := by
    refine hGcl.Icc_subset_of_forall_exists_gt hG0 fun x hx y hy => ?_
    obtain ⟨e, ⟨heQ, hae⟩, hce⟩ := hx.1
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.2.1, hx.2.2.le.trans hs₁1⟩
    obtain ⟨U₀, heU₀, hU₀O, hU₀⟩ := S.exists_locIso (hQO heQ)
    obtain ⟨ε, hε, hball⟩ := hstep x hxI e (hQO heQ) hce.symm U₀ heU₀ hU₀O
    set σ := min y (min (x + ε / 2) ((x + s₁) / 2)) with hσ
    have hxs₁ := hx.2.2
    have hxσ : x < σ := lt_min hy (lt_min (by linarith) (by linarith))
    have hσy : σ ≤ y := min_le_left _ _
    have hσs₁ : σ < s₁ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
    have hσε : σ ≤ x + ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hseg : ∀ τ ∈ Icc x σ, c τ ∈ S.Φ '' U₀ := fun τ hτ =>
      hball τ ⟨hx.2.1.trans hτ.1, (hτ.2.trans hσs₁.le).trans hs₁1⟩
        (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])
    obtain ⟨e', he'Q, hce'⟩ := hlow σ ⟨by linarith [hx.2.1], hσs₁⟩
    obtain ⟨e'', he''U, hce''⟩ := hseg σ ⟨hxσ.le, le_rfl⟩
    have he' : e'' = e' := S.injOn (hU₀O he''U) (hQO he'Q) (hce''.trans hce'.symm)
    subst he'
    have hcurve : (CE X).CausalCurveOn ⊤ c x σ :=
      Causal.CurveOn.restrict hc hx.2.1 ((hσs₁.le.trans hs₁1)) le_rfl fun τ hτ =>
        hc.mem τ ⟨hx.2.1.trans hτ.1, (hτ.2.trans hσs₁.le).trans hs₁1⟩
    have hee' := S.le_of_curve hU₀O hU₀ hxσ.le hcurve hseg heU₀ he''U hce.symm hce''.symm
    refine ⟨σ, ⟨e'', ⟨he'Q, ?_⟩, hce''⟩, hxσ, hσy⟩
    exact Causal.Precausality.mem_Jplus_singleton.2
      (causality.le_trans (Causal.Precausality.mem_Jplus_singleton.1 hae) hee')
  obtain ⟨e, ⟨heQ, hae⟩, hce⟩ := hGs₁ ⟨hs₁0, le_rfl⟩
  have hae' := Causal.Precausality.mem_Jplus_singleton.1 hae
  refine ⟨e, heQ, ?_, hae', ?_⟩
  · -- the exit point is on the wall or the lid
    by_contra hwl
    push Not at hwl
    have her : rad e < ρ := lt_of_le_of_ne heQ.1.2 hwl.1
    have heT : e.1 < T := lt_of_le_of_ne heQ.2 hwl.2
    obtain ⟨U₀, heU₀, hU₀O, hU₀⟩ := S.exists_locIso (hQO heQ)
    set U₁ : Opens E0 := U₀ ⊓ ⟨{x : E0 | rad x < ρ ∧ x.1 < T},
      (isOpen_lt continuous_rad continuous_const).inter (isOpen_lt continuous_fst continuous_const)⟩
    have heU₁ : e ∈ U₁ := ⟨heU₀, her, heT⟩
    have hU₁O : (U₁ : Set E0) ⊆ S.O := fun x hx => hU₀O hx.1
    obtain ⟨ε, hε, hball⟩ := hstep s₁ ⟨hs₁0, hs₁1⟩ e (hQO heQ) hce.symm U₁ heU₁ hU₁O
    obtain ⟨σ, hσS, hσlt⟩ := exists_lt_of_csInf_lt hSne
      (show s₁ < min (s₁ + ε / 2) 1 from lt_min (by linarith) hs₁lt)
    have hs₁σ : s₁ ≤ σ := csInf_le hSbdd hσS
    have hσε : σ < s₁ + ε / 2 := hσlt.trans_le (min_le_left _ _)
    have hseg : ∀ τ ∈ Icc s₁ σ, c τ ∈ S.Φ '' U₁ := fun τ hτ =>
      hball τ ⟨hs₁0.trans hτ.1, hτ.2.trans hσS.1.2⟩
        (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])
    obtain ⟨e', he'U, hce'⟩ := hseg σ ⟨hs₁σ, le_rfl⟩
    have hcurve : (CE X).CausalCurveOn ⊤ c s₁ σ :=
      Causal.CurveOn.restrict hc hs₁0 hσS.1.2 le_rfl fun τ hτ =>
        hc.mem τ ⟨hs₁0.trans hτ.1, hτ.2.trans hσS.1.2⟩
    have hee' := S.le_of_curve hU₁O
      (fun U hU V hV a ha b hb h => hU₀ U (hU.trans inf_le_left) V hV a ha b hb h)
      hs₁σ hcurve hseg heU₁ he'U hce.symm hce'.symm
    have hf := (calculus_le hee').2.2.2.2.1
    have he'Q : e' ∈ Q := ⟨⟨heQ.1.1.trans hf, he'U.2.1.le⟩, he'U.2.2.le⟩
    exact hσS.2 ⟨e', he'Q, hce'⟩
  · rw [hce, ← hc1]
    exact hc.le_of_le hs₁0 hs₁1 le_rfl

omit [HasGroupoid X e0Groupoid] in
/-- **A radius avoiding a regular point**: a regular `x` lies outside the spear of some radius
`ρ ∈ ]0, R]` (the spear can be chosen with `q ∉ 𝒮`, B21 l.1107). -/
theorem exists_radius_avoiding {x : X} (hx : x ∉ S0 X) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ S.R ∧ x ∉ S.Φ '' spear S.v ρ := by
  by_cases h : x ∈ S.Φ '' spear S.v S.R
  · obtain ⟨e₁, he₁, rfl⟩ := h
    have hax : e₁ ∉ axis := fun hax => hx ((S.mem_S0_iff (S.spear_subset_O le_rfl he₁)).2 hax)
    have hr : 0 < rad e₁ := norm_pos_iff.2 hax
    have hR := he₁.2
    refine ⟨rad e₁ / 2, by linarith, by linarith, ?_⟩
    rintro ⟨e, he, hee⟩
    have := S.injOn (S.spear_subset_O (by linarith) he) (S.spear_subset_O le_rfl he₁) hee
    subst this
    linarith [he.2]
  · exact ⟨S.R, S.pos, le_rfl, h⟩

omit [HasGroupoid X e0Groupoid] in
/-- **Regular points of the chart below a regular `q'` above a BTZ point** (`I⁻(q')` is open). -/
theorem exists_regular_le {ρ : ℝ} (hρ0 : 0 < ρ) {t : ℝ} (ht : S.v + ρ ≤ t)
    {q' : X} (hlt : (CE X).lt ⊤ (S.Φ ((t, 0) : E0)) q') :
    ∃ w : ℂ, 0 < ‖w‖ ∧ ‖w‖ ≤ ρ ∧ (CE X).le ⊤ (S.Φ ((t, w) : E0)) q' := by
  have htO : ((t, 0) : E0) ∈ S.O := S.spear_subset_O le_rfl (axis_mem_spear S.pos.le (by linarith))
  have hc : ContinuousAt S.Φ ((t, 0) : E0) := S.continuousOn.continuousAt (S.isOpen_O.mem_nhds htO)
  have hev : ∀ᶠ x in 𝓝 ((t, 0) : E0), S.Φ x ∈ (CE X).Iminus ⊤ {q'} :=
    hc.eventually ((isOpen_Iminus {q'}).mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hlt))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set w : ℂ := ((min (ε / 2) ρ : ℝ) : ℂ) with hw
  have hwn : ‖w‖ = min (ε / 2) ρ := by
    rw [hw, Complex.norm_real, Real.norm_of_nonneg (le_min (by linarith) hρ0.le)]
  refine ⟨w, by rw [hwn]; exact lt_min (by linarith) hρ0, by rw [hwn]; exact min_le_right _ _, ?_⟩
  have hd : dist ((t, w) : E0) (t, 0) < ε := by
    rw [Prod.dist_eq, dist_self, dist_zero_right, hwn, max_eq_right (le_min (by linarith) hρ0.le)]
    linarith [min_le_left (ε / 2) ρ]
  exact (CE X).le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 (hball hd))

end SpearChart

/-! ### §2 No vertical null line of an `𝔼₀`-morphism converges to a regular point -/

/-- The velocity of the vertical null lines of `𝔼₀` under the paper's developing map. -/
noncomputable def vertU : Causal.Minkowski 2 := (1, WithLp.toLp 2 ![1, 0])

theorem vertU_ne_zero : vertU ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  simp [vertU] at this

/-- **The paper's developing map is affine along the vertical lines** (`btzPaperDev`,
`RamcovGX.tex:1947`): `D(σ', r, θ) = D(σ, r, θ) + (σ' − σ) • (1, (1, 0))`, a null velocity. -/
theorem btzPaperDev_vertical (σ σ' r θ : ℝ) :
    btzPaperDev (σ', r, θ) = btzPaperDev (σ, r, θ) + (σ' - σ) • vertU := by
  simp only [btzPaperDev, vertU]
  refine Prod.ext ?_ ?_
  · simp; ring
  · ext i; fin_cases i <;> simp; ring

attribute [local instance] btzE0Structure in
/-- **No vertical null line of an `𝔼₀`-morphism has a regular future endpoint** (the regular
analogue of `E0Spear.axis_noLimit`, the core of DEC-126's repair; no volume, no time separation).
Were `σ ↦ φ(σ, z)` (`z ≠ 0`) convergent to a regular `x₀`, then in a regular chart `c'` at the
chart image of `x₀`, `F(σ) = c'(κ(φ(σ, z)))` is near every `σ` of the form `k • D(σ, |z|, arg z)`,
`k ∈ Isom(𝐌³)` (the a.e.-isomorphism property of `κ ∘ φ`, `E0RegAt`, and
`btz_chart_eq_smul_btzPaperDev`): locally affine with the nonzero velocity `k.linear (1,(1,0))`;
`affine_noLimit` concludes. The Lorentz-invariant size is the affine parameter of the null line. -/
theorem vertical_noLimit {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X]
    [HasGroupoid X e0Groupoid] {W : Set E0Y} {φ : E0Y → X} (hW : IsOpen W)
    (hφ : IsE0Mor φ W) {z : ℂ} (hz : z ≠ 0) {σ₀ : ℝ}
    (hmem : ∀ σ, σ₀ ≤ σ → paperInY ((σ, z) : E0) ∈ W) {x₀ : X} (hx₀ : x₀ ∉ S0 X) :
    ¬ Tendsto (fun σ : ℝ => φ (paperInY ((σ, z) : E0))) atTop (𝓝 x₀) := by
  intro hlim
  set κ := chartAt E0Y x₀ with hκ
  have hκreg : κ x₀ ∈ e0Reg := by
    by_contra h
    exact hx₀ ⟨rfl, h⟩
  obtain ⟨c', hc', hc'x⟩ := mem_support.1 hκreg
  have hN : IsOpen (κ.source ∩ κ ⁻¹' c'.source) := κ.isOpen_inter_preimage c'.open_source
  obtain ⟨σ₁', hev⟩ := eventually_atTop.1
    (hlim.eventually (hN.mem_nhds ⟨mem_chart_source E0Y x₀, hc'x⟩))
  set σ₁ := max σ₀ σ₁' with hσ₁
  set γ : ℝ → E0Y := fun σ => paperInY ((σ, z) : E0) with hγ
  have hγc : Continuous γ := continuous_paperInY.comp (continuous_id.prodMk continuous_const)
  set F : ℝ → Causal.Minkowski 2 := fun σ => c' (κ (φ (γ σ))) with hF
  have hFlim : Tendsto F atTop (𝓝 (c' (κ x₀))) :=
    ((c'.continuousAt hc'x).comp (κ.continuousAt (mem_chart_source E0Y x₀))).tendsto.comp hlim
  refine affine_noLimit (σ₁ := σ₁) (fun σ hσ => ?_) _ hFlim
  have hσ₀ : σ₀ ≤ σ := (le_max_left _ _).trans hσ.le
  have hσ₁' : σ₁' ≤ σ := (le_max_right _ _).trans hσ.le
  have hyW : γ σ ∈ W := hmem σ hσ₀
  -- `κ ∘ φ` is an `𝔼₀`-morphism near `γ σ`
  have hφc : ContinuousOn φ W := fun y hy => (hφ y hy).continuousWithinAt
  set U := W ∩ φ ⁻¹' κ.source with hU
  have hUo : IsOpen U := hφc.isOpen_inter_preimage hW κ.open_source
  have hyU : γ σ ∈ U := ⟨hyW, (hev σ hσ₁').1⟩
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hφU : IsE0Mor φ U := Causal.CBG.liftPropOn_mono_of_le hW hUo hφ inter_subset_left
  have hgU : IsE0Mor (κ ∘ φ) U :=
    Causal.CBG.liftPropOn_comp hUo κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hφU
      (fun y hy => hy.2)
  have h := (hgU (γ σ) hyU).2
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    preimage_id_eq] at h
  obtain ⟨e, he, hge, hye⟩ := h hyU
  have hyreg : γ σ ∈ e0Reg := paperInY_mem_e0Reg_iff.2 fun h => hz h
  obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 (γ σ) hye).2 hyreg
  obtain ⟨c, hc, hyc⟩ := mem_support.1 hyreg
  have hgy : (κ ∘ φ) (γ σ) = e (γ σ) := hge ⟨hyU, hye⟩
  have hey : e (γ σ) ∈ c'.source := by rw [← hgy]; exact (hev σ hσ₁').2
  obtain ⟨k₀, hk₀⟩ := hch c hc c' hc' hyc hey
  -- the regular chart at `γ σ` is a chart of `𝔼₀`
  have hyb : γ σ = Sum.inr (E0.toPaper.symm ((σ, z) : E0)) := paperInY_apply _
  rw [hyb] at hyc
  obtain ⟨c₀, hc₀, rfl, hbc₀⟩ := exists_of_mem_e0Atlas_inr hc hyc
  have hev1 : ∀ᶠ σ' in 𝓝 σ, F σ' = k₀ • c₀ (E0.toPaper.symm ((σ', z) : E0)) := by
    have h1 := (hγc.tendsto σ).eventually hk₀
    have h2 : ∀ᶠ σ' in 𝓝 σ, (κ ∘ φ) (γ σ') = e (γ σ') :=
      (hγc.tendsto σ).eventually (Filter.eventually_of_mem
        ((hUo.inter e.open_source).mem_nhds ⟨hyU, hye⟩) fun y hy => hge hy)
    filter_upwards [h1, h2] with σ' h1 h2
    have h3 : F σ' = c' ((κ ∘ φ) (γ σ')) := rfl
    rw [h3, h2, h1]
    simp [γ, paperInY_apply]
  -- the paper's coordinates `(σ, r, θ)` of the line
  set r := ‖z‖ with hr
  set θ := Complex.arg z with hθ
  have hr0 : 0 < r := norm_pos_iff.2 hz
  have hpaper : ∀ σ' : ℝ, E0.toPaper.symm ((σ', z) : E0) =
      orbitMk (GammaA (2 * π)) (btzPaperCyl (σ', r, θ)) := by
    intro σ'
    rw [Homeomorph.symm_apply_eq, btzPaperCyl_of_pos (show 0 < ((σ', r, θ) : ℝ × ℝ × ℝ).2.1 from hr0)]
    rw [E0.toPaper_posEmb hr0 θ σ', hr, hθ, Complex.norm_mul_exp_arg_mul_I]
  have hbc : orbitMk (GammaA (2 * π)) (btzPaperCyl ((σ, r, θ) : ℝ × ℝ × ℝ)) ∈ c₀.source := by
    rw [← hpaper]; exact hbc₀
  obtain ⟨g₁, hg₁⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc₀
    (p := ((σ, r, θ) : ℝ × ℝ × ℝ)) hr0 hbc
  have hlin : Continuous (fun σ' : ℝ => ((σ', r, θ) : ℝ × ℝ × ℝ)) :=
    continuous_id.prodMk continuous_const
  have hev2 : ∀ᶠ σ' in 𝓝 σ, F σ' = (k₀ * g₁) • btzPaperDev (σ', r, θ) := by
    filter_upwards [hev1, (hlin.tendsto σ).eventually hg₁] with σ' h1 h2
    rw [h1, hpaper, h2, mul_smul]
  -- locally affine with the nonzero velocity `(k₀ g₁).linear (1, (1, 0))`
  set k := k₀ * g₁ with hk
  refine ⟨((k : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear) vertU, ?_, ?_⟩
  · intro hw
    exact vertU_ne_zero ((k : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective
      (hw.trans (map_zero _).symm))
  · have hFσ : F σ = k • btzPaperDev (σ, r, θ) := hev2.self_of_nhds
    filter_upwards [hev2] with σ' h'
    rw [h', hFσ, btzPaperDev_vertical σ σ' r θ, Causal.Flat.isom_smul_def,
      Causal.Flat.isom_smul_def, add_comm, ← vadd_eq_add, AffineEquiv.map_vadd, vadd_eq_add,
      map_smul, add_comm]

end Chart

/-! ### §3 Two facts of globally hyperbolic causalities -/

section GH

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] {C : Causal.Causality Z}

/-- **`J⁺(K) ∩ J⁻(x)` is compact** for `K` compact in a tarentin globally hyperbolic Hausdorff
spacetime (the time dual of `E0Spear.isCompact_Jplus_singleton_inter_Jminus_of_isCompact`). -/
theorem isCompact_Jplus_inter_Jminus_singleton (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    {K : Set Z} (hK : IsCompact K) (x : Z) : IsCompact (C.Jplus ⊤ K ∩ C.Jminus ⊤ {x}) := by
  have hcl : IsClosed (C.Jplus ⊤ K ∩ C.Jminus ⊤ {x}) :=
    (Causal.Causality.isClosed_Jplus_of_isCompact (hG.isClosed_le hT) hK).inter
      (hG.isClosed_Jminus_singleton hT x)
  have hex : ∀ k : Z, ∃ ab : Z × Z, k ∈ C.openDiamond ⊤ ab.1 ab.2 := fun k => by
    obtain ⟨a, b, hk, -⟩ := hG.exists_diamond_subset hT k univ_mem
    exact ⟨(a, b), hk⟩
  choose ab hab using hex
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => C.openDiamond ⊤ (ab k).1 (ab k).2)
    fun k _ => isOpen_interior.mem_nhds (hab k)
  refine (t.isCompact_biUnion fun k _ => hG.2 (ab k).1 x).of_isClosed_subset hcl ?_
  rintro z ⟨⟨k₀, hk₀, hk₀z⟩, hzx⟩
  obtain ⟨k, hkt, hk₀k⟩ := mem_iUnion₂.1 (ht hk₀)
  have hak₀ : C.le ⊤ (ab k).1 k₀ := (Causal.Causality.mem_diamond.1 (interior_subset hk₀k)).1
  exact mem_iUnion₂.2 ⟨k, hkt, Causal.Causality.mem_diamond.2
    ⟨C.le_trans hak₀ hk₀z, Causal.Precausality.mem_Jminus_singleton.1 hzx⟩⟩

/-- **A future-monotone curve eventually in a compact set converges** (the abstract form of
`E0Spear.exists_tendsto_of_monotone`): cluster points are above the curve and below each other. -/
theorem exists_tendsto_of_monotone_gh (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    {γ : ℝ → Z} {t₀ : ℝ} (hmono : ∀ s t, t₀ ≤ s → s ≤ t → C.le ⊤ (γ s) (γ t))
    {K : Set Z} (hK : IsCompact K) (hKγ : ∀ t, t₀ ≤ t → γ t ∈ K) :
    ∃ q, Tendsto γ atTop (𝓝 q) := by
  have hev : ∀ᶠ t in atTop, γ t ∈ K := eventually_atTop.2 ⟨t₀, hKγ⟩
  obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (le_principal_iff.2 hev)
  have habove : ∀ q', MapClusterPt q' atTop γ → ∀ s, t₀ ≤ s → C.le ⊤ (γ s) q' := by
    intro q' hq' s hs
    have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jplus_singleton hT (γ s)) hq'
      (eventually_atTop.2 ⟨s, fun t ht => by simpa using hmono s t hs ht⟩)
    simpa using this
  have huniq : ∀ q', MapClusterPt q' atTop γ → q' = q := by
    intro q' hq'
    have h1 : C.le ⊤ q' q := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jminus_singleton hT q) hq'
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q hq t ht⟩)
      simpa using this
    have h2 : C.le ⊤ q q' := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jminus_singleton hT q') hq
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q' hq' t ht⟩)
      simpa using this
    exact hG.1 h1 h2
  exact ⟨q, hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx⟩

end GH

/-! ### §4 The push-out of B21 Prop 2.17: its mixed diamonds -/

section Pushout

open E0CBG E0Spear E0 E0AbsMax

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
  {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}

omit [SecondCountableTopology M] in
/-- **The relations of `M̄` between points of `N` are those of `N`** (`N ↪ M̄` is a BTZ-extension
of a globally hyperbolic `N`, so `ι₂(N)` is causally convex, B21 Lemma 2.13(b)). -/
theorem le_top_ι₂_iff (hN : Causal.Flat.GH N) (P : E0Pushout M N f) (y y' : N) :
    (CE P.carrier).le ⊤ (P.ι₂ y) (P.ι₂ y') ↔ (Causal.Flat.flatCausality 2 N).le ⊤ y y' := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨-, -, hBc⟩ := P.pieces
  let B : Opens P.carrier := ⟨range P.ι₂, P.isOpenEmbedding_ι₂.isOpen_range⟩
  have hGB : (CE P.carrier).GloballyHyperbolicOn B :=
    globallyHyperbolicOn_of_le_iff hN P.isOpenEmbedding_ι₂.continuous rfl (P.le_ι₂ B rfl)
  have hconv := btzExt_causallyConvexIn_of_globallyHyperbolicOn hP hBc hGB
  rw [← P.le_ι₂ B rfl]
  exact (Causal.Causality.le_iff_of_causallyConvexIn hP.causallyArcConnected hconv
    (show P.ι₂ y' ∈ B from ⟨y', rfl⟩) (show P.ι₂ y ∈ B from ⟨y, rfl⟩)).symm

/-- **A spear chart of `M̄` at every BTZ point** (B21 Lemma 2.3 in `M`, `E0Spear.lem_tube_e0`,
pushed by `ι₁`). -/
theorem exists_spearChart (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    (P : E0Pushout M N f) {p : P.carrier} (hp : p ∈ S0 P.carrier) :
    Nonempty (SpearChart P.carrier p) := by
  obtain ⟨hA, hsA, -⟩ := P.pieces
  obtain ⟨p₀, rfl⟩ := hsA hp
  have hp₀ : p₀ ∈ S0 M := (P.sing_ι₁ p₀).1 hp
  obtain ⟨R, U, hU⟩ := lem_tube_e0 hGH hmax hp₀
  obtain ⟨v, W, ψ, hW, hsub, hψ, hinj, hv, -⟩ := hU.chart
  refine ⟨⟨v, R, hU.pos, W, P.ι₁ ∘ ψ, hW, hsub, ?_, ?_, by simp [hv]⟩⟩
  · exact Causal.CBG.liftPropOn_comp hW isOpen_univ P.isE0Mor_ι₁ hψ (mapsTo_univ _ _)
  · exact P.injective_ι₁.comp_injOn hinj

variable (P : E0Pushout M N f) {p : P.carrier} (S : SpearChart P.carrier p)

/-- The points of `N` read by the regular points of the chart. -/
noncomputable def toN (x : E0) : N := Function.invFun P.ι₂ (S.Φ x)

omit [SecondCountableTopology M] in
theorem ι₂_toN {x : E0} (hx : x ∈ S.O) (hax : x ∉ axis) : P.ι₂ (toN P S x) = S.Φ x := by
  have hreg : S.Φ x ∉ S0 P.carrier := fun h => hax ((S.mem_S0_iff hx).1 h)
  obtain ⟨-, -, hBc⟩ := P.pieces
  have hmem : S.Φ x ∈ range P.ι₂ := by_contra fun h => hreg (hBc h)
  exact Function.invFun_eq hmem

omit [SecondCountableTopology M] in
theorem continuousOn_toN : ContinuousOn (toN P S) (S.O ∩ axisᶜ) := by
  rw [P.isOpenEmbedding_ι₂.isInducing.continuousOn_iff]
  exact (S.continuousOn.mono inter_subset_left).congr fun x hx => ι₂_toN P S hx.1 hx.2


theorem isOpen_axis_compl : IsOpen (axisᶜ : Set E0) :=
  (isClosed_eq continuous_snd continuous_const).isOpen_compl

omit [SecondCountableTopology M] in
/-- **The circle trick** (B21 l.1104–1117 repaired, step 2): points of the spear below a regular
`q'` at arbitrarily large height and with radius bounded below are impossible. Compactness of the
annulus gives a limit radius-angle `z`; closedness of `J⁻_N(q')` puts the WHOLE vertical null line
of `z` below `q'`; it then lies in a compact diamond of `N`, so it converges, against
`vertical_noLimit`. -/
theorem circle_trick (hN : Causal.Flat.GH N) {ρ : ℝ} (hρ : ρ ≤ S.R) {q' : P.carrier}
    (hq' : q' ∉ S0 P.carrier) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hseq : ∀ H : ℝ, ∃ e ∈ spear S.v ρ, r₀ ≤ rad e ∧ H ≤ e.1 ∧ (CE P.carrier).le ⊤ (S.Φ e) q') :
    False := by
  obtain ⟨-, -, hBc⟩ := P.pieces
  obtain ⟨y', rfl⟩ : q' ∈ range P.ι₂ := by_contra fun h => hq' (hBc h)
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hT := Causal.Flat.flatCausality_tarentin (d := 2) (X := N)
  choose e he using fun n : ℕ => hseq n
  set A : Set ℂ := {w | r₀ ≤ ‖w‖ ∧ ‖w‖ ≤ ρ} with hA
  have hAc : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun w hw => mem_closedBall_zero_iff.2 hw.2
  obtain ⟨z, hzA, ψ, hψ, hlim⟩ := hAc.tendsto_subseq (x := fun n => (e n).2)
    fun n => ⟨(he n).2.1, (he n).1.2⟩
  have hz0 : z ≠ 0 := fun h => by
    have := hzA.1; rw [h, norm_zero] at this; linarith
  have hzρ : ‖z‖ ≤ ρ := hzA.2
  set σ₀ := S.v + ρ / 2 with hσ₀
  have hmemsp : ∀ σ, σ₀ ≤ σ → ∀ w : ℂ, ‖w‖ ≤ ρ → ((σ, w) : E0) ∈ spear S.v ρ :=
    fun σ hσ w hw => ⟨by simp only [fcoord, rad]; linarith, hw⟩
  have hspR : spear S.v ρ ⊆ spear S.v S.R := spear_mono le_rfl hρ
  have hOz : ∀ σ, σ₀ ≤ σ → ((σ, z) : E0) ∈ S.O ∩ axisᶜ := fun σ hσ =>
    ⟨S.spear_subset_O hρ (hmemsp σ hσ z hzρ), fun h => hz0 h⟩
  -- the vertical line at `z` is below `q'`
  have hbelow : ∀ σ, σ₀ ≤ σ → (Causal.Flat.flatCausality 2 N).le ⊤ (toN P S (σ, z)) y' := by
    intro σ hσ
    have hcl := hN'.isClosed_Jminus_singleton hT y'
    have hcont : Tendsto (fun n => toN P S (σ, (e (ψ n)).2)) atTop (𝓝 (toN P S (σ, z))) := by
      have h1 : Tendsto (fun n => ((σ, (e (ψ n)).2) : E0)) atTop (𝓝 ((σ, z) : E0)) :=
        tendsto_const_nhds.prodMk_nhds hlim
      exact ((continuousOn_toN P S).continuousAt
        ((S.isOpen_O.inter isOpen_axis_compl).mem_nhds (hOz σ hσ))).tendsto.comp h1
    have hev : ∀ᶠ n in atTop,
        toN P S (σ, (e (ψ n)).2) ∈ (Causal.Flat.flatCausality 2 N).Jminus ⊤ {y'} := by
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge σ
      refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
      have hψn : (n₀ : ℝ) ≤ ψ n := by exact_mod_cast hn.trans (hψ.id_le n)
      have hen := he (ψ n)
      have hσen : σ ≤ (e (ψ n)).1 := hn₀.trans (hψn.trans hen.2.2.1)
      have hmem1 : ((σ, (e (ψ n)).2) : E0) ∈ spear S.v ρ := hmemsp σ hσ _ hen.1.2
      have hax1 : ((σ, (e (ψ n)).2) : E0) ∉ axis := fun h => by
        have h2 := hen.2.1
        have h3 : (e (ψ n)).2 = 0 := h
        simp only [rad, h3, norm_zero] at h2
        linarith
      have hle1 : causality.le ⊤ ((σ, (e (ψ n)).2) : E0) (e (ψ n)) := le_vertical_top hσen
      have hX := (CE P.carrier).le_trans (S.le_of_le (hspR hmem1) (hspR hen.1) hle1) hen.2.2.2
      rw [← ι₂_toN P S (S.spear_subset_O hρ hmem1) hax1] at hX
      exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 hX)
    exact Causal.Precausality.mem_Jminus_singleton.1 (hcl.mem_of_tendsto hcont hev)
  -- the line converges in `N`
  set ℓ : ℝ → N := fun σ => toN P S (σ, z) with hℓ
  have hmono : ∀ s t, σ₀ ≤ s → s ≤ t → (Causal.Flat.flatCausality 2 N).le ⊤ (ℓ s) (ℓ t) := by
    intro s t hs hst
    have ht : σ₀ ≤ t := hs.trans hst
    have h1 := S.le_of_le (hspR (hmemsp s hs z hzρ)) (hspR (hmemsp t ht z hzρ))
      (le_vertical_top hst)
    rw [← ι₂_toN P S (hOz s hs).1 (hOz s hs).2, ← ι₂_toN P S (hOz t ht).1 (hOz t ht).2] at h1
    exact (le_top_ι₂_iff hN P _ _).1 h1
  obtain ⟨y₁, hy₁⟩ := exists_tendsto_of_monotone_gh hT hN' hmono (hN'.2 (ℓ σ₀) y') fun t ht =>
    Causal.Causality.mem_diamond.2 ⟨hmono σ₀ t le_rfl ht, hbelow t ht⟩
  -- so does the vertical line of `M̄`, against `vertical_noLimit`
  have hlimX : Tendsto (fun σ : ℝ => S.φ (paperInY ((σ, z) : E0))) atTop (𝓝 (P.ι₂ y₁)) := by
    refine ((P.isOpenEmbedding_ι₂.continuous.tendsto y₁).comp hy₁).congr' ?_
    exact eventually_atTop.2 ⟨σ₀, fun σ hσ => ι₂_toN P S (hOz σ hσ).1 (hOz σ hσ).2⟩
  exact vertical_noLimit S.isOpen S.mor hz0 (fun σ hσ => (hOz σ hσ).1) (P.sing_ι₂ y₁) hlimX

omit [SecondCountableTopology M] in
/-- **The BTZ ray of the vertex is bounded below a regular `q`** (B21 l.1104–1117 repaired, step 2;
the fact the printed proof uses without proof when it takes `K' = K ∩ ∂𝒮` compact). Otherwise every
BTZ point of the chart is below `q ≪ q'`; regular points of the spear below `q'` start at every
height (`exists_regular_le`), and their exits from truncated spears (`SpearChart.exit`) feed the
circle trick: either wall points of radius `ρ` at every height, or, from one start of radius
`r₀ > 0`, lid points at every height of radius `≥ r₀`. -/
theorem exists_bound_axis (hN : Causal.Flat.GH N) (q : P.carrier) :
    ∃ H : ℝ, ∀ t : ℝ, H ≤ t → ¬ (CE P.carrier).le ⊤ (S.Φ ((t, 0) : E0)) q := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  by_contra hcon
  push Not at hcon
  obtain ⟨q', hqq', hq'reg⟩ := exists_lt_notMem_sing hP q
  obtain ⟨ρ, hρ0, hρ, hq'ρ⟩ := S.exists_radius_avoiding hq'reg
  have hstart : ∀ n : ℕ, ∃ a : E0, a ∈ spear S.v ρ ∧ a ∉ axis ∧ (n : ℝ) ≤ fcoord a ∧
      (CE P.carrier).le ⊤ (S.Φ a) q' := by
    intro n
    obtain ⟨t, ht, htq⟩ := hcon (max (n : ℝ) S.v + ρ)
    have hlt := hP.pushUp.lt_of_le_of_lt htq hqq'
    obtain ⟨w, hw0, hwρ, hwle⟩ :=
      S.exists_regular_le hρ0 (by linarith [le_max_right (n : ℝ) S.v]) hlt
    refine ⟨(t, w), ⟨?_, hwρ⟩, fun h => ?_, ?_, hwle⟩
    · simp only [fcoord, rad]; linarith [le_max_right (n : ℝ) S.v]
    · have h3 : w = 0 := h
      rw [h3, norm_zero] at hw0
      exact lt_irrefl _ hw0
    · simp only [fcoord, rad]; linarith [le_max_left (n : ℝ) S.v]
  by_cases hall : ∀ n : ℕ, ∃ e ∈ spear S.v ρ, rad e = ρ ∧ (n : ℝ) ≤ e.1 ∧
      (CE P.carrier).le ⊤ (S.Φ e) q'
  · refine circle_trick P S hN hρ hq'reg hρ0 fun H => ?_
    obtain ⟨e, he, her, hen, hle⟩ := hall ⌈H⌉₊
    exact ⟨e, he, her.ge, (Nat.le_ceil H).trans hen, hle⟩
  · push Not at hall
    obtain ⟨n, hn⟩ := hall
    obtain ⟨a, ha, hax, han, haq⟩ := hstart n
    have hra : 0 < rad a := norm_pos_iff.2 hax
    refine circle_trick P S hN hρ hq'reg hra fun H => ?_
    obtain ⟨e, heQ, hwl, hae, heq⟩ := S.exit hρ (a := a) (T := max H a.1)
      ⟨ha, show a.1 ≤ max H a.1 from le_max_right _ _⟩ (fun ⟨x, hx, hxe⟩ => hq'ρ ⟨x, hx.1, hxe⟩) haq
    have hcal := calculus_le hae
    rcases hwl with hr | hT
    · exfalso
      have hfe : fcoord e ≤ e.1 := by simp only [fcoord, rad]; linarith [norm_nonneg e.2]
      exact hn e heQ.1 hr (by linarith [hcal.2.2.2.2.1]) heq
    · exact ⟨e, heQ.1, hcal.2.2.2.1, by rw [hT]; exact le_max_left _ _, heq⟩

/-- **The mixed diamonds of the push-out are compact** (B21 Prop 2.17's last case,
`BTZ_1.tex:1104–1117`, DEC-126): `p ∈ sing₀(M̄)`, `q` regular. With the spear chart of vertex `p`
(`exists_spearChart`), a radius `ρ` with `q ∉ 𝒮` (`exists_radius_avoiding`), a lid `T` above the
bound of the BTZ points below `q` (`exists_bound_axis`) and `E` the compact set of wall points
below `q`: `J(p, q) = Φ(𝒬 ∩ J⁻(E)) ∪ ι₂(J⁺_N(E) ∩ J⁻_N(q))`, both compact. A point of `J(p, q)`
in `Φ(𝒬)` exits `𝒬` towards `q` through the wall (`SpearChart.exit`; the lid is not below `q`);
one outside `Φ(𝒬)` is reached from `p` through the wall, hence lies in `N`. -/
theorem isCompact_diamond_mixed (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    (hN : Causal.Flat.GH N) (P : E0Pushout M N f) {p q : P.carrier} (hp : p ∈ S0 P.carrier)
    (hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨S⟩ := exists_spearChart hGH hmax P hp
  obtain ⟨-, -, hBc⟩ := P.pieces
  obtain ⟨yq, rfl⟩ : q ∈ range P.ι₂ := by_contra fun h => hq (hBc h)
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hT := Causal.Flat.flatCausality_tarentin (d := 2) (X := N)
  obtain ⟨ρ, hρ0, hρ, hqρ⟩ := S.exists_radius_avoiding hq
  obtain ⟨H, hH⟩ := exists_bound_axis P S hN (P.ι₂ yq)
  set T := max H S.v + ρ + 1 with hTdef
  set Q := spear S.v ρ ∩ {x : E0 | x.1 ≤ T} with hQ
  have hQc : IsCompact Q := isCompact_spear_inter_le _ _ _
  have hspR : spear S.v ρ ⊆ spear S.v S.R := spear_mono le_rfl hρ
  have hQO : Q ⊆ S.O := fun x hx => S.spear_subset_O hρ hx.1
  have hqQ : P.ι₂ yq ∉ S.Φ '' Q := fun ⟨x, hx, hxe⟩ => hqρ ⟨x, hx.1, hxe⟩
  -- no point of the lid is below `q`
  have hnolid : ∀ e ∈ spear S.v ρ, e.1 = T → ¬ (CE P.carrier).le ⊤ (S.Φ e) (P.ι₂ yq) := by
    intro e he heT hle
    have hax : ((fcoord e, 0) : E0) ∈ spear S.v S.R := axis_mem_spear S.pos.le he.1
    have h1 : causality.le ⊤ ((fcoord e, 0) : E0) e := by
      rw [le_top_iff, le_axis_iff rfl]
    refine hH (fcoord e) ?_ ((CE P.carrier).le_trans (S.le_of_le hax (hspR he) h1) hle)
    have := he.2
    simp only [fcoord, rad] at this ⊢
    rw [heT]; linarith [le_max_left H S.v]
  -- the wall `W_T` and its points `E` below `q`
  set WT : Set E0 := {x | rad x = ρ ∧ S.v + ρ / 2 ≤ x.1 ∧ x.1 ≤ T} with hWT
  have hWTc : IsCompact WT := by
    refine ((isCompact_Icc (a := S.v + ρ / 2) (b := T)).prod
      (isCompact_closedBall (0 : ℂ) ρ)).of_isClosed_subset ?_ ?_
    · exact (isClosed_eq continuous_rad continuous_const).inter
        ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_le continuous_fst continuous_const))
    · rintro x ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h3⟩, mem_closedBall_zero_iff.2 h1.le⟩
  have hWTsp : WT ⊆ spear S.v ρ := fun x hx => ⟨by simp only [fcoord]; rw [hx.1]; linarith [hx.2.1],
    hx.1.le⟩
  have hWTreg : WT ⊆ S.O ∩ axisᶜ := fun x hx => ⟨S.spear_subset_O hρ (hWTsp hx), fun h => by
    have h1 := hx.1
    have h2 : x.2 = 0 := h
    simp only [rad, h2, norm_zero] at h1
    linarith⟩
  set E := WT ∩ toN P S ⁻¹' (Causal.Flat.flatCausality 2 N).Jminus ⊤ {yq} with hE
  have hEc : IsCompact E :=
    hWTc.of_isClosed_subset (((continuousOn_toN P S).mono hWTreg).preimage_isClosed_of_isClosed
      hWTc.isClosed (hN'.isClosed_Jminus_singleton hT yq)) inter_subset_left
  have hmemE : ∀ e ∈ WT, (CE P.carrier).le ⊤ (S.Φ e) (P.ι₂ yq) → e ∈ E := by
    intro e heWT heq
    refine ⟨heWT, ?_⟩
    rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2] at heq
    exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 heq)
  have hwall : ∀ e ∈ Q, rad e = ρ → e ∈ WT := fun e heQ hr =>
    ⟨hr, by have := heQ.1.1; simp only [fcoord] at this; rw [hr] at this; linarith, heQ.2⟩
  -- a point of `𝒬` below `q` is below a point of `E`
  have hkey : ∀ x ∈ Q, (CE P.carrier).le ⊤ (S.Φ x) (P.ι₂ yq) →
      ∃ e ∈ E, causality.le ⊤ x e := by
    intro x hx hxq
    obtain ⟨e, heQ, hwl, hxe, heq⟩ := S.exit hρ hx hqQ hxq
    rcases hwl with hr | hT'
    · exact ⟨e, hmemE e (hwall e heQ hr) heq, hxe⟩
    · exact absurd heq (hnolid e heQ.1 hT')
  set G := Q ∩ causality.Jminus ⊤ E with hG
  have hle_cl : IsClosed {z : E0 × E0 | causality.le ⊤ z.1 z.2} :=
    Causal.Causality.isClosed_le E0.tarentin E0.isClosed_Jplus E0.isClosed_Jminus
  have hGc : IsCompact G :=
    hQc.inter_right (Causal.Causality.isClosed_Jminus_of_isCompact hle_cl hEc)
  set KN := toN P S '' E with hKN
  have hKNc : IsCompact KN :=
    hEc.image_of_continuousOn ((continuousOn_toN P S).mono (inter_subset_left.trans hWTreg))
  have hvQ : ((S.v, 0) : E0) ∈ Q :=
    ⟨axis_mem_spear hρ0.le le_rfl, by show S.v ≤ T; linarith [le_max_right H S.v]⟩
  have hvle : ∀ x ∈ spear S.v ρ, (CE P.carrier).le ⊤ p (S.Φ x) := fun x hx => by
    have h1 : causality.le ⊤ ((S.v, 0) : E0) x := by
      rw [le_top_iff, le_axis_iff rfl]; exact hx.1
    have := S.le_of_le (axis_mem_spear S.pos.le le_rfl) (hspR hx) h1
    rwa [S.Φ_vertex] at this
  -- the decomposition
  have hEq : (CE P.carrier).diamond ⊤ p (P.ι₂ yq) = S.Φ '' G ∪
      P.ι₂ '' ((Causal.Flat.flatCausality 2 N).Jplus ⊤ KN ∩
        (Causal.Flat.flatCausality 2 N).Jminus ⊤ {yq}) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hpz, hzq⟩ := Causal.Causality.mem_diamond.1 hz
      by_cases hzQ : z ∈ S.Φ '' Q
      · obtain ⟨x, hx, rfl⟩ := hzQ
        obtain ⟨e, heE, hxe⟩ := hkey x hx hzq
        exact Or.inl ⟨x, ⟨hx, e, heE, hxe⟩, rfl⟩
      · have hpz' : (CE P.carrier).le ⊤ (S.Φ ((S.v, 0) : E0)) z := by
          rw [S.Φ_vertex]; exact hpz
        obtain ⟨e, heQ, hwl, -, hez⟩ := S.exit hρ hvQ hzQ hpz'
        have heq := (CE P.carrier).le_trans hez hzq
        rcases hwl with hr | hT'
        · have heWT := hwall e heQ hr
          have heE := hmemE e heWT heq
          have hzreg : z ∉ S0 P.carrier := fun hzs =>
            (hWTreg heWT).2 ((S.mem_S0_iff (hWTreg heWT).1).1 (hP.mem_sing_zero_of_le hzs hez))
          obtain ⟨y, rfl⟩ : z ∈ range P.ι₂ := by_contra fun h => hzreg (hBc h)
          refine Or.inr ⟨y, ⟨⟨toN P S e, ⟨e, heE, rfl⟩, ?_⟩, ?_⟩, rfl⟩
          · rw [← le_top_ι₂_iff hN P, ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2]
            exact hez
          · exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 hzq)
        · exact absurd heq (hnolid e heQ.1 hT')
    · rintro (⟨x, ⟨hxQ, e, heE, hxe⟩, rfl⟩ | ⟨y, ⟨⟨_, ⟨e, heE, rfl⟩, hey⟩, hyq⟩, rfl⟩)
      · have heWT := heE.1
        refine Causal.Causality.mem_diamond.2 ⟨hvle x hxQ.1, ?_⟩
        refine (CE P.carrier).le_trans (S.le_of_le (hspR hxQ.1) (hspR (hWTsp heWT)) hxe) ?_
        rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2, le_top_ι₂_iff hN P]
        exact Causal.Precausality.mem_Jminus_singleton.1 heE.2
      · have heWT := heE.1
        refine Causal.Causality.mem_diamond.2 ⟨?_, ?_⟩
        · have h1 := hvle e (hWTsp heWT)
          rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2] at h1
          exact (CE P.carrier).le_trans h1 ((le_top_ι₂_iff hN P _ _).2 hey)
        · exact (le_top_ι₂_iff hN P _ _).2 (Causal.Precausality.mem_Jminus_singleton.1 hyq)
  rw [hEq]
  exact (hGc.image_of_continuousOn (S.continuousOn.mono (inter_subset_left.trans hQO))).union
    ((isCompact_Jplus_inter_Jminus_singleton hT hN' hKNc yq).image
      P.isOpenEmbedding_ι₂.continuous)


end Pushout

end E0AbsMax.Mixed

namespace E0AbsMax

section E0

open E0CBG E0Spear

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **The mixed diamonds of the push-out are compact** (B21 Prop 2.17's last case,
`BTZ_1.tex:1104–1115`): `p ∈ sing₀(M̄)`, `q` regular. -/
theorem E0Pushout.isCompact_diamond_mixed (_hGH : (CE M).GloballyHyperbolic)
    (_hmax : IsE0CauchyMaximal M) {N : Causal.Flat.FlatSpacetime.{0} 2} (_hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (P : E0Pushout M N f) {p q : P.carrier} (_hp : p ∈ S0 P.carrier)
    (_hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) :=
  Mixed.isCompact_diamond_mixed _hGH _hmax _hN P _hp _hq

include hLine in
/-- **The push-out is globally hyperbolic** (B21 Prop 2.17, `BTZ_1.tex:1098–1116`): causal by the
two-open argument (`isCausal_of_twoOpens`, the instance of Cor 2.15 the proof uses), diamonds
compact by `isCompact_diamond_of_twoOpens` — inside `ι₂(N)` by Lemma 2.13(b), inside `ι₁(M)` when
the upper tip is BTZ, and the mixed case `E0Pushout.isCompact_diamond_mixed`. -/
theorem E0Pushout.globallyHyperbolic (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    {N : Causal.Flat.FlatSpacetime.{0} 2} (hN : Causal.Flat.GH N) {f : e0RegMFlat M → N}
    (P : E0Pushout M N f) : (CE P.carrier).GloballyHyperbolic := by
  have hP := e0_sfa hLine P.carrier
  obtain ⟨hA, hsA, hBc⟩ := P.pieces
  let A : Opens P.carrier := ⟨range P.ι₁, hA⟩
  let B : Opens P.carrier := ⟨range P.ι₂, P.isOpenEmbedding_ι₂.isOpen_range⟩
  have hGA : (CE P.carrier).GloballyHyperbolicOn A :=
    globallyHyperbolicOn_of_le_iff hGH (continuous_of_isE0Mor P.isE0Mor_ι₁) rfl
      (le_iff_of_isE0Mor P.isE0Mor_ι₁ P.injective_ι₁ rfl)
  have hGB : (CE P.carrier).GloballyHyperbolicOn B :=
    globallyHyperbolicOn_of_le_iff hN P.isOpenEmbedding_ι₂.continuous rfl
      (P.le_ι₂ B rfl)
  exact globallyHyperbolic_of_twoOpens hP (A := A) (B := B) hsA hBc hGA hGB
    fun p hp q hq => P.isCompact_diamond_mixed hGH hmax hN hp hq

include hLine in
/-- **B21 Prop 2.17, maximality of `Reg M`** (`BTZ_1.tex:1095–1116`) for `A = {0}`, `A* = ∅`:
absolutely maximal in Barbot's sense (`Causal.Flat.AbsMax (fun _ => True)`). For an isometric
embedding `f : Reg M → N` into a GH flat spacetime, the push-out `M̄` is a GH `𝔼₀`-manifold
(`E0Pushout.globallyHyperbolic`); `M` is `E₀`-maximal (Prop 2.16), so `ι₁ : M → M̄` is onto, and a
point `ι₂ y = ι₁ x` is glued: `y = f w`. -/
theorem absMax_e0RegM (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  have hE := isE0Maximal_of_isE0CauchyMaximal hLine hGH hS hSc hSac hmax
  intro N hN _ f hf y
  obtain ⟨P⟩ := exists_e0Pushout hN hf
  have hbij := hE P.carrier P.ι₁ (P.globallyHyperbolic hLine hGH hmax hN) P.isE0Mor_ι₁
    P.injective_ι₁
  obtain ⟨x, hx⟩ := hbij.2 (P.ι₂ y)
  obtain ⟨w, -, hw⟩ := P.glue x y hx
  exact ⟨w, hw⟩

/-! ### §6 (deleted, DEC-117)

The topological forms `prop_abs_max` / `cor_abs_max` (a compact acausal Cauchy surface, Cauchy
completeness through the legacy `E0Surgery.regM_isCauchyComplete` and its (G0) smoothing) are
**deleted** with that route (DEC-117, DEC-107): the forms of record are §8's `prop_abs_max_C1`,
`cor_abs_max_C1`. -/

/-! ### §7 The unconditional forms (no `hLine`: (O2) is `e0_hLine`)

The primary declarations of the Prop 2.16 / 2.17 / Cor 2.18 rows: each `hLine`-form above with
its (O2) hypothesis discharged by `e0_hLine` (`E0LM.e0_globalBTZ`, sorry-free). The `hLine`-forms
are kept because downstream files (`GX.BTZ.Uniformization`) pass their own `hLine`. -/

/-- **B21 Prop 2.16, (i) ⇒ (ii)**, unconditional. -/
theorem isE0Maximal_of_isE0CauchyMaximal_e0 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) : IsE0Maximal M :=
  isE0Maximal_of_isE0CauchyMaximal e0_hLine hGH hS hSc hSac hmax

/-- **B21 Prop 2.16** (`BTZ_1.tex:1048–1075`), unconditional. -/
theorem prop_cauchy_abs_max_e0 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S) :
    IsE0CauchyMaximal M ↔ IsE0Maximal M :=
  prop_cauchy_abs_max e0_hLine hGH hS hSc hSac

/-- **B21 Prop 2.16** as printed (Cauchy-compact), unconditional. -/
theorem prop_cauchy_abs_max_of_cauchyCompact_e0 (hGH : (CE M).GloballyHyperbolic)
    (hCC : E0CauchyCompact M) : IsE0CauchyMaximal M ↔ IsE0Maximal M :=
  prop_cauchy_abs_max_of_cauchyCompact e0_hLine hGH hCC

/-- **`Reg M` is globally hyperbolic**, unconditional. -/
theorem gh_e0RegMFlat_e0 (hGH : (CE M).GloballyHyperbolic) : Causal.Flat.GH (e0RegMFlat M) :=
  gh_e0RegMFlat e0_hLine hGH

/-- **The push-out is globally hyperbolic**, unconditional. -/
theorem E0Pushout.globallyHyperbolic_e0 (hGH : (CE M).GloballyHyperbolic)
    (hmax : IsE0CauchyMaximal M) {N : Causal.Flat.FlatSpacetime.{0} 2} (hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (P : E0Pushout M N f) : (CE P.carrier).GloballyHyperbolic :=
  P.globallyHyperbolic e0_hLine hGH hmax hN

/-- **`Reg M` is absolutely maximal**, unconditional. -/
theorem absMax_e0RegM_e0 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) : Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  absMax_e0RegM e0_hLine hGH hS hSc hSac hmax

/-! ### §8 DEC-107: « Cauchy-compact » read as B21 l.227 (a compact `C¹` spacelike Cauchy surface)

The forms of record of Props 2.16, 2.17 and Cor 2.18 (WP-44f): « Cauchy-compact » is
`GX.E0Surgery.IsE0C1SpacelikeCauchy` (DEC-107), so Cauchy-completeness comes from
`GX.E0Surgery.regM_isCauchyComplete_of_C1` and NOT through the (G0) smoothing
`exists_isE0C1SpacelikeCauchy` (not owed). Acausality of the surface is not assumed: a Cauchy
surface of a globally hyperbolic `𝔼₀`-manifold is acausal (`isAcausal_of_isCauchySurface_e0`). -/

omit [ConnectedSpace M] in
/-- **A Cauchy surface of a globally hyperbolic `𝔼₀`-manifold is acausal** (causal
arc-connectedness and Levin's `CurvesExtend`, `Causal.Causality.IsCauchySurface.isAcausal`): the
acausality field of `E0CauchyCompact` is redundant. -/
theorem isAcausal_of_isCauchySurface_e0 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) : (CE M).IsAcausal S :=
  hS.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)

/-- **Cauchy-compact in the `C¹` sense (DEC-107)** implies `E0CauchyCompact`. -/
theorem e0CauchyCompact_of_C1 (hGH : (CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) : E0CauchyCompact M := by
  obtain ⟨S, hS⟩ := hCC
  exact ⟨S, hS.cauchy, hS.compact, isAcausal_of_isCauchySurface_e0 hGH hS.cauchy⟩

/-- **B21 Prop 2.16 under DEC-107** (`BTZ_1.tex:1048–1075`): a globally hyperbolic `𝔼₀`-manifold
with a compact `C¹` spacelike Cauchy surface is Cauchy-maximal iff it is `E₀`-maximal. -/
theorem prop_cauchy_abs_max_C1 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : E0Surgery.IsE0C1SpacelikeCauchy M S) : IsE0CauchyMaximal M ↔ IsE0Maximal M :=
  prop_cauchy_abs_max_e0 hGH hS.cauchy hS.compact (isAcausal_of_isCauchySurface_e0 hGH hS.cauchy)

/-- **B21 Prop 2.17 under DEC-107** (`prop:abs_max`, `BTZ_1.tex:1078–1082`, proof l.1088–1119), the
form of record: for `M` a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold with a compact `C¹`
spacelike Cauchy surface `S`, `Reg M` is globally hyperbolic, Cauchy-complete
(`E0Surgery.regM_isCauchyComplete_of_C1`, no smoothing) and absolutely maximal in Barbot's sense. -/
theorem prop_abs_max_C1 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  ⟨gh_e0RegMFlat_e0 hGH, E0Surgery.regM_isCauchyComplete_of_C1 hGH hS hmax,
    absMax_e0RegM_e0 hGH hS.cauchy hS.compact (isAcausal_of_isCauchySurface_e0 hGH hS.cauchy) hmax⟩

/-- **B21 Cor 2.18 under DEC-107** (`cor:abs_max`, `BTZ_1.tex:1083–1086`; DEC-28's input to the
headline), the form of record: for `M` a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold which is
Cauchy-compact in B21 l.227's sense (a compact `C¹` spacelike Cauchy surface, DEC-107), `Reg(M)`
is globally hyperbolic, Cauchy-complete and absolutely maximal in the sense of Barbot
(`Causal.Flat.AbsMax (fun _ => True)`). -/
theorem cor_abs_max_C1 (hGH : (CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  obtain ⟨S, hS⟩ := hCC
  exact prop_abs_max_C1 hGH hS hmax

end E0

end E0AbsMax

end GX
