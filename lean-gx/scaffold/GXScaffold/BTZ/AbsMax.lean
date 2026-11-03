import GXScaffold.BTZ.Surgery
import Causal.LemmaKLocal

/-!
# `GXScaffold.BTZ.AbsMax` — absolute maximality of `Reg M` (B21 Lemmas 2.12–2.15, Props 2.16–2.17, Cor 2.18)

Package WP-41k (WAVE5-PLAN.md, WP-39k). `brunswic2021cauchy` (**B21**,
`papers/gx/sources/2108.12631/src/BTZ_1.tex`), §2.3–2.4 (l.936–1117), the input of DEC-28's
headline (`AbsMax (fun _ => True) (Reg M)` in the Cauchy-compact case). No gx ledger label is
certified: these are cited results built here (DEC-23). Rows (B21 labels; PDF numbering):

* `brunswic2021cauchy:Remark 1` — `BTZ_1.tex:995–998` (unlabelled `remark`; partial, a reading):
  'embedding' read as an open subset (kb/0001), no transport along an abstract embedding;
  `GX.E0AbsMax.globallyHyperbolicOn_of_causallyConvexIn` for any causality under the hypothesis
  `CausallyArcConnected` (for `𝔼≥0`-manifolds an SFA model-fact field, kb/0012); unconditional
  for `𝔼₀`-manifolds: `GX.E0AbsMax.globallyHyperbolic_opens_of_causallyConvexIn`.
* `brunswic2021cauchy:lem:BTZext_caus_conv` (Lemma 2.13) — `BTZ_1.tex:999–1033` (partial):
  open-set form under the named model-fact hypothesis `SingularFlatAxioms` (kb/0012, bucket D;
  `T2` is its field `t2`), whose `𝔼₀` instance `e0_sfa` is conditional on (O2) `hLine`:
  (a) `GX.E0AbsMax.btzExt_causallyConvexIn_iff`, (b)
  `GX.E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn`.
* `brunswic2021cauchy:Lemma 2.14` — `BTZ_1.tex:1026–1036`: `GX.E0AbsMax.btzExt_isCausal_of_stronglyCausalOn`,
  regular case proved, the closed BTZ loop a tagged `sorry`
  (`GX.E0AbsMax.sing_eq_of_le_of_le_of_stronglyCausalOn`).
* `brunswic2021cauchy:cor:GH_causal` (Cor 2.15) — `BTZ_1.tex:1038`: `GX.E0AbsMax.cor_GH_causal`
  (through Lemma 2.14; GH ⇒ strongly causal proved, `stronglyCausalOn_of_globallyHyperbolicOn`).
  The instance Prop 2.17 uses is sorry-free: `GX.E0AbsMax.isCausal_of_twoOpens`.
* `brunswic2021cauchy:lem:extension_hausdorff` (Lemma 2.12) — `BTZ_1.tex:941–991`: stated in the
  case Prop 2.17 uses (`GX.E0AbsMax.lem_extension_hausdorff`, tagged `sorry`).
* `brunswic2021cauchy:prop:cauchy_abs_max` (Prop 2.16) — `BTZ_1.tex:1048–1074`, for `𝔼₀`-manifolds
  through lemma K: `GX.E0AbsMax.prop_cauchy_abs_max` ((ii)⇒(i) sorry-free; (i)⇒(ii) rests on
  `isLocallyCauchy_image`), printed form `prop_cauchy_abs_max_of_cauchyCompact`.
* `brunswic2021cauchy:prop:abs_max` (Prop 2.17) — `BTZ_1.tex:1078–1117`, `A = {0}`:
  `GX.E0AbsMax.prop_abs_max`; `Reg M` globally hyperbolic **sorry-free** (`gh_e0RegMFlat`, given
  O2), absolutely maximal `absMax_e0RegM` (push-out `E0Pushout`, its GH
  `E0Pushout.globallyHyperbolic` modulo the mixed diamonds), Cauchy-complete from WP-41j.
* `brunswic2021cauchy:cor:abs_max` (Cor 2.18) — `BTZ_1.tex:1082–1085`: `GX.E0AbsMax.cor_abs_max`.

> Let $M_0\xrightarrow{\iota} M_1$ be an embedding of $\mass{\geq0}$-manifold. If $M_1$ is
> globally hyperbolic and $\iota(M_0)$ is causally convex in $M_1$, then $M_0$ is globally
> hyperbolic. (l.996–997)
>
> Let $M_0\xrightarrow{\iota} M_1$ be a BTZ-extension of $\mass{\geq0}$-manifolds. (a) $\iota(M_0)$
> is causally convex in $M_1$ if and only if $\forall x\in \sing_0(M_0),
> \sing_0\left[J^+(\iota(x))\right] \subset \iota(M_0).$ (b) If $M_0$ is globally hyperbolic then
> $\iota(M_0)$ is causally convex in $M_1$. (l.1000–1006)
>
> If $M_0$ is strongly causal then $M_1$ is causal. (l.1028) Any BTZ-extension of a globally
> hyperbolic $\mass{\geq0}$-manifold is causal. (l.1038)
>
> Let $M$ be a globally hyperbolic Cauchy-compact $\mass{A}$-manifold. The following are
> equivalent: (i) $M$ is Cauchy-maximal (ii) $M$ is $\mass{A}$-maximal. (l.1048–1054)
>
> Let $M$ be a globally hyperbolic Cauchy-compact $\mass{0}$-manifold. If $M$ is Cauchy-maximal
> then $\Reg(M)$ is globally hyperbolic Cauchy-complete and absolutely maximal in the sense of
> Barbot. (l.1082–1084)

## What is proved (0 `sorry` unless named)

* §1 model-free: Remark 1; diamonds inside an open set (`diamond_eq_of_subset`); transport of
  global hyperbolicity onto an image (`globallyHyperbolicOn_of_le_iff`); **a compact acausal
  Cauchy surface of a connected GH spacetime is connected** without a splitting
  (`isConnected_of_isCauchySurface_abstract`: a minimal point of `J⁻(x) ∩ J⁺(S₁) ∩ J⁺(S₂)`).
* §2 under `SingularFlatAxioms` (kb/0012, a named model-fact hypothesis), BTZ-extension `A ↪ M` read as an open `A` with
  `Aᶜ ⊆ sing₀`: Lemma 2.13 (a), (b) (the first-exit argument along a causal curve,
  compact diamond `J_A(c 0, q')`, `q' ≫ c t` regular); `causallyConvexIn_reg`,
  `globallyHyperbolicOn_reg` (Reg is causally convex: BTZ points precede); GH ⇒ strongly causal
  on `A`; the two-open causality and diamond lemmas of Prop 2.17's bullets.
* §3–§6 `𝔼₀`-manifolds (two of the five tagged `sorry`s feed this bullet: Prop 2.16's (i)⇒(ii)
  rests on `isLocallyCauchy_image`, `E0Pushout.globallyHyperbolic` on
  `E0Pushout.isCompact_diamond_mixed`): `IsE0Maximal`, `E0CauchyCompact`; Prop 2.16 through
  `Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus` (lemma K, gx
  shape) — every hypothesis of lemma K on `N` discharged (`E0LM.sfa_isOpen_Jplus`, Levin's
  `E0LM.e0_curvesExtend`); relations along injective `𝔼₀`-morphisms (`le_iff_of_isE0Mor`); the
  push-out structure `E0Pushout` and its global hyperbolicity; `ce_opens_eq`
  (charted causality of an open subset = restriction, no CBG geometry needed);
  `flatCausality_e0RegM_eq` (the flat causality of `Reg M` is its `𝔼₀` causality) and
  `gh_e0RegMFlat` (`GH (e0RegMFlat M)`, the hypothesis WP-39m's holonomy carries).

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifolds (Lemmas 2.13–2.15) | ✓ abstract: any causality with `SingularFlatAxioms` (massive cones included); open-set form (kb/0001) |
| `𝔼_A`-manifolds (Props 2.16–2.17, Cor 2.18) | ⚠ strengthened (E0 only; harmless for gx, DEC-77(c)): `A = {0}`, `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, Hausdorff, connected, second countable (DEC-66) |
| `SingularFlatAxioms` of `𝔼₀`-manifolds | ⚠ conditional: from (O2) `hLine` (named hypothesis, as WP-41g/i; `E0LM.e0_globalBTZ` upstream `sorry`) |
| Cauchy-compact | ✓ `E0CauchyCompact` (compact acausal Cauchy surface); its connectedness (lemma K's hypothesis) is proved, `isConnected_of_isCauchySurface`, with no splitting |
| Cauchy-maximal | ✓ `E0Spear.IsE0CauchyMaximal` (DEC-77(c)) |
| `𝔼_A`-maximal | ⚠ `IsE0Maximal`, two readings: 'a.e. `𝔼`-morphism' read as `IsE0Mor f univ`, 'embedding' as injective, 'isomorphism' as bijective; targets `N` **connected** — necessary, not without loss of generality as B21 l.1058 says: unrestricted, `M ↪ M ⊔ M'` (`M'` any nonempty GH `𝔼₀`-manifold) is a non-surjective embedding into a GH manifold, so no `M` would be maximal (finding) |
| Hausdorff (§2) | ✓ part of `SingularFlatAxioms` (field `t2`), not an extra binder |
| absolutely maximal (Barbot) | ✓ `Causal.Flat.AbsMax (fun _ => True)` over `FlatSpacetime.{0} 2` (universe 0, as `e0RegMFlat`) |
| Prop 2.16: smooth splitting of `N`, O'Neill Lemma 45, intersection theory | ⚠ replaced by lemma K (WAVE5-PLAN WP-39k); its local input `isLocallyCauchy_image` a tagged `sorry` |
| Lemma 2.12: general `M₀ → M₁`, `M₂` | ⚠ the case Prop 2.17 uses: `M₀ = Reg M`, `M₂ = N` flat GH |

## SCOPE (disclosed; five tagged `sorry`s)

`sing_eq_of_le_of_le_of_stronglyCausalOn` (the BTZ-loop tube of Lemma 2.14), `isLocallyCauchy_image`
(Prop 2.16), `lem_extension_hausdorff` (Lemma 2.12's
holonomy step), `exists_e0Pushout` (the `𝔼₀`-atlas of the push-out, template Spear §4b, not built),
`E0Pushout.isCompact_diamond_mixed` (Prop 2.17's spear case, through Lemma 2.3 — upstream). Upstream:
`regM_isCauchyComplete` (WP-41j), O2. Each `sorry` names its obstruction.

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

/-- **B21 Remark 1** (`BTZ_1.tex:995–998`, model-free, open-set form, kb/0001): an open subset
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

/-- **B21 Lemma 2.13 (a)** (`BTZ_1.tex:1000–1004, 1011–1018`; open-set form, kb/0001): for an
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

/-- **B21 Lemma 2.13 (b)** (`BTZ_1.tex:1005, 1019–1031`; open-set form): a globally hyperbolic open
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

/-- **The closed BTZ loop of B21 Lemma 2.14's proof** (`BTZ_1.tex:1034–1036`): in a
BTZ-extension of a strongly causal `A`, two BTZ points causal to each other are equal.
Stated for an abstract `SingularFlatAxioms` causality; at that generality it may be unprovable
(the proof needs `𝔼₀` charts and Prop 1.3's tube), and the chart-based form for `𝔼₀`-manifolds
(`C = CE M`, `sing = chartedSing e0SingY M`) is the one owed. -/
theorem sing_eq_of_le_of_le_of_stronglyCausalOn (h : C.SingularFlatAxioms sing) {A : Opens X}
    (hA : (A : Set X)ᶜ ⊆ sing 0) (hSC : StronglyCausalOn C A) {x y : X} (hx : x ∈ sing 0)
    (hy : y ∈ sing 0) (hxy : C.le ⊤ x y) (hyx : C.le ⊤ y x) : x = y := by
  sorry -- SORRY(brunswic2021cauchy:Lemma 2.14): a closed future causal curve c inside sing₀ (x ≤ y ≤ x, x ≠ y, on one BTZ line). B21 l.1034–1036: from a finite cover of c by charts and Prop 1.3 (chart changes at BTZ points are rotation-translations, Rigid's localUnique_sing), a neighbourhood of c is isomorphic to the tube ⟨γ⟩\{r < r*} ⊂ 𝔼₀, γ(τ,r,θ) = (τ+τ₀, r, θ+θ₀), τ₀ > 0; the regular causal curve t ↦ (t, r₁, θ₁) of A is then closed (θ₀ ∈ ℚπ) or recurrent, contradicting strong causality of A. Needs the tube classification (a holonomy computation along the loop through charts), not in the library; the SFA field `line` gives a closed embedding only under causality, which is the conclusion sought. CAUTION: at this generality (an abstract causality with SingularFlatAxioms) the statement may be UNPROVABLE — SFA carries neither 𝔼₀ charts nor Prop 1.3's tube; the form owed is the chart-based one, C = CE M and sing = chartedSing e0SingY M for an 𝔼₀-manifold M, and the abstract statement is kept only because btzExt_isCausal_of_stronglyCausalOn (Lemma 2.14) is stated abstractly

/-- **B21 Lemma 2.14** (`BTZ_1.tex:1026–1036`; open-set form): a BTZ-extension of a strongly
causal `A` is causal. The regular case: two regular causal points lie in a diamond of regular
points (BTZ points precede), inside `A`, and strong causality of `A` separates them; the BTZ
case is the closed BTZ loop (`sing_eq_of_le_of_le_of_stronglyCausalOn`). -/
theorem btzExt_isCausal_of_stronglyCausalOn (h : C.SingularFlatAxioms sing)
    {A : Opens X} (hA : (A : Set X)ᶜ ⊆ sing 0) (hSC : StronglyCausalOn C A) : C.IsCausal := by
  haveI := h.t2
  have hAreg : ∀ z, z ∉ sing 0 → z ∈ A := fun z hz => by_contra fun h' => hz (hA h')
  intro x y hxy hyx
  by_cases hx : x ∈ sing 0
  · exact sing_eq_of_le_of_le_of_stronglyCausalOn h hA hSC hx (h.mem_sing_zero_of_le hx hyx)
      hxy hyx
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
hyperbolic ⇒ strongly causal" of B21 Cor 2.15, l.1038): `A` is causally convex (Lemma 2.13(b)),
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

/-- **B21 Cor 2.15** (`cor:GH_causal`, `BTZ_1.tex:1038`; open-set form): a BTZ-extension of a
globally hyperbolic open set is causal (Lemma 2.14 and `stronglyCausalOn_of_globallyHyperbolicOn`). -/
theorem cor_GH_causal (h : C.SingularFlatAxioms sing) {A : Opens X}
    (hA : (A : Set X)ᶜ ⊆ sing 0) (hG : C.GloballyHyperbolicOn A) : C.IsCausal :=
  btzExt_isCausal_of_stronglyCausalOn h hA (stronglyCausalOn_of_globallyHyperbolicOn h hA hG)

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

/-- **The diamond bullet of B21 Prop 2.17's proof** (`BTZ_1.tex:1100–1103`), in open-set form: in
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

/-- **B21 Prop 2.17's proof, global hyperbolicity of the push-out** (`BTZ_1.tex:1097–1103`), in
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

end SFA

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

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- An `𝔼₀`-morphism on `univ` is continuous. -/
theorem continuous_of_isE0Mor {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] {f : M → N} (hf : IsE0Mor f univ) : Continuous f := by
  have := (isEMorphismOn_of_isE0Mor (W := ⊤) hf).continuousOn
  rwa [Opens.coe_top, continuousOn_univ] at this

/-- **A compact acausal Cauchy surface of a connected globally hyperbolic `𝔼₀`-manifold is
connected** (implicit in B21 Prop 2.16, whose Cauchy surface is "a closed surface of genus g",
gx l.2215; the hypothesis `IsConnected S` of lemma K): `isConnected_of_isCauchySurface_abstract`
with tarentin, causal arc-connectedness and Levin's `CurvesExtend`. -/
theorem isConnected_of_isCauchySurface (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S) :
    IsConnected S :=
  isConnected_of_isCauchySurface_abstract E0LM.e0_tarentin hGH E0LM.e0_causallyArcConnected
    (E0LM.e0_curvesExtend hGH) hS hSc hSac

/-- **The image of an acausal Cauchy surface is locally Cauchy** — the "spacelike hypersurface"
input of lemma K, for an injective `𝔼₀`-morphism between globally hyperbolic `𝔼₀`-manifolds: every
point `f s` has an open `U ∋ f s`, causally convex in `N`, in which `f(S) ∩ U` is a Cauchy
surface of `U`. The flat analogue is `Causal.Flat.Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding`
(sorry-free). -/
theorem isLocallyCauchy_image {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]
    (_hGH : (CE M).GloballyHyperbolic) (_hGN : (CE N).GloballyHyperbolic) {f : M → N}
    (_hf : IsE0Mor f univ) (_hinj : Injective f) {S : Set M} (_hS : (CE M).IsCauchySurface S)
    (_hSac : (CE M).IsAcausal S) : (CE N).IsLocallyCauchy (f '' S) := by
  sorry -- SORRY(brunswic2021cauchy:prop:cauchy_abs_max): the local Cauchy charts of f(S) in N. For a regular point f s this is the 𝔼₀ transcription of Causal.Flat.Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding (≈700 lines in the flat case: J^±(S) closed with union M and intersection S — available here from SingularFlatAxioms; a causally convex chart ball of N inside f(M) by strong causality; the vertical segments of the ball meet f(S) once, giving a strictly contracting graph G; its Lipschitz extension and the local domain graphLocalDomain on which graph G is Cauchy), stated there for FlatSpacetime targets and not reusable for E0Y-charted N; at a point s ∈ S ∩ sing₀ (S crosses a BTZ line) the chart is an 𝔼₀ chart and the graph argument must be redone in the BTZ model, where vertical lines are null (le_vertical) and the cone is not that of 𝐌³ — no local graph/Cauchy-domain theory for 𝔼₀ exists in the library

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **B21 Prop 2.16, (ii) ⇒ (i)** (`BTZ_1.tex:1060`): `E₀`-maximal ⇒ Cauchy-maximal (a Cauchy
embedding is an injective `𝔼₀`-morphism into a globally hyperbolic manifold). -/
theorem isE0CauchyMaximal_of_isE0Maximal (h : IsE0Maximal M) : IsE0CauchyMaximal M :=
  fun N _ _ _ _ _ _ f hf hfm => h N f hf.globallyHyperbolic_target hfm hf.injective

include hLine in
/-- **B21 Prop 2.16, (i) ⇒ (ii)** (`BTZ_1.tex:1048–1074`), through lemma K
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
/-- **B21 Prop 2.16** (`BTZ_1.tex:1048–1074`), for `𝔼₀`-manifolds: a globally hyperbolic
`𝔼₀`-manifold with a compact acausal Cauchy surface is Cauchy-maximal iff it is
`E₀`-maximal. -/
theorem prop_cauchy_abs_max (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S) :
    IsE0CauchyMaximal M ↔ IsE0Maximal M :=
  ⟨isE0Maximal_of_isE0CauchyMaximal hLine hGH hS hSc hSac,
    isE0CauchyMaximal_of_isE0Maximal⟩

include hLine in
/-- **B21 Prop 2.16** (`BTZ_1.tex:1048–1074`) as printed, for `𝔼₀`-manifolds: GH and
Cauchy-compact ⇒ (Cauchy-maximal ⇔ `E₀`-maximal). -/
theorem prop_cauchy_abs_max_of_cauchyCompact (hGH : (CE M).GloballyHyperbolic)
    (hCC : E0CauchyCompact M) : IsE0CauchyMaximal M ↔ IsE0Maximal M := by
  obtain ⟨S, hS, hSc, hSac⟩ := hCC
  exact prop_cauchy_abs_max hLine hGH hS hSc hSac

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

/-! ### §4 The push-out of B21 Prop 2.17 and absolute maximality of `Reg M` -/

/-- **The push-out of B21 Prop 2.17's proof** (`BTZ_1.tex:1094–1096`, via Lemma 2.12
`lem:extension_hausdorff`): for an isometric embedding `f : Reg M → N` into a flat spacetime, an
`𝔼₀`-manifold `M̄` (Hausdorff, connected, second countable) with an injective `𝔼₀`-morphism
`ι₁ : M → M̄` and an open embedding `ι₂ : N → M̄` agreeing on `Reg M`, jointly onto, identifying
only along `f`, with `sing₀(M̄) = ι₁(sing₀ M)` and the flat causality of `N` read through `ι₂`. -/
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
  comm : ∀ w : E0LM.e0RegM M, ι₁ w = ι₂ (f w)
  cover : ∀ z, (∃ x, ι₁ x = z) ∨ ∃ y, ι₂ y = z
  glue : ∀ x y, ι₁ x = ι₂ y → ∃ w : E0LM.e0RegM M, (w : M) = x ∧ f w = y
  sing_ι₁ : ∀ x, ι₁ x ∈ S0 carrier ↔ x ∈ S0 M
  sing_ι₂ : ∀ y, ι₂ y ∉ S0 carrier
  le_ι₂ : ∀ U : Opens carrier, (U : Set carrier) = range ι₂ → ∀ y y',
    (CE carrier).le U (ι₂ y) (ι₂ y') ↔ (Causal.Flat.flatCausality 2 N).le ⊤ y y'

attribute [instance] E0Pushout.top E0Pushout.t2 E0Pushout.conn E0Pushout.sc E0Pushout.cs
  E0Pushout.gx

/-- **B21 Lemma 2.12** (`lem:extension_hausdorff`, `BTZ_1.tex:941–991`), in the case Prop 2.17
uses: `M₀ = Reg M`, `M₁ = M` (`Reg M ↪ M` is a BTZ-extension), `M₂ = N` a globally hyperbolic flat
spacetime (`sing₀ N = ∅ = j(sing₀ Reg M)`), `j = f`: the topological push-out
`(M ⊔ N)/Reg M` (`Causal.Gluing`) is Hausdorff. -/
theorem lem_extension_hausdorff {N : Causal.Flat.FlatSpacetime.{0} 2} (_hN : Causal.Flat.GH N) {f : e0RegMFlat M → N}
    (_hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    T2Space (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) := by
  sorry -- SORRY(brunswic2021cauchy:lem:extension_hausdorff): by Causal.Gluing.t2Space_iff the graph {(w, f w)} must be closed in M × N. B21 l.957–988: for (p, q) in its closure, f(I⁺(p)) ⊆ I⁺(q) (I⁺(x) ⊆ Reg M, GH of N: I⁺(q) is the interior of the lim sup of I⁺(f aₙ)); a decreasing sequence bₙ → p has f(bₙ) decreasing in the compact J⁺(q) ∩ J⁻(f b₀), with a limit q'; in an 𝔼₀ chart at p and a flat chart at q', f is a flat map on W = I⁺(p) ∩ I⁻(bₙ) — if p were a BTZ point, W would be the regular part of a BTZ neighbourhood, containing a loop of nontrivial parabolic holonomy, mapped by f to a loop of N's flat chart (trivial holonomy): impossible; so p ∈ Reg M and q = f p. The holonomy step needs the developing map of Reg M near a BTZ line versus a single flat chart (Holonomy/Rigid have the BTZ model's holonomy, not this comparison), and the sequence argument needs closedness of J^± in N and the lim sup description of I⁺(q); neither is assembled here

/-- **The push-out exists** (B21 Prop 2.17, l.1094–1096): Lemma 2.12 makes `(M ⊔ N)/Reg M`
Hausdorff, and the atlases of `M` and of `N` (read in `Y = 𝕄 ⊕ 𝔼₀` through `inl`) descend. -/
theorem exists_e0Pushout {N : Causal.Flat.FlatSpacetime.{0} 2}
    (hN : Causal.Flat.GH N) {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    Nonempty (E0Pushout M N f) := by
  have _ := lem_extension_hausdorff hN hf
  sorry -- SORRY(brunswic2021cauchy:prop:abs_max): the 𝔼₀-atlas of the Hausdorff push-out (M ⊔ N)/Reg M. Template: Spear's §4b (Causal.CBG.FamilyGlueData over Bool, FamilyGlueData.chartedSpace, hasGroupoid_chartedSpace_of_eqOn, liftPropOn_ι_of_eqOn, secondCountableTopology, t2Space_iff_isClosed_graph). Missing pieces: N as an E0Y-charted 𝔼₀-manifold (charts e.trans e0Inl, transitions inl ∘ Isom(𝐌³) ∘ inl⁻¹ in e0Groupoid via e0RegAt_of_exists); f and f⁻¹ as 𝔼₀-morphisms between Reg M's E0Y-charts and N's (Reg M's flat charts are regChartM = chart ∘ regAtlasChart, LocalModel §5c); sing₀ of the glued space (e0_sing_mem); and the identification of the charted causality on ι₂(N) with flatCausality N (Causal.Flat.eq_flatCausality, inlChart a ChartIso, chartIso_inlChart). Not built in this package

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

/-- **The mixed diamonds of the push-out are compact** (B21 Prop 2.17's last case,
`BTZ_1.tex:1104–1117`): `p ∈ sing₀(M̄)`, `q` regular. -/
theorem E0Pushout.isCompact_diamond_mixed (_hGH : (CE M).GloballyHyperbolic)
    (_hmax : IsE0CauchyMaximal M) {N : Causal.Flat.FlatSpacetime.{0} 2} (_hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (P : E0Pushout M N f) {p q : P.carrier} (_hp : p ∈ S0 P.carrier)
    (_hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) := by
  sorry -- SORRY(brunswic2021cauchy:prop:abs_max): B21 l.1104–1117. A spear neighbourhood 𝒮 ⊆ M of vertex p avoiding q (Lemma 2.3, lem_tube — stated in GXScaffold.BTZ.Spear, its gluing resting on four upstream tagged sorries), its rim 𝒞 (compact, regular); K = J⁺(𝒞) ∩ J⁻(q) = J⁺_N(𝒞) ∩ J⁻_N(q) compact (causal convexity of ι₂ N, Lemma 2.13(b) = btzExt_causallyConvexIn_of_globallyHyperbolicOn), K' = K ∩ ∂𝒮; a past causal curve from q to p meets ∂𝒮 last at a point of K' (no past causal curve enters 𝒮 through its head, Spear's frontier_spear), so J(p, q) ⊆ [J⁻_N(q) ∩ J⁺_N(K')] ∪ [J⁻_M(K') ∩ J⁺_M(p)], both compact. Needs Lemma 2.3 sorry-free and the curve-exit argument at the spear's frontier (the curve-extension theory of open subsets that Spear's isCauchySurface_glued also lacks)

include hLine in
/-- **The push-out is globally hyperbolic** (B21 Prop 2.17, `BTZ_1.tex:1097–1117`): causal by the
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
/-- **B21 Prop 2.17, maximality of `Reg M`** (`BTZ_1.tex:1094–1117`) for `A = {0}`, `A* = ∅`:
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
/-- **B21 Remark 1** (`BTZ_1.tex:995–998`) for an open subset of an `𝔼₀`-manifold: a causally
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

/-! ### §6 B21 Prop 2.17 and Cor 2.18 -/

include hLine in
/-- **B21 Prop 2.17** (`prop:abs_max`, `BTZ_1.tex:1078–1081`, proof l.1086–1117) for `A = {0}`
(`A* = ∅`, so `E_{A*}`-maximality is Barbot's absolute maximality among flat spacetimes): for `M`
a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold with a compact acausal Cauchy
surface, `Reg M` is globally hyperbolic (`gh_e0RegMFlat`), Cauchy-complete
(`GX.E0Surgery.regM_isCauchyComplete`, WP-41j) and absolutely maximal (`absMax_e0RegM`). -/
theorem prop_abs_max (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  ⟨gh_e0RegMFlat hLine hGH, E0Surgery.regM_isCauchyComplete M hGH ⟨S, hS, hSc⟩ hmax,
    absMax_e0RegM hLine hGH hS hSc hSac hmax⟩

include hLine in
/-- **B21 Cor 2.18** (`cor:abs_max`, `BTZ_1.tex:1082–1085`; DEC-28's input to the headline): for `M`
a globally hyperbolic Cauchy-compact Cauchy-maximal `𝔼₀`-manifold, `Reg(M)` is globally hyperbolic,
Cauchy-complete and absolutely maximal in the sense of Barbot. Cauchy-compact as printed
(`E0CauchyCompact`); connectedness of the Cauchy surface proved (`isConnected_of_isCauchySurface`). -/
theorem cor_abs_max (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  obtain ⟨S, hS, hSc, hSac⟩ := hCC
  exact prop_abs_max hLine hGH hS hSc hSac hmax

end E0

end E0AbsMax

end GX
