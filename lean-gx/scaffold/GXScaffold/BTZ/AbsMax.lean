import GXScaffold.BTZ.Surgery
import Causal.LemmaKLocal

/-!
# `GXScaffold.BTZ.AbsMax` — absolute maximality of `Reg M` (B21 Lemmas 2.12–2.15, Props 2.16–2.17, Cor 2.18)

Packages WP-41k, WP-43c (WAVE5-PLAN.md, WP-39k). `brunswic2021cauchy` (**B21**,
`papers/gx/sources/2108.12631/src/BTZ_1.tex`), §2.3–2.4 (l.936–1117), the input of DEC-28's
headline (`AbsMax (fun _ => True) (Reg M)` in the Cauchy-compact case). No gx ledger label is
certified and nothing is marked: these are cited results built here (DEC-23). Rows (B21 labels):

* `brunswic2021cauchy:Remark 1` — `BTZ_1.tex:994–996` (partial, a reading): open-set form
  (kb/0001); `GX.E0AbsMax.globallyHyperbolicOn_of_causallyConvexIn` (any causality, hypothesis
  `CausallyArcConnected`), unconditional for `𝔼₀`-manifolds:
  `GX.E0AbsMax.globallyHyperbolic_opens_of_causallyConvexIn`.
* `brunswic2021cauchy:lem:BTZext_caus_conv` (Lemma 2.13) — `BTZ_1.tex:999–1023` (partial): (a)
  `GX.E0AbsMax.btzExt_causallyConvexIn_iff`, (b) `…_of_globallyHyperbolicOn` under
  `SingularFlatAxioms` (massive cones included); for `𝔼₀`-manifolds with NO model-fact
  hypothesis (WP-43c): `btzExt_causallyConvexIn_iff_e0`, `btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0`.
* `brunswic2021cauchy:Lemma 2.14` — `BTZ_1.tex:1026–1037` (partial): `𝔼₀` form
  `GX.E0AbsMax.btzExt_isCausal_of_stronglyCausalOn_e0`, resting on the tagged `sorry`
  `sing_eq_of_le_of_le_of_stronglyCausalOn_e0` (the closed BTZ loop, l.1035–1036); abstract form
  `btzExt_isCausal_of_stronglyCausalOn` sorry-free with the loop exclusion `NoCausalLoopIn C sing₀`
  an explicit hypothesis.
* `brunswic2021cauchy:cor:GH_causal` (Cor 2.15) — `BTZ_1.tex:1038–1039` (partial): `𝔼₀` form
  `GX.E0AbsMax.cor_GH_causal_e0` (through the Lemma 2.14 loop `sorry`); abstract `cor_GH_causal`
  sorry-free with `NoCausalLoopIn C Aᶜ` explicit; the instance Prop 2.17 uses is sorry-free with no
  hypothesis, `isCausal_of_twoOpens`.
* `brunswic2021cauchy:lem:extension_hausdorff` (Lemma 2.12) — `BTZ_1.tex:941–991` (partial, the
  case Prop 2.17 uses): `GX.E0AbsMax.lem_extension_hausdorff`, sorry-free.
* `brunswic2021cauchy:prop:cauchy_abs_max` (Prop 2.16) — `BTZ_1.tex:1048–1075` (partial), through
  lemma K: `GX.E0AbsMax.prop_cauchy_abs_max_e0` ((ii)⇒(i) sorry-free; (i)⇒(ii) rests on
  `isLocallyCauchy_image`), printed form `prop_cauchy_abs_max_of_cauchyCompact_e0`.
* `brunswic2021cauchy:prop:abs_max` (Prop 2.17, `A = {0}`) — `BTZ_1.tex:1078–1082`, proof
  l.1088–1119 (partial): `GX.E0AbsMax.prop_abs_max_e0`; `Reg M` GH sorry-free (`gh_e0RegMFlat_e0`);
  the push-out `E0Pushout` built (`exists_e0Pushout`), its GH modulo the mixed diamonds
  (`E0Pushout.isCompact_diamond_mixed`); Cauchy-complete from WP-41j.
* `brunswic2021cauchy:cor:abs_max` (Cor 2.18) — `BTZ_1.tex:1083–1086` (partial):
  `GX.E0AbsMax.cor_abs_max_e0` (DEC-28's input; no `hLine`).

The `_e0` declarations carry NO model-fact hypothesis; the `hLine`-forms (same names without
`_e0`) are kept for `GXScaffold.BTZ.Uniformization`, and `hLine := e0_hLine` turns one into the
other.

> Let $M_0\xrightarrow{\iota} M_1$ be a BTZ-extension of $\mass{\geq0}$-manifolds. (a) $\iota(M_0)$
> is causally convex in $M_1$ iff $\forall x\in \sing_0(M_0), \sing_0[J^+(\iota(x))] \subset
> \iota(M_0)$. (b) If $M_0$ is globally hyperbolic then $\iota(M_0)$ is causally convex. (l.999–1006)
>
> If $M_2$ is globally hyperbolic and $\sing_0(M_2)=j(\sing_0(M_0))$, then $M_3$ is a
> $\mass{\geq0}$-manifold. (l.954) Let $M$ be a globally hyperbolic Cauchy-compact $\mass{0}$-manifold.
> If $M$ is Cauchy-maximal then $\Reg(M)$ is globally hyperbolic Cauchy-complete and absolutely
> maximal in the sense of Barbot. (l.1081–1084)

## What is proved (0 `sorry` unless named)

* §1 model-free: Remark 1; diamonds inside an open set; transport of GH onto an image; a compact
  acausal Cauchy surface of a connected GH spacetime is connected (no splitting).
* §2 under `SingularFlatAxioms`: Lemma 2.13 (a), (b); Reg causally convex; GH ⇒ strongly causal;
  the two-open causality and diamond lemmas of Prop 2.17; (WP-43c) `exists_nhds_diff_sing_subset_Iplus`
  (regular points near `z > p` on a BTZ line are in `I⁺(p)`), `lt_reg_of_lt`.
* §3–§6 `𝔼₀`-manifolds. **WP-43c: (O2) is discharged** — `e0_sfa_of_globalBTZ`, `e0_hLine`
  (`E0LM.e0_globalBTZ`, sorry-free since WP-43d); the `hLine`-forms are kept for their callers.
  **Lemma 2.12 (§4a)**: for `(p, q)` in the closure of the graph of `f`, a BTZ `p` is refuted by a
  decreasing chronological sequence `bₙ → p`, the cluster point `q'` of `f(bₙ)`, the diamonds
  `J(q', f bₙ)` shrinking into a chart ball `O ∋ q'`, a BTZ `z > p` with a neighbourhood whose
  regular part lies in `I⁺(p) ∩ I⁻(bₙ)` — and the **holonomy step** `exists_nhds_not_mapsTo`:
  `f` read in a chart of `M` at `z` and (after a translation) a chart of the maximal a.e. atlas of
  `𝔼₀` is an injective local `G`-structomorphism on the regular part of a connected neighbourhood of
  the singular `κ z`, which `GX.e0_localUnique_sing` (B21 `prop:isom_strong`) extends by an element
  of `G` sending `κ z` into the compact regular closure of the image: impossible. **The push-out
  atlas (§4b)**: `FlatE0 N` (`N` with charts `· ≫ inl`, `HasGroupoid` by `inlConj_mem`),
  `flatE0_rel_iff` (its charted causality is `flatCausality N`), `f` and `f⁻¹` `𝔼₀`-morphisms
  (`isE0Mor_regExt`, `isE0Mor_regInv`), `Causal.CBG.gluedChartedSpace` on `Causal.Gluing val f`.
  Earlier: Prop 2.16 through lemma K; `E0Pushout.globallyHyperbolic` modulo the mixed diamonds;
  `ce_opens_eq`, `flatCausality_e0RegM_eq`, `gh_e0RegMFlat`. Lemma 2.14 / Cor 2.15 for
  `𝔼₀`-manifolds (`_e0`, §3), the loop lemma their one `sorry`.
* §7 the unconditional (`hLine`-free) forms of Props 2.16, 2.17 and Cor 2.18.

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifolds (Lemmas 2.13–2.15) | ⚠ abstract forms: any causality with `SingularFlatAxioms`, a NAMED model-fact hypothesis for massive cones (kb/0012; those rows partial); Lemmas 2.14/2.15 abstractly also take the loop exclusion `NoCausalLoopIn` (explicit). `𝔼₀`-manifolds (M1): unconditional — Lemma 2.13 `_e0` sorry-free; Lemmas 2.14/2.15 `_e0` through the tagged loop `sorry`; open-set form (kb/0001) |
| `𝔼_A`-manifolds (Props 2.16–2.17, Cor 2.18) | ⚠ `A = {0}` (harmless for gx, DEC-77(c)): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable (DEC-66) |
| `SingularFlatAxioms` of `𝔼₀`-manifolds | ✓ **discharged** (WP-43c): `e0_sfa_of_globalBTZ`; the `hLine` of the non-`_e0` statements is `e0_hLine`, and every Prop 2.16 / 2.17 / Cor 2.18 row has an `hLine`-free `_e0` declaration (§7) |
| Cauchy-compact / Cauchy-maximal | ✓ `E0CauchyCompact`; `E0Spear.IsE0CauchyMaximal` (DEC-77(c)) |
| `𝔼_A`-maximal | ⚠ `IsE0Maximal`, targets `N` **connected** (finding: unrestricted, no `M` is maximal) |
| absolutely maximal (Barbot) | ✓ `Causal.Flat.AbsMax (fun _ => True)` over `FlatSpacetime.{0} 2` |
| Prop 2.16: smooth splitting, O'Neill Lemma 45, intersection theory | ⚠ replaced by lemma K; its local input `isLocallyCauchy_image` a tagged `sorry` |
| Lemma 2.12: general `M₀ → M₁`, `M₂` | ⚠ the case Prop 2.17 uses: `M₀ = Reg M`, `M₂ = N` flat GH (sing₀ = ∅); proved |

## SCOPE (disclosed; three tagged `sorry`s, down from five)

`sing_eq_of_le_of_le_of_stronglyCausalOn_e0` (Lemma 2.14's BTZ loop in an `𝔼₀`-manifold: the tube
of B21 l.1035–1036; WP-43c fixer: the abstract `SingularFlatAxioms` form, possibly unprovable, is
removed, and the abstract Lemma 2.14 / Cor 2.15 take the loop exclusion `NoCausalLoopIn` as an
explicit hypothesis, sorry-free),
`isLocallyCauchy_image` (Prop 2.16's local graph/Cauchy-domain theory in `𝔼₀`),
`E0Pushout.isCompact_diamond_mixed` (Prop 2.17's spear case, through B21 Lemma 2.3, upstream
sorries in `GXScaffold.BTZ.Spear`). Upstream: `regM_isCauchyComplete` (WP-41j). Closed by WP-43c:
`lem_extension_hausdorff`, `exists_e0Pushout`. Each remaining `sorry` names its obstruction.

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
`𝔼₀`-manifolds it is `sing_eq_of_le_of_le_of_stronglyCausalOn_e0`. -/
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
1035–1036`): in an `𝔼₀`-manifold `M`, for an open `A` with BTZ complement (a BTZ-extension
`A ↪ M`) which is strongly causal, two BTZ points causal to each other are equal — no closed
future causal curve lies in `sing₀(M)`. -/
theorem sing_eq_of_le_of_le_of_stronglyCausalOn_e0 {A : Opens M} (_hA : (A : Set M)ᶜ ⊆ S0 M)
    (_hSC : StronglyCausalOn (CE M) A) {x y : M} (_hx : x ∈ S0 M) (_hy : y ∈ S0 M)
    (_hxy : (CE M).le ⊤ x y) (_hyx : (CE M).le ⊤ y x) : x = y := by
  sorry -- SORRY(brunswic2021cauchy:Lemma 2.14): the closed future causal curve c inside sing₀(M) through x ≠ y (x ≤ y ≤ x on one BTZ line). B21 l.1035–1036: from a finite cover of c by 𝔼₀ charts (exists_cyl_chart) and Prop 1.3 (chart changes at BTZ points are rotation-translations: GX.e0_localUnique_sing / Rigid's localUnique_sing), a neighbourhood 𝒰 of c is isomorphic to the tube 𝒯 = ⟨γ⟩\{r < r*} ⊂ 𝔼₀, γ(τ,r,θ) = (τ+τ₀, r, θ+θ₀), τ₀ > 0; the regular causal curve t ↦ (t, r₁, θ₁), 0 < r₁ < r*, lies in Reg M ⊆ A and is closed (θ₀ ∈ ℚπ) or returns arbitrarily close to itself, contradicting strong causality of A. Needs the holonomy of the loop through a chain of 𝔼₀ charts (composition of the rotation-translation chart changes around c) and the identification of 𝒰 with the tube quotient; neither is in the library (E0GlobalBTZ.line gives a closed embedding of the BTZ line only under causality, which is the conclusion sought). The order-theoretic SFA data cannot replace it: regular points never precede BTZ points (mem_sing_zero_of_le), so the loop produces no causal relation between regular points except through the tube's geometry

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
  have hsymm : ∀ b (x : pushPiece M N b),
      (Causal.CBG.glueEmb he b).symm (pushEmb f b x) = x := fun b x =>
    Causal.CBG.glueEmb_symm_apply he b x
  have htrans : ∀ i j, ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt
      (Causal.CBG.glueTransition he i j) (pushEmb f i ⁻¹' range (pushEmb f j)) := by
    have hWo : ∀ i j, IsOpen (pushEmb f i ⁻¹' range (pushEmb f j)) := fun i j =>
      (he j).isOpen_range.preimage (he i).continuous
    intro i j
    cases i <;> cases j
    · refine Causal.CBG.liftPropOn_congr_of_eqOn (hWo false false)
        (Causal.CBG.liftPropOn_id (hWo false false)) fun x _ => ?_
      exact (hsymm false x).symm
    · -- `N → M`: `f⁻¹` on `range f`
      have hW : pushEmb f false ⁻¹' range (pushEmb f true) = (range f : Set N) := by
        ext y
        constructor
        · rintro ⟨x, hx⟩
          obtain ⟨w, -, rfl⟩ := (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 hx
          exact ⟨w, rfl⟩
        · rintro ⟨w, rfl⟩
          exact ⟨(toRegM w : M), Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M))
            (j₂ := f) (toRegM w)⟩
      show ChartedSpace.LiftPropOn _ _ (pushEmb f false ⁻¹' range (pushEmb f true))
      rw [hW]
      refine Causal.CBG.liftPropOn_congr_of_eqOn hj₂.isOpen_range (isE0Mor_regInv hf) ?_
      rintro _ ⟨w, rfl⟩
      show regInv hf (f w) = (Causal.CBG.glueEmb he true).symm (pushEmb f false (f w))
      have h1 : pushEmb f false (f w) = pushEmb f true (toRegM w : M) :=
        (Causal.Gluing.ι₁_j₁ (toRegM w)).symm
      rw [regInv_apply, h1, hsymm]
    · -- `M → N`: `f` on `Reg M`
      have hW : pushEmb f true ⁻¹' range (pushEmb f false) = (E0LM.e0RegM M : Set M) := by
        ext x
        constructor
        · rintro ⟨y, hy⟩
          obtain ⟨w, rfl, -⟩ := (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 hy.symm
          exact w.2
        · intro hx
          exact ⟨f ⟨x, hx⟩, (Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M))
            (j₂ := f) (⟨x, hx⟩ : E0LM.e0RegM M)).symm⟩
      show ChartedSpace.LiftPropOn _ _ (pushEmb f true ⁻¹' range (pushEmb f false))
      rw [hW]
      refine Causal.CBG.liftPropOn_congr_of_eqOn (E0LM.e0RegM M).isOpen
        (isE0Mor_regExt hf (Classical.arbitrary N)) ?_
      intro x hx
      show regExt f _ x = (Causal.CBG.glueEmb he false).symm (pushEmb f true x)
      have h1 : pushEmb f true x = pushEmb f false (f ⟨x, hx⟩) :=
        Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f)
          (⟨x, hx⟩ : E0LM.e0RegM M)
      rw [regExt_apply f _ x hx, h1, hsymm]
    · refine Causal.CBG.liftPropOn_congr_of_eqOn (hWo true true)
        (Causal.CBG.liftPropOn_id (hWo true true)) fun x _ => ?_
      exact (hsymm true x).symm
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

/-- **The mixed diamonds of the push-out are compact** (B21 Prop 2.17's last case,
`BTZ_1.tex:1104–1115`): `p ∈ sing₀(M̄)`, `q` regular. -/
theorem E0Pushout.isCompact_diamond_mixed (_hGH : (CE M).GloballyHyperbolic)
    (_hmax : IsE0CauchyMaximal M) {N : Causal.Flat.FlatSpacetime.{0} 2} (_hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (P : E0Pushout M N f) {p q : P.carrier} (_hp : p ∈ S0 P.carrier)
    (_hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) := by
  sorry -- SORRY(brunswic2021cauchy:prop:abs_max): B21 l.1104–1117 (the push-out and its Hausdorffness are now built, WP-43c; this case is the only obstruction left to E0Pushout.globallyHyperbolic). A causal curve from p to q is BTZ on an initial segment [0, s] and regular after; the regular part lies in ι₂ N, the BTZ part in ι₁ M, and the cut between them must be a COMPACT set of regular points of M through which every such curve passes — a chart neighbourhood V of the BTZ part (exists_cyl_chart) does not do: ∂V meets the BTZ ray beyond q, and the regular exit points of ∂V accumulate at those BTZ points, so J⁺_N(∂V ∩ reg) ∩ J⁻_N(q) is not known compact. B21's cut is the rim of a spear. A spear neighbourhood 𝒮 ⊆ M of vertex p avoiding q (Lemma 2.3, lem_tube — stated in GXScaffold.BTZ.Spear, its gluing resting on four upstream tagged sorries), its rim 𝒞 (compact, regular); K = J⁺(𝒞) ∩ J⁻(q) = J⁺_N(𝒞) ∩ J⁻_N(q) compact (causal convexity of ι₂ N, Lemma 2.13(b) = btzExt_causallyConvexIn_of_globallyHyperbolicOn), K' = K ∩ ∂𝒮; a past causal curve from q to p meets ∂𝒮 last at a point of K' (no past causal curve enters 𝒮 through its head, Spear's frontier_spear), so J(p, q) ⊆ [J⁻_N(q) ∩ J⁺_N(K')] ∪ [J⁻_M(K') ∩ J⁺_M(p)], both compact. Needs Lemma 2.3 sorry-free and the curve-exit argument at the spear's frontier (the curve-extension theory of open subsets that Spear's isCauchySurface_glued also lacks)

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

/-! ### §6 B21 Prop 2.17 and Cor 2.18 -/

include hLine in
/-- **B21 Prop 2.17** (`prop:abs_max`, `BTZ_1.tex:1078–1082`, proof l.1088–1119) for `A = {0}`
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
/-- **B21 Cor 2.18** (`cor:abs_max`, `BTZ_1.tex:1083–1086`; DEC-28's input to the headline): for `M`
a globally hyperbolic Cauchy-compact Cauchy-maximal `𝔼₀`-manifold, `Reg(M)` is globally hyperbolic,
Cauchy-complete and absolutely maximal in the sense of Barbot. Cauchy-compact as printed
(`E0CauchyCompact`); connectedness of the Cauchy surface proved (`isConnected_of_isCauchySurface`). -/
theorem cor_abs_max (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  obtain ⟨S, hS, hSc, hSac⟩ := hCC
  exact prop_abs_max hLine hGH hS hSc hSac hmax

/-! ### §7 The unconditional forms (no `hLine`: (O2) is `e0_hLine`)

The primary declarations of the Prop 2.16 / 2.17 / Cor 2.18 rows: each `hLine`-form above with
its (O2) hypothesis discharged by `e0_hLine` (`E0LM.e0_globalBTZ`, sorry-free). The `hLine`-forms
are kept because downstream files (`GXScaffold.BTZ.Uniformization`) pass their own `hLine`. -/

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

/-- **B21 Prop 2.17** (`prop:abs_max`, `BTZ_1.tex:1078–1082`, proof l.1088–1119) for `A = {0}`,
unconditional: `Reg M` globally hyperbolic, Cauchy-complete and absolutely maximal. -/
theorem prop_abs_max_e0 (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  prop_abs_max e0_hLine hGH hS hSc hSac hmax

/-- **B21 Cor 2.18** (`cor:abs_max`, `BTZ_1.tex:1083–1086`; DEC-28's input to the headline),
unconditional: for `M` a globally hyperbolic Cauchy-compact Cauchy-maximal `𝔼₀`-manifold,
`Reg(M)` is globally hyperbolic, Cauchy-complete and absolutely maximal in Barbot's sense. -/
theorem cor_abs_max_e0 (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  cor_abs_max e0_hLine hGH hCC hmax

end E0

end E0AbsMax

end GX
