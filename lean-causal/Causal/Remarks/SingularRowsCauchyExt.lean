import Causal.Remarks.SingularRowsDiamond
import Causal.Port.CupCapBTZCounterexample
import Causal.Remarks.SingularRowsSplitting
import Causal.Flat.SplittingFull

/-!
# A Cauchy extension between `E_{≥0}`-manifolds that is not onto: `{T < a}` inside `E₀`

Target `T-ett-cauchy-ext-e0`. Cited, all unmarked (SCOPE):
`def:cauchy_embedding_cauchy_extension` — `ETT.tex:1858`, an instance between `E_{≥0}`-manifolds
that is not onto;
`lem:Cauchy_plongement_toutes` — `ETT.tex:1865`, witnessed at it;
`lem:image_diamant` — `ETT.tex:2024`, witnessed at it, at a BTZ point;
`lem:passe_pgcd` — `ETT.tex:2042`, as printed, witnessed at it at a BTZ point and at a regular
point of `∂ i(M) ∩ J⁺(i(Σ))`.

For a Cauchy time function `T` of `E₀` strictly increasing along `≤` and any `a`, the open set
`{T < a}`, with the pulled-back structure (DEC-25) and its natural causality, is a globally
hyperbolic, connected `E₀`-manifold, and its inclusion `i` into `E₀` is a Cauchy extension that
is not onto. The rows of `Causal.Remarks.SingularRowsDiamond` and
`Causal.Remarks.SingularRowsCauchy` are instantiated at `i`, which is not onto: `lem:passe_pgcd`
at points of the frontier `T⁻¹(a)` of its range, `lem:image_diamant` at an interior BTZ point (as
the lemma requires), `lem:Cauchy_plongement_toutes` at `i` itself.

> Let $M$ and $N$ be globally hyperbolic singular flat spacetimes. A \emph{Cauchy embedding} of
> $M$ into $N$ is an injective $\mass{\geq0}$-morphism $\phi:M\rightarrow N$ carrying some Cauchy
> surface of $M$ onto a Cauchy surface of $N$. We then say that $N$, together with $\phi$, is a
> \emph{Cauchy extension} of $M$. (`def:cauchy_embedding_cauchy_extension`, `ETT.tex:1859–1862`)

> for every Cauchy surface $\Sigma$ of $M$, the image $\phi(\Sigma)$ is a Cauchy surface of $N$.
> (`lem:Cauchy_plongement_toutes` (ii), `ETT.tex:1870`)

> let $i:M\rightarrow N$ be a Cauchy extension and let $p\in J^+_M(\Sigma)$. Then
> $$i\left(J_M(\Sigma,p)\right)=J_N\left(i(\Sigma),i(p)\right).$$
> (`lem:image_diamant`, `ETT.tex:2025–2027`)

> let $i:M\rightarrow N$ be a Cauchy extension and let
> $p\in \partial i(M)\cap J^+\left(i(\Sigma)\right)$. Then
> $$K^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M);$$ explicitly,
> $I^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M)$ if $p\notin \sing_0(N)$, and
> $J_N\left(i(\Sigma),p\right)\setminus \{p\}\subset i(M)$ if $p\in \sing_0(N)$.
> (`lem:passe_pgcd`, `ETT.tex:2043–2048`)

## What is proved (no `sorry` in this file)

* **Model-free** (namespace `Causality`). The relations of an open past set `U` are those of `M`
  restricted (`le_iff_le_top_of_isPast`, `lt_iff_lt_top_of_isPast`, `M` causally
  arc-connected; `causallyConvexIn_of_isPast`). **The past-set lemma**
  `isCauchySurfaceOn_of_isPast`: in a causally arc-connected causal `M` with a continuous `T`
  strictly increasing along `≤`, a Cauchy surface `S` of `M` inside an open past set `W` is a
  Cauchy surface of `W` (section `CurveExt`, ported from lean-gx, SCOPE).
  `SingularRowsCauchyExt.isEMorphism_val_of_chartIso`: the inclusion of an open set which is a
  chart isomorphism is an injective abstract `𝕄≥0`-morphism.
* **At `E₀`**, for every Cauchy time function `T` strictly increasing along `≤` (one exists,
  `exists_cauchyTimeFunction`) and every `a`: `sublevel = {T < a}` is a past set
  (`isPast_sublevel`); every `T⁻¹(b)` is a Cauchy surface of `E₀` and, for `b < a`, of `{T < a}`
  (`isCauchySurface_level`, `isCauchySurfaceOn_sublevel`). **The construction**,
  `cauchyExtension`: `{T < a}` is an `E₀`-manifold with a unique natural causality `C`, and for
  it `C` is absolutely minimal with `IsoChartsCoverDEC25` over the family, its relations at `⊤`
  are `E₀`'s, it is globally hyperbolic, `i⁻¹(T⁻¹(b))` is a Cauchy surface for `b < a`, `i`
  is an `IsCauchyEmbedding`, and `i` is not onto. `{T < a}` is connected
  (`connectedSpace_sublevel`), so a singular flat spacetime of the library
  (`singularFlatSpacetime_sublevel`).
* **Witnesses** (kb/0011), each conclusion out of the row's own M-level theorem, at `i`, which is
  not onto, with `Σ = i⁻¹(T⁻¹(b))`, `b < a`:
  `image_diamant_witness` (`SingularRowsDiamond.image_diamant`) at a BTZ point `p` with
  `b < T p < a`: `i(J⁺(Σ) ∩ J⁻(p)) = J⁺(T⁻¹(b)) ∩ J⁻(p)`, while `J⁺(T⁻¹(b)) ⊄ i(M)`;
  `passe_pgcd_btz_witness` (`passe_pgcd_printed`) at the BTZ point `p₁` with `T p₁ = a`, in
  `∂ i(M) ∩ J⁺(T⁻¹(b))` and not in `i(M)`: the inclusion and the BTZ form, the set
  `J(T⁻¹(b), p₁) ∖ {p₁}` non-empty; `passe_pgcd_regular_witness` at a regular `q₁` with
  `T q₁ = a`: the inclusion and the regular form, `I⁻(q₁) ∩ J⁺(T⁻¹(b))` non-empty;
  `plongement_witness` (`SingularRowsCauchy.cauchy_plongement_toutes_manifolds`): (i) ⇔ (ii) at
  `i`, (ii), and `i(i⁻¹(T⁻¹(c)))` a Cauchy surface of `E₀` for every `c < a`. Assembled at the
  Geroch time and `a = 1`: `nonvacuous_e0`.

## Hypothesis checklist

| paper | here |
|---|---|
| `M`, `N` globally hyperbolic singular flat spacetimes | ⚠ read (DEC-25, OQ-18): `M = {T < a}` (`opensSingularGXStructure`, natural causality `SFALocalE0.IsE0Natural`), `N = E₀` (`E0GX.singularGX`, `E0.causality`); both globally hyperbolic, `M` connected, Hausdorff, second countable — proved |
| `φ` an injective `E_{≥0}`-morphism (DEC-17) | ✓ `IsEMorphism C E0.causality Subtype.val`, injective |
| some Cauchy surface of `M` onto one of `N` | ✓ `i⁻¹(T⁻¹(b))` onto `T⁻¹(b)` |
| `p ∈ J⁺_M(Σ)` (`lem:image_diamant`) | ✓ met at a BTZ point |
| `p ∈ ∂ i(M) ∩ J⁺(i(Σ))` (`lem:passe_pgcd`) | ✓ met at `p₁ ∈ sing₀(N)` and at `q₁ ∉ sing₀(N)`, neither in `i(M)` |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** These are witnesses and an instance; the rows are proved in
  `Causal.Remarks.SingularRowsDiamond`, `SingularRowsCauchy`, `Causal.CauchyExtension`, and
  rest on DEC-25 and the readings OQ-18, OQ-34, OQ-35, OQ-82. Nothing is marked.
* **What the witnesses show** (AUDIT-1). `{T < a}` is a past set, so each witnessed conclusion
  also follows in a line from `isPast_sublevel`. The witnesses show that the rows' hypotheses are
  met off the range of a Cauchy embedding, not the depth of the rows' proofs.
* **A subtype in the statements** (kb/0001 set aside): the rows quantify over manifolds `M`, so
  the source of a Cauchy extension that is not onto is the type `↥{T < a}`.
* **The points** `p`, `p₁`, `q₁` lie on τ-orbits (`SingularRowsSplitting.tauFlow`) of
  `(0, 0)` (the axis) and `(0, 1)`, at the times where `T` takes the values `(a + b)/2` and `a`:
  each level of `T` is a Cauchy surface, which every orbit meets.
* **The route's step (b)** assumed an inextensible curve of `M` over `I' ⊇ I` extending `c`, from
  `curvesExtend_of_t1_secondCountable`; the library's `CurvesExtend` only gives
  `c(I) ⊆ c'(I')`, with no reparametrisation, and a strict extension in `U` is not built from it.
  The past-set lemma is instead the time-graph argument (`exists_inextensible_of_timeFunction`,
  `T ∘ γ = id`), with `T` the Cauchy time function itself. Whether it holds with curve extension
  alone is not examined.
* **Ported, not rewritten**: section `CurveExt` is `lean-gx/GX/BTZ/Spear.lean` l.1183–1511 at
  `8b15f9e` (`GX.E0Spear` there), character for character except one token (its l.171:
  `le_of_lt` is `_root_.le_of_lt`, kb/0016); its universe is gx's `X : Type`. lean-causal never
  imports lean-gx (DEC-33).
* **Not done**: the natural-causality forms through `rows_of_isAtlasCausalityDEC25`
  (`MassACovered` and `IsAtlasCausalityDEC25` of `{T < a}` are not derived); the construction at
  every globally hyperbolic `E₀`-manifold (`relations_top_iff` is for open sets of `E₀` only).
* **Prose this made stale** (`Causal/Remarks/SingularRowsDiamond.lean`'s witnesses item, kb/0201,
  the ledger notes of `lem:image_diamant` and `lem:passe_pgcd`) was updated at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.Remarks.SingularRowsDiamond`, `Causal.Port.CupCapBTZCounterexample` (section `E0Opens`),
`Causal.Remarks.SingularRowsSplitting` (the τ-flow) and `Causal.Flat.SplittingFull`
(`IsCauchyTimeFunction.isCauchySurface_level`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u

namespace Causality

section PastSet

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- A past set is causally convex in `M`. -/
theorem causallyConvexIn_of_isPast {U : Set M} (hU : ∀ x y, x ∈ U → C.le ⊤ y x → y ∈ U) :
    C.CausallyConvexIn U ⊤ :=
  ⟨fun _ _ => trivial, fun _ _ q hq z hz => hU q z hq (mem_diamond.1 hz).2⟩

/-- **The relations of an open past set are those of `M`, restricted** (causally arc-connected
`M`): a causal curve of `M` ending in `U` stays in `U`. -/
theorem le_iff_le_top_of_isPast (hC : C.CausallyArcConnected) {U : Opens M}
    (hU : ∀ x y, x ∈ U → C.le ⊤ y x → y ∈ U) {x y : M} (hy : y ∈ U) :
    C.le U x y ↔ C.le ⊤ x y :=
  ⟨fun h => C.le_mono le_top h, fun h =>
    le_of_causallyConvexIn hC (causallyConvexIn_of_isPast hU) subset_rfl (hU y x hy h) hy h⟩

/-- The chronological half of `le_iff_le_top_of_isPast`. -/
theorem lt_iff_lt_top_of_isPast (hC : C.CausallyArcConnected) {U : Opens M}
    (hU : ∀ x y, x ∈ U → C.le ⊤ y x → y ∈ U) {x y : M} (hy : y ∈ U) :
    C.lt U x y ↔ C.lt ⊤ x y :=
  ⟨fun h => C.lt_mono le_top h, fun h =>
    lt_of_causallyConvexIn hC (causallyConvexIn_of_isPast hU) (hU y x hy (C.le_of_lt h)) hy h⟩

end PastSet

section CurveExt

variable {X : Type} [TopologicalSpace X] {C : Causal.Causality X} {W : Opens X}

/-- A causal curve read through a continuous non-decreasing change of parameter is a causal
curve (constant pieces allowed: `≤_N` is reflexive). -/
theorem causalCurveOn_comp_monotoneOn {γ : ℝ → X} {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : C.CausalCurveOn W γ (h a) (h b)) (hh : MonotoneOn h (Icc a b))
    (hhc : ContinuousOn h (Icc a b)) : C.CausalCurveOn W (γ ∘ h) a b := by
  have hmaps : ∀ s ∈ Icc a b, h s ∈ Icc (h a) (h b) := fun s hs =>
    ⟨hh ⟨le_rfl, hab⟩ hs hs.1, hh hs ⟨hab, le_rfl⟩ hs.2⟩
  refine ⟨fun t ht => hγ.mem _ (hmaps t ht), fun t ht N hN htN => ?_⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hγ.rel (h t) (hmaps t ht) N hN htN
  have hpre : h ⁻¹' Ioo l u ∈ 𝓝[Icc a b] t := hhc t ht (Ioo_mem_nhds hl hu)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  have hin : ∀ s ∈ Icc a b, t - δ < s → s < t + δ → h s ∈ Ioo l u := fun s hs h1 h2 =>
    hball ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs⟩
  -- every value of `γ ∘ h` in the window lies in `N`
  have hmemN : ∀ s ∈ Icc a b, t - δ < s → s < t + δ → γ (h s) ∈ N := by
    intro s hs h1 h2
    obtain ⟨hl', hu'⟩ := hin s hs h1 h2
    rcases lt_trichotomy (h s) (h t) with e | e | e
    · exact C.isRelFamily_le.mem_left (hrel _ (hmaps s hs) _ (hmaps t ht) hl' e hu)
    · rw [e]; exact htN
    · exact C.isRelFamily_le.mem_right (hrel _ (hmaps t ht) _ (hmaps s hs) hl e hu')
  refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have e := hh hs hs' h2.le
  rcases e.lt_or_eq with e | e
  · exact hrel _ (hmaps s hs) _ (hmaps s' hs') (hin s hs h1 (h2.trans h3)).1 e
      (hin s' hs' (h1.trans h2) h3).2
  · show C.le N (γ (h s)) (γ (h s'))
    rw [← e]
    exact C.le_refl (hmemN s hs h1 (h2.trans h3))

/-- The interval form of `causalCurveOn_comp_monotoneOn`. -/
theorem causalCurveIn_comp_monotoneOn {γ : ℝ → X} {h : ℝ → ℝ} {J I' : Set ℝ}
    (hγ : C.CausalCurveIn W J γ) (hne : I'.Nonempty) (hoc : I'.OrdConnected)
    (hh : MonotoneOn h I') (hhc : ContinuousOn h I') (hmaps : MapsTo h I' J) :
    C.CausalCurveIn W I' (γ ∘ h) := by
  refine ⟨hne, hoc, fun a ha b hb => ?_⟩
  rcases le_or_gt a b with hab | hab
  · have hsub : Icc a b ⊆ I' := hoc.out ha hb
    exact causalCurveOn_comp_monotoneOn hab (hγ.curve _ (hmaps ha) _ (hmaps hb)) (hh.mono hsub)
      (hhc.mono hsub)
  · exact Causal.CurveOn.of_lt hab

/-- A causal curve over an interval is continuous on it. -/
theorem continuousOn_of_causalCurveIn {I : Set ℝ} {c : ℝ → X} (hc : C.CausalCurveIn W I c) :
    ContinuousOn c I := by
  intro s hs
  by_cases hleft : ∃ j ∈ I, j < s
  · obtain ⟨j, hj, hjs⟩ := hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc j i ∈ 𝓝[I] s :=
        nhdsWithin_le_nhds (Icc_mem_nhds hjs hsi)
      exact ((hc.continuousOn_Icc hj hi) s ⟨hjs.le, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hmem : Icc j s ∈ 𝓝[I] s := by
        refine mem_nhdsWithin.2 ⟨Ioi j, isOpen_Ioi, hjs, fun x hx => ⟨hx.1.le, hright x hx.2⟩⟩
      exact ((hc.continuousOn_Icc hj hs) s ⟨hjs.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  · push Not at hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc s i ∈ 𝓝[I] s := by
        refine mem_nhdsWithin.2 ⟨Iio i, isOpen_Iio, hsi, fun x hx => ⟨hleft x hx.2, hx.1.le⟩⟩
      exact ((hc.continuousOn_Icc hs hi) s ⟨le_rfl, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hI : I ⊆ {s} := fun x hx => le_antisymm (hright x hx) (hleft x hx)
      exact (continuousWithinAt_singleton (f := c) (x := s)).mono hI

variable {T : X → ℝ} {J I : Set ℝ} {γ c : ℝ → X}

/-- **Extension at an open, bounded future end along a time-parametrised curve.** -/
theorem extensible_of_timeGraph_openEnd (hγ : C.CausalCurveIn W J γ)
    (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t) (hmono : MonotoneOn (T ∘ c) I)
    (hTcont : ContinuousOn (T ∘ c) I) (hbdd : BddAbove I) (hnomax : ∀ t ∈ I, ∃ s ∈ I, t < s)
    {t' : ℝ} (ht' : t' ∈ J) (hlt : ∀ t ∈ I, T (c t) < t') : C.Extensible W I c := by
  have hne := hc.nonempty
  set b := sSup I with hb
  have hltb : ∀ t ∈ I, t < b := fun t ht => by
    obtain ⟨s, hs, hts⟩ := hnomax t ht
    exact hts.trans_le (le_csSup hbdd hs)
  have hTbdd : BddAbove ((T ∘ c) '' I) := ⟨t', by rintro _ ⟨t, ht, rfl⟩; exact (hlt t ht).le⟩
  have hTne : ((T ∘ c) '' I).Nonempty := hne.image _
  set k := sSup ((T ∘ c) '' I) with hk
  have hTk : ∀ t ∈ I, T (c t) ≤ k := fun t ht => le_csSup hTbdd ⟨t, ht, rfl⟩
  have hkt' : k ≤ t' := csSup_le hTne (by rintro _ ⟨t, ht, rfl⟩; exact (hlt t ht).le)
  obtain ⟨t₀, ht₀⟩ := hne
  set L := t' - k with hL
  set I' : Set ℝ := I ∪ Icc b (b + L) with hI'
  set hfun : ℝ → ℝ := fun s => if s < b then T (c s) else k + (s - b) with hhfun
  have hlow : ∀ s ∈ I', s < b → s ∈ I := by
    rintro s (hs | hs) hsb
    · exact hs
    · exact absurd hs.1 (not_le.2 hsb)
  have hoc : I'.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases lt_or_ge z b with hzb | hzb
    · have hxI : x ∈ I := hlow x hx (hz.1.trans_lt hzb)
      obtain ⟨i, hi, hzi⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hzb
      exact Or.inl (hc.ordConnected.out hxI hi ⟨hz.1, hzi.le⟩)
    · rcases hy with hy | hy
      · exact absurd (hltb y hy) (not_lt.2 (hzb.trans hz.2))
      · exact Or.inr ⟨hzb, hz.2.trans hy.2⟩
  have hTJ : ∀ s ∈ I', hfun s ∈ J := by
    intro s hs
    rcases lt_or_ge s b with hsb | hsb
    · simp only [hhfun, if_pos hsb]; exact (hcγ s (hlow s hs hsb)).1
    · simp only [hhfun, if_neg (not_lt.2 hsb)]
      have hs' : s ∈ Icc b (b + L) := by
        rcases hs with hs | hs
        · exact absurd (hltb s hs) (not_lt.2 hsb)
        · exact hs
      refine hγ.ordConnected.out (hcγ t₀ ht₀).1 ht' ⟨?_, ?_⟩
      · linarith [hTk t₀ ht₀, hs'.1]
      · linarith [hs'.2]
  have hmonoh : MonotoneOn hfun I' := by
    intro x hx y hy hxy
    rcases lt_or_ge y b with hyb | hyb
    · have hxb : x < b := hxy.trans_lt hyb
      simp only [hhfun, if_pos hxb, if_pos hyb]
      exact hmono (hlow x hx hxb) (hlow y hy hyb) hxy
    · simp only [hhfun, if_neg (not_lt.2 hyb)]
      rcases lt_or_ge x b with hxb | hxb
      · simp only [if_pos hxb]; linarith [hTk x (hlow x hx hxb)]
      · simp only [if_neg (not_lt.2 hxb)]; linarith
  have hcont : ContinuousOn hfun I' := by
    intro s hs
    rcases lt_trichotomy s b with hsb | hsb | hsb
    · -- below `b`, `hfun = T ∘ c`
      have hsI : s ∈ I := hlow s hs hsb
      have hmem : I ∈ 𝓝[I'] s := mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hsb,
        fun x hx => hlow x hx.2 hx.1⟩
      have h1 : ContinuousWithinAt hfun I s := by
        refine (hTcont s hsI).congr (fun x hx => ?_) ?_
        · simp only [hhfun, if_pos (hltb x hx)]; rfl
        · simp only [hhfun, if_pos hsb]; rfl
      exact h1.mono_of_mem_nhdsWithin hmem
    · -- at `b`
      rw [hsb]
      have hb' : hfun b = k := by
        simp only [hhfun, lt_irrefl, if_false, sub_self, add_zero]
      refine ContinuousWithinAt.union ?_ ?_
      · rw [ContinuousWithinAt, hb', Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        obtain ⟨_, ⟨i, hi, rfl⟩, hki⟩ := exists_lt_of_lt_csSup hTne (show k - ε < k by linarith)
        refine ⟨b - i, by linarith [hltb i hi], fun x hx hxd => ?_⟩
        have hxb := hltb x hx
        rw [Real.dist_eq, abs_lt] at hxd
        have hix : i ≤ x := by linarith [hxd.1]
        have hfx : hfun x = T (c x) := by simp only [hhfun, if_pos hxb]
        rw [hfx, Real.dist_eq, abs_lt]
        have := hmono hi hx hix
        simp only [Function.comp] at this hki
        constructor <;> linarith [hTk x hx]
      · have : ContinuousOn (fun s => k + (s - b)) (Icc b (b + L)) := by
          fun_prop
        refine (this _ ⟨le_rfl, by linarith⟩).congr (fun x hx => ?_) ?_
        · rcases hx.1.lt_or_eq with hx' | hx'
          · simp only [hhfun, if_neg (not_lt.2 hx'.le)]
          · simp only [hhfun, ← hx', lt_irrefl, if_false]
        · rw [hb']; ring
    · -- above `b`, affine
      have hmem : Ioi b ∈ 𝓝[I'] s := nhdsWithin_le_nhds (Ioi_mem_nhds hsb)
      have h1 : ContinuousWithinAt (fun s => k + (s - b)) I' s :=
        (by fun_prop : Continuous (fun s : ℝ => k + (s - b))).continuousWithinAt
      refine h1.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hsb)] with x hx
        simp [hhfun, not_lt.2 (_root_.le_of_lt (show b < x from hx))]
      · simp [hhfun, not_lt.2 hsb.le]
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hcurve : C.CausalCurveIn W I' (γ ∘ hfun) :=
    causalCurveIn_comp_monotoneOn hγ ⟨t₀, Or.inl ht₀⟩ hoc hmonoh hcont hTJ
  refine ⟨I', γ ∘ hfun, hcurve, ⟨id, strictMonoOn_id, fun t ht => Or.inl ht,
    by rw [image_id]; exact hc.ordConnected, fun t ht => ?_⟩,
    ⟨b + L, Or.inr ⟨by linarith, le_rfl⟩, fun t ht heq => ?_⟩⟩
  · show γ (hfun t) = c t
    simp only [hhfun, if_pos (hltb t ht)]
    exact (hcγ t ht).2
  · have h1 : hfun (b + L) = t' := by
      simp only [hhfun, if_neg (not_lt.2 (show b ≤ b + L by linarith))]
      rw [hL]; ring
    have h2 : T ((γ ∘ hfun) (b + L)) = t' := by
      simp only [Function.comp, h1]; exact hTγ t' ht'
    rw [heq] at h2
    linarith [hlt t ht]

/-- **A causal curve lying on a time-parametrised curve `γ` that goes further to the future is
extensible** (constant pieces of `c` allowed). -/
theorem extensible_of_timeGraph_future (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hγ : C.CausalCurveIn W J γ) (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t)
    {t' : ℝ} (ht' : t' ∈ J) (hlt : ∀ t ∈ I, T (c t) < t') : C.Extensible W I c := by
  by_cases hmax : ∃ b, IsGreatest I b
  · obtain ⟨b, hb⟩ := hmax
    refine Causal.Causality.extensible_of_isGreatest hC hcaus hc hb fun heq => ?_
    have hmem : γ t' ∈ C.Jplus W {c b} := by
      refine ⟨c b, rfl, ?_⟩
      have := hγ.le_of_le (hcγ b hb.1).1 ht' (hlt b hb.1).le
      rwa [(hcγ b hb.1).2] at this
    rw [heq, mem_singleton_iff] at hmem
    have h2 := hTγ t' ht'
    rw [hmem] at h2
    linarith [hlt b hb.1]
  · push Not at hmax
    have hnomax : ∀ t ∈ I, ∃ s ∈ I, t < s := fun t ht => by
      by_contra h
      push Not at h
      exact hmax t ⟨ht, h⟩
    have htan : ∀ t, Real.tan (Real.arctan t) = t := Real.tan_arctan
    set I₁ := Real.arctan '' I with hI₁
    set d : ℝ → X := c ∘ Real.tan with hd
    have hsub : I₁ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t⟩
    have hmaps : MapsTo Real.tan I₁ I := by
      rintro _ ⟨t, ht, rfl⟩; rw [htan]; exact ht
    have hdc : C.CausalCurveIn W I₁ d :=
      hc.comp (hc.nonempty.image _)
        (isPreconnected_iff_ordConnected.1
          (hc.ordConnected.isPreconnected.image _ Real.continuous_arctan.continuousOn))
        (Real.strictMonoOn_tan.mono hsub) (Real.continuousOn_tan_Ioo.mono hsub) hmaps
    have hdγ : ∀ s ∈ I₁, T (d s) ∈ J ∧ γ (T (d s)) = d s := by
      rintro _ ⟨t, ht, rfl⟩
      simp only [hd, Function.comp, htan]
      exact hcγ t ht
    have hdext : C.Extensible W I₁ d := by
      refine extensible_of_timeGraph_openEnd hγ hTγ hdc hdγ
        (fun x hx y hy hxy => Causal.Causality.CausalCurveIn.time_mono hT hdc hx hy hxy)
        (hTc.comp_continuousOn (continuousOn_of_causalCurveIn hdc))
        ⟨Real.pi / 2, fun x hx => (hsub hx).2.le⟩ ?_ ht' ?_
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨u, hu, htu⟩ := hnomax t ht
        exact ⟨Real.arctan u, ⟨u, hu, rfl⟩, Real.arctan_strictMono htu⟩
      · rintro _ ⟨t, ht, rfl⟩
        simp only [hd, Function.comp, htan]
        exact hlt t ht
    exact hdext.of_comp (ψ := Real.arctan) (Real.arctan_strictMono.strictMonoOn _)
      (mapsTo_image _ _) (surjOn_image _ _) fun t _ => by simp only [hd, Function.comp, htan]

/-- The past form of `extensible_of_timeGraph_future` (reversed causality). -/
theorem extensible_of_timeGraph_past (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hγ : C.CausalCurveIn W J γ) (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t)
    {t' : ℝ} (ht' : t' ∈ J) (hgt : ∀ t ∈ I, t' < T (c t)) : C.Extensible W I c := by
  apply Causal.Causality.Extensible.of_dual_reverse
  refine extensible_of_timeGraph_future (C := C.dual) (T := fun x => -T x) (J := -J)
    (γ := fun τ => γ (-τ)) (Causal.Causality.dual_causallyArcConnectedOn.2 hC)
    (Causal.Causality.dual_isCausal.2 hcaus) hTc.neg ?_ hγ.reverse ?_ hc.reverse ?_
    (t' := -t') (by simpa using ht') ?_
  · intro x y hxy hne
    have := hT y x hxy (Ne.symm hne)
    linarith
  · intro τ hτ
    have := hTγ (-τ) hτ
    simp only [this, neg_neg]
  · intro t ht
    obtain ⟨h1, h2⟩ := hcγ (-t) ht
    refine ⟨by simpa using h1, ?_⟩
    simp only [neg_neg]; exact h2
  · intro t ht
    have := hgt (-t) ht
    linarith

/-- **A Cauchy surface of `X` inside an open past set `W` is a Cauchy surface of `W`**, given a
continuous function strictly increasing along `≤`. -/
theorem isCauchySurfaceOn_of_isPast (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hW : ∀ x y, x ∈ W → C.le ⊤ y x → y ∈ W) {S : Set X} (hSW : S ⊆ W)
    (hS : C.IsCauchySurface S) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  have hcT := hc.1.mono_opens le_top
  obtain ⟨J, γ, hγ, hsub, hTγ⟩ := Causal.Causality.exists_inextensible_of_timeFunction hTc hT hcT
  obtain ⟨_, ⟨⟨tS, htS, rfl⟩, hγS⟩, -⟩ := hS J γ hγ
  have hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t := by
    intro t ht
    obtain ⟨u, hu, hcu⟩ := hsub ⟨t, ht, rfl⟩
    rw [← hcu, hTγ u hu]; exact ⟨hu, rfl⟩
  have hac : C.IsAcausal S := hS.isAcausal_of_timeFunction hC hTc hT
  have hex : ∃ t ∈ I, c t ∈ S := by
    by_contra hno
    push Not at hno
    have hne : ∀ t ∈ I, T (c t) ≠ tS := fun t ht e =>
      hno t ht (by rw [← (hcγ t ht).2, e]; exact hγS)
    set J' : Set ℝ := {u | u ∈ J ∧ (u ≤ tS ∨ ∃ t ∈ I, u ≤ T (c t))} with hJ'
    have hJ'mem : ∀ u ∈ J', γ u ∈ W := by
      rintro u ⟨hu, hu' | ⟨t, ht, hut⟩⟩
      · exact hW _ _ (hSW hγS) (hγ.1.le_of_le hu htS hu')
      · have h1 := hγ.1.le_of_le hu (hcγ t ht).1 hut
        rw [(hcγ t ht).2] at h1
        exact hW _ _ (hc.1.mem ht) h1
    have hJ'oc : J'.OrdConnected := ⟨fun x hx y hy z hz => by
      refine ⟨hγ.1.ordConnected.out hx.1 hy.1 hz, ?_⟩
      rcases hy.2 with h | ⟨t, ht, h⟩
      · exact Or.inl (hz.2.trans h)
      · exact Or.inr ⟨t, ht, hz.2.trans h⟩⟩
    have htS' : tS ∈ J' := ⟨htS, Or.inl le_rfl⟩
    have hγ' : C.CausalCurveIn W J' γ := ⟨⟨tS, htS'⟩, hJ'oc, fun a ha b hb =>
      Causal.CurveOn.restrict (hγ.1.curve a ha.1 b hb.1) le_rfl le_rfl le_top
        fun u hu => hJ'mem u (hJ'oc.out ha hb hu)⟩
    have hcγ' : ∀ t ∈ I, T (c t) ∈ J' ∧ γ (T (c t)) = c t := fun t ht =>
      ⟨⟨(hcγ t ht).1, Or.inr ⟨t, ht, le_rfl⟩⟩, (hcγ t ht).2⟩
    have hTγ' : ∀ τ ∈ J', T (γ τ) = τ := fun τ hτ => hTγ τ hτ.1
    by_cases hall : ∀ t ∈ I, T (c t) < tS
    · exact hc.2 (extensible_of_timeGraph_future hC hcaus hTc hT hγ' hTγ' hc.1 hcγ' htS' hall)
    · push Not at hall
      obtain ⟨t₁, ht₁, h₁⟩ := hall
      have hgt : ∀ t ∈ I, tS < T (c t) := by
        intro t ht
        by_contra h
        push Not at h
        have hsub' : uIcc t t₁ ⊆ I := hc.1.ordConnected.uIcc_subset ht ht₁
        have hcont : ContinuousOn (T ∘ c) (uIcc t t₁) :=
          hTc.comp_continuousOn ((continuousOn_of_causalCurveIn hc.1).mono hsub')
        obtain ⟨s, hs, hse⟩ := intermediate_value_uIcc hcont (Set.mem_uIcc_of_le h h₁)
        exact hne s (hsub' hs) hse
      exact hc.2 (extensible_of_timeGraph_past hC hcaus hTc hT hγ' hTγ' hc.1 hcγ' htS' hgt)
  obtain ⟨t, ht, hcS⟩ := hex
  refine ⟨c t, ⟨mem_image_of_mem c ht, hcS⟩, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsS⟩
  rcases le_total s t with h | h
  · exact hac _ hsS _ hcS ((hc.1.mono_opens le_top).le_of_le hs ht h)
  · exact (hac _ hcS _ hsS ((hc.1.mono_opens le_top).le_of_le ht hs h)).symm

end CurveExt

end Causality

namespace SingularRowsCauchyExt

open SingularRowsSplitting

/-! ### Open sets as subtypes -/

section Opens

variable {X : Type*} [TopologicalSpace X]

/-- The image by the inclusion of the trace of a set `K ⊆ W` is `K`. -/
theorem image_val_preimage {W : Opens X} {K : Set X} (hK : K ⊆ W) :
    (Subtype.val : W → X) '' (Subtype.val ⁻¹' K) = K := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨⟨z, hK hz⟩, hz, rfl⟩

/-- **The inclusion of an open set `W` is an injective abstract `𝕄≥0`-morphism** for every
causality `C` of `W` for which it is a chart isomorphism into `(X, D)`: its source is all of `W`,
and the image of an open `V ⊆ W` is `V` itself. -/
theorem isEMorphism_val_of_chartIso {W : Opens X} (hW : Nonempty W) {C : Causality W}
    {D : Causality X} (h : ChartIso C D (W.openPartialHomeomorphSubtypeCoe hW)) :
    IsEMorphism C D Subtype.val := by
  set e := W.openPartialHomeomorphSubtypeCoe hW with he
  have hsrc : ∀ V : Opens W, V ≤ chartSource e := fun V z _ => by
    show z ∈ e.source
    rw [he, Opens.openPartialHomeomorphSubtypeCoe_source]
    exact mem_univ z
  have hci : ∀ V : Opens W, (chartImage e V : Set X) = Subtype.val '' (V : Set W) := fun V => by
    rw [coe_chartImage, he, Opens.openPartialHomeomorphSubtypeCoe_source, univ_inter,
      Opens.openPartialHomeomorphSubtypeCoe_coe]
  have hle : ∀ (V : Opens W) (U : Opens X), MapsTo Subtype.val (V : Set W) U →
      chartImage e V ≤ U := fun V U hmaps z hz => by
    rw [← SetLike.mem_coe, hci V] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hmaps hw
  exact
    { continuousOn := continuous_subtype_val.continuousOn
      isOpen_image := fun V _ => W.isOpen.isOpenMap_subtype_val _ V.isOpen
      map_le := fun V U _ hmaps x y hxy =>
        D.le_mono (hle V U hmaps)
          (((h V (hsrc V) x (C.le_mem_left hxy) y (C.le_mem_right hxy)).1).1 hxy)
      map_lt := fun V U _ hmaps x y hxy =>
        D.lt_mono (hle V U hmaps)
          (((h V (hsrc V) x (C.lt_mem_left hxy) y (C.lt_mem_right hxy)).2).1 hxy)
      locally := fun _ _ => ⟨⊤, le_rfl, trivial, Subtype.val_injective.injOn,
        fun V' _ U hU y hy z hz => by
          have hU' : chartImage e V' = U := SetLike.coe_injective (by rw [hci V', hU])
          rw [← hU']
          exact h V' (hsrc V') y hy z hz⟩ }

end Opens

attribute [local instance] E0GX.singularGX

/-- The open sublevel set `{T < a}` of a continuous `T : E₀ → ℝ`. -/
def sublevel {T : E0 → ℝ} (hT : Continuous T) (a : ℝ) : Opens E0 :=
  ⟨{x | T x < a}, isOpen_lt hT continuous_const⟩

variable {T : E0 → ℝ}

/-- Membership in `{T < a}`. -/
theorem mem_sublevel {hT : Continuous T} {a : ℝ} {x : E0} : x ∈ sublevel hT a ↔ T x < a :=
  Iff.rfl

/-! ### `E₀` and a time function strictly increasing along `≤` -/

/-- `E₀` has no causal endpoint (`E0.Jminus_ne_singleton`, `E0.Jplus_ne_singleton` at `⊤`). -/
theorem noCausalEndpoint_e0 : E0.causality.NoCausalEndpoint :=
  ⟨fun _ => E0.Jminus_ne_singleton (W := ⊤) trivial,
    fun _ => E0.Jplus_ne_singleton (W := ⊤) trivial⟩

/-- `T` is non-decreasing along `≤`. -/
theorem time_le_of_le (hTs : ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) {x y : E0}
    (h : E0.causality.le ⊤ x y) : T x ≤ T y := by
  rcases eq_or_ne x y with rfl | hne
  · exact le_rfl
  · exact (hTs x y h hne).le

/-- **The sublevel set `{T < a}` is a past set.** -/
theorem isPast_sublevel (hTc : Continuous T)
    (hTs : ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) (a : ℝ) :
    ∀ x y, x ∈ sublevel hTc a → E0.causality.le ⊤ y x → y ∈ sublevel hTc a :=
  fun _ _ hx hyx => lt_of_le_of_lt (time_le_of_le hTs hyx) hx

/-- `T⁻¹(b) ⊆ {T < a}` for `b < a`. -/
theorem level_subset_sublevel (hTc : Continuous T) {a b : ℝ} (hab : b < a) :
    T ⁻¹' {b} ⊆ sublevel hTc a := fun x hx => by
  show T x < a
  rw [mem_preimage, mem_singleton_iff] at hx
  rw [hx]
  exact hab

/-- Along a τ-orbit, `T` is strictly increasing. -/
theorem time_lt_of_lt (hTs : ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) (x : E0)
    {s t : ℝ} (hst : s < t) : T (tauFlow s x) < T (tauFlow t x) := by
  refine hTs _ _ (isCausalFlow_tauFlow.le x hst.le) fun h => ?_
  have h1 := congrArg Prod.fst h
  rw [tauFlow_apply, tauFlow_apply] at h1
  linarith

/-- Along a τ-orbit, the parameter is ordered as the values of `T`. -/
theorem lt_of_time_lt (hTs : ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) (x : E0)
    {s t : ℝ} (h : T (tauFlow s x) < T (tauFlow t x)) : s < t := by
  by_contra hst
  push Not at hst
  have := time_le_of_le hTs (isCausalFlow_tauFlow.le x hst)
  linarith

section Construction

variable (hT : E0.causality.IsCauchyTimeFunction T)
  (hTs : ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y)
include hT hTs

/-- Every level `T⁻¹(b)` is a Cauchy surface of `E₀`
(`Causality.IsCauchyTimeFunction.isCauchySurface_level`). -/
theorem isCauchySurface_level (b : ℝ) : E0.causality.IsCauchySurface (T ⁻¹' {b}) :=
  hT.isCauchySurface_level E0.causallyArcConnected E0.stronglyCausal noCausalEndpoint_e0.1
    noCausalEndpoint_e0.2 hTs b

/-- **The level `T⁻¹(b)` is a Cauchy surface of `{T < a}`** for `b < a`: the past-set lemma
`Causality.isCauchySurfaceOn_of_isPast` at `E₀`. -/
theorem isCauchySurfaceOn_sublevel {a b : ℝ} (hab : b < a) :
    E0.causality.IsCauchySurfaceOn (sublevel hT.1.continuous a) (T ⁻¹' {b}) :=
  Causality.isCauchySurfaceOn_of_isPast E0.causallyArcConnected E0.isCausal hT.1.continuous hTs
    (isPast_sublevel hT.1.continuous hTs a) (level_subset_sublevel hT.1.continuous hab)
    (isCauchySurface_level hT hTs b)

/-- Every level `T⁻¹(b)` meets the τ-orbit of every point of `E₀`. -/
theorem exists_tauFlow_level (x : E0) (b : ℝ) : ∃ t : ℝ, T (tauFlow t x) = b :=
  isCausalFlow_tauFlow.exists_apply_mem (isCauchySurface_level hT hTs b) x

/-- **The construction**: `{T < a}` is an `E₀`-manifold with a unique natural causality; for
it, `{T < a}` is globally hyperbolic, its relations at the top are `E₀`'s, each `T⁻¹(b)`, `b < a`,
is a Cauchy surface, and the inclusion is a Cauchy embedding which is not onto. -/
theorem cauchyExtension (a : ℝ) :
    SFALocalE0.E0Covered (sublevel hT.1.continuous a) ∧
      (∃! C : Causality (sublevel hT.1.continuous a), SFALocalE0.IsE0Natural C) ∧
      ∀ C : Causality (sublevel hT.1.continuous a), SFALocalE0.IsE0Natural C →
        C.AbsolutelyMinimal ∧
        IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
        (∀ x y : sublevel hT.1.continuous a,
          (C.le ⊤ x y ↔ E0.causality.le ⊤ x y) ∧ (C.lt ⊤ x y ↔ E0.causality.lt ⊤ x y)) ∧
        C.GloballyHyperbolic ∧
        (∀ b < a, C.IsCauchySurface (Subtype.val ⁻¹' (T ⁻¹' {b}))) ∧
        IsCauchyEmbedding C E0.causality Subtype.val ∧
        ¬ Surjective (Subtype.val : sublevel hT.1.continuous a → E0) := by
  have hpast := isPast_sublevel hT.1.continuous hTs a
  have he0 : SFALocalE0.E0Covered (sublevel hT.1.continuous a) :=
    CupCapBTZCounterexample.e0Covered_opens SFALocalE0.nonvacuous.1 _
  refine ⟨he0, SFALocalE0.existsUnique_isE0Natural he0, fun C hC => ?_⟩
  have hrel : ∀ x y : sublevel hT.1.continuous a,
      (C.le ⊤ x y ↔ E0.causality.le ⊤ x y) ∧ (C.lt ⊤ x y ↔ E0.causality.lt ⊤ x y) :=
    fun x y => by
      rw [CupCapBTZCounterexample.le_top_iff_opens hC, CupCapBTZCounterexample.lt_top_iff_opens hC]
      exact ⟨Causality.le_iff_le_top_of_isPast E0.causallyArcConnected hpast y.2,
        Causality.lt_iff_lt_top_of_isPast E0.causallyArcConnected hpast y.2⟩
  have hG : C.GloballyHyperbolic := by
    refine ⟨CupCapBTZCounterexample.isCausal_opens hC, fun p q => ?_⟩
    have hd : C.diamond ⊤ p q = Subtype.val ⁻¹' (E0.causality.diamond ⊤ p q) := by
      ext z
      simp only [mem_preimage, Causality.mem_diamond, (hrel _ _).1]
    have hsub : E0.causality.diamond ⊤ (p : E0) q ⊆ sublevel hT.1.continuous a :=
      fun z hz => hpast q z q.2 (Causality.mem_diamond.1 hz).2
    rw [hd, Subtype.isCompact_iff, image_val_preimage hsub]
    exact E0.globallyHyperbolic.2 p q
  have hne : Nonempty (sublevel hT.1.continuous a) := by
    obtain ⟨t, ht⟩ := exists_tauFlow_level hT hTs (0 : E0) (a - 1)
    exact ⟨⟨tauFlow t 0, show T _ < a by rw [ht]; linarith⟩⟩
  have hφ : IsEMorphism C E0.causality Subtype.val :=
    isEMorphism_val_of_chartIso hne
      (hC.2.1 _ (CupCapBTZCounterexample.isAEChart_subtypeCoe _ hne))
  have hcs : ∀ b < a, C.IsCauchySurface (Subtype.val ⁻¹' (T ⁻¹' {b})) := fun b hb => by
    refine (IsEMorphismOn.isCauchySurfaceOn_image_iff hφ Subtype.val_injective.injOn le_rfl
      (U := sublevel hT.1.continuous a) ?_ (fun _ _ => trivial)).2 ?_
    · ext x
      simp
    · rw [image_val_preimage (level_subset_sublevel hT.1.continuous hb)]
      exact isCauchySurfaceOn_sublevel hT hTs hb
  refine ⟨hC.2.2, SFALocal.isoChartsCoverDEC25_of_e0 he0 hC, hrel, hG, hcs,
    ⟨hG, E0.globallyHyperbolic, hφ, Subtype.val_injective,
      ⟨_, hcs (a - 1) (by linarith), ?_⟩⟩, ?_⟩
  · rw [image_val_preimage (level_subset_sublevel hT.1.continuous (by linarith : a - 1 < a))]
    exact isCauchySurface_level hT hTs (a - 1)
  · intro hsurj
    obtain ⟨t, ht⟩ := exists_tauFlow_level hT hTs (0 : E0) a
    obtain ⟨y, hy⟩ := hsurj (tauFlow t 0)
    have h1 : T (y : E0) < a := y.2
    rw [hy, ht] at h1
    exact lt_irrefl a h1

/-- **The sublevel set `{T < a}` is connected**: `T⁻¹(a - 1)` is connected (the τ-flow splits
`E₀` along it, `SingularRowsSplitting.tauFlow_split`), and every point of `{T < a}` is joined
to it along its τ-orbit inside `{T < a}`. -/
theorem connectedSpace_sublevel (a : ℝ) : ConnectedSpace (sublevel hT.1.continuous a) := by
  have hS := isCauchySurface_level hT hTs (a - 1)
  obtain ⟨ψ, -, -⟩ := tauFlow_split hS
  haveI : ConnectedSpace (↥(T ⁻¹' {a - 1}) × ℝ) :=
    ψ.symm.surjective.connectedSpace ψ.symm.continuous
  haveI : ConnectedSpace ↥(T ⁻¹' {a - 1}) :=
    (Prod.fst_surjective (α := ↥(T ⁻¹' {a - 1})) (β := ℝ)).connectedSpace continuous_fst
  have hSc : IsConnected (T ⁻¹' {a - 1}) := isConnected_iff_connectedSpace.2 inferInstance
  have hsub := level_subset_sublevel hT.1.continuous (by linarith : a - 1 < a)
  obtain ⟨x₀, hx₀⟩ := hSc.nonempty
  refine isConnected_iff_connectedSpace.1
    ⟨⟨x₀, hsub hx₀⟩, isPreconnected_of_forall x₀ fun y hy => ?_⟩
  obtain ⟨t, ht⟩ := exists_tauFlow_level hT hTs y (a - 1)
  have hc : Continuous fun s : ℝ => tauFlow s y := tauFlow.continuous continuous_id continuous_const
  refine ⟨(fun s => tauFlow s y) '' uIcc 0 t ∪ T ⁻¹' {a - 1}, union_subset ?_ hsub, Or.inr hx₀,
    Or.inl ⟨0, left_mem_uIcc, Flow.map_zero_apply tauFlow y⟩, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    show T (tauFlow s y) < a
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hs
      have := time_le_of_le hTs (isCausalFlow_tauFlow.le y hs.2)
      rw [ht] at this
      linarith
    · rw [uIcc_of_ge h] at hs
      have := time_le_of_le hTs (isCausalFlow_tauFlow.le y hs.2)
      rw [Flow.map_zero_apply] at this
      exact lt_of_le_of_lt this hy
  · exact IsPreconnected.union (tauFlow t y) ⟨t, right_mem_uIcc, rfl⟩ ht
      (isPreconnected_uIcc.image _ hc.continuousOn) hSc.isPreconnected

/-- **The sublevel set `{T < a}` with its natural causality is a singular flat spacetime** in
the library's class (`CupCapBTZCounterexample.singularFlatSpacetime_opens`, connected by
`connectedSpace_sublevel`). -/
theorem singularFlatSpacetime_sublevel (a : ℝ) {C : Causality (sublevel hT.1.continuous a)}
    (hC : SFALocalE0.IsE0Natural C) :
    C.SingularFlatSpacetime (SFALocalE0.sing (sublevel hT.1.continuous a)) :=
  CupCapBTZCounterexample.singularFlatSpacetime_opens hC (connectedSpace_sublevel hT hTs a)

/-! ### Witnesses (kb/0011), off the identity -/

/-- `lem:image_diamant` **at the inclusion `i : {T < a} → E₀`, at a BTZ point**, out of
`SingularRowsDiamond.image_diamant`. With `Σ = i⁻¹(T⁻¹(b))`, `b < a`, the point `p` of the axis
where `T = (a + b)/2` lies in `J⁺(Σ)`, and `i(J⁺(Σ) ∩ J⁻(p)) = J⁺(T⁻¹(b)) ∩ J⁻(p)`. What it
exercises: `J⁺(T⁻¹(b))` is not contained in `i(M)` (the first conjunct), so the equality says
that the diamond of `E₀` from `T⁻¹(b)` to `p` stays in `{T < a}` and is the diamond of
`{T < a}`. -/
theorem image_diamant_witness {a b : ℝ} (hab : b < a)
    {C : Causality (sublevel hT.1.continuous a)} (hC : SFALocalE0.IsE0Natural C) :
    ¬ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ⊆ range (Subtype.val : sublevel hT.1.continuous a → E0) ∧
    ∃ p : sublevel hT.1.continuous a, (p : E0) ∈ SFALocal.sing E0 0 ∧ b < T p ∧
      p ∈ C.Jplus ⊤ (Subtype.val ⁻¹' (T ⁻¹' {b})) ∧
      Subtype.val '' (C.Jplus ⊤ (Subtype.val ⁻¹' (T ⁻¹' {b})) ∩ C.Jminus ⊤ {p}) =
        E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∩ E0.causality.Jminus ⊤ {(p : E0)} := by
  obtain ⟨-, -, h⟩ := cauchyExtension hT hTs a
  obtain ⟨hmin, hcov, hrel, -, hcs, hi, -⟩ := h C hC
  obtain ⟨hminN, hCN, hsing, -⟩ := SFALocal.nonvacuous_e0
  have hS := hcs b hab
  have hsub := level_subset_sublevel hT.1.continuous hab
  have hx₀ : ((0 : ℝ), (0 : ℂ)) ∈ E0.axis := rfl
  obtain ⟨tb, htb⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) b
  obtain ⟨tm, htm⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) ((a + b) / 2)
  obtain ⟨ta, hta⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) a
  have hbm : tb < tm := lt_of_time_lt hTs _ (by rw [htb, htm]; linarith)
  have hba : tb < ta := lt_of_time_lt hTs _ (by rw [htb, hta]; linarith)
  have hpU : tauFlow tm ((0 : ℝ), (0 : ℂ)) ∈ sublevel hT.1.continuous a :=
    show T _ < a by rw [htm]; linarith
  have hσU : tauFlow tb ((0 : ℝ), (0 : ℂ)) ∈ sublevel hT.1.continuous a :=
    show T _ < a by rw [htb]; exact hab
  have hpJ : (⟨_, hpU⟩ : sublevel hT.1.continuous a) ∈
      C.Jplus ⊤ (Subtype.val ⁻¹' (T ⁻¹' {b})) :=
    ⟨⟨_, hσU⟩, htb, (hrel _ _).1.2 (isCausalFlow_tauFlow.le _ hbm.le)⟩
  refine ⟨fun hJ => ?_, ⟨_, hpU⟩, ?_, ?_, hpJ, ?_⟩
  · obtain ⟨y, hy⟩ := hJ ⟨_, htb, isCausalFlow_tauFlow.le ((0 : ℝ), (0 : ℂ)) hba.le⟩
    have h1 : T (y : E0) < a := y.2
    rw [hy, hta] at h1
    exact lt_irrefl a h1
  · rw [hsing]
    exact tauFlow_mem_axis.2 hx₀
  · show b < T (tauFlow tm _)
    rw [htm]
    linarith
  · have := SingularRowsDiamond.image_diamant hmin hcov hminN hCN hi hS hpJ
    rwa [image_val_preimage hsub] at this

/-- `lem:passe_pgcd` **as printed, BTZ branch, at a BTZ point of the frontier**, out of
`SingularRowsDiamond.passe_pgcd_printed`. `p₁` is the point of the axis where `T = a`: it lies in
`∂ i(M) ∩ J⁺(T⁻¹(b))` (the axis points below it are in `{T < a}` and converge to it) and not in
`i(M)`. What it exercises: the hypothesis of the printed lemma, met off `i(M)`, and its two
conclusions there, `K⁻(p₁) ∩ J⁺(T⁻¹(b)) ⊆ i(M)` and `J(T⁻¹(b), p₁) ∖ {p₁} ⊆ i(M)`, the latter set
non-empty (it contains the axis point where `T = b`). -/
theorem passe_pgcd_btz_witness {a b : ℝ} (hab : b < a)
    {C : Causality (sublevel hT.1.continuous a)} (hC : SFALocalE0.IsE0Natural C) :
    ∃ p₁ : E0, p₁ ∈ SFALocal.sing E0 0 ∧ T p₁ = a ∧
      p₁ ∈ frontier (range (Subtype.val : sublevel hT.1.continuous a → E0)) ∧
      p₁ ∉ range (Subtype.val : sublevel hT.1.continuous a → E0) ∧
      p₁ ∈ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∧
      ((E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∩ E0.causality.Jminus ⊤ {p₁}) \ {p₁}).Nonempty ∧
      E0.causality.Kminus ⊤ {p₁} ∩ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ⊆
        range (Subtype.val : sublevel hT.1.continuous a → E0) ∧
      (E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∩ E0.causality.Jminus ⊤ {p₁}) \ {p₁} ⊆
        range (Subtype.val : sublevel hT.1.continuous a → E0) := by
  obtain ⟨-, -, h⟩ := cauchyExtension hT hTs a
  obtain ⟨hmin, hcov, -, -, hcs, hi, -⟩ := h C hC
  obtain ⟨hminN, hCN, hsing, -⟩ := SFALocal.nonvacuous_e0
  have hS := hcs b hab
  have hsub := level_subset_sublevel hT.1.continuous hab
  have hx₀ : ((0 : ℝ), (0 : ℂ)) ∈ E0.axis := rfl
  obtain ⟨tb, htb⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) b
  obtain ⟨ta, hta⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) a
  have hba : tb < ta := lt_of_time_lt hTs _ (by rw [htb, hta]; linarith)
  have hp₀ : tauFlow ta ((0 : ℝ), (0 : ℂ)) ∈ SFALocal.sing E0 0 := by
    rw [hsing]
    exact tauFlow_mem_axis.2 hx₀
  have hp₁J : tauFlow ta ((0 : ℝ), (0 : ℂ)) ∈ E0.causality.Jplus ⊤ (T ⁻¹' {b}) :=
    ⟨_, htb, isCausalFlow_tauFlow.le _ hba.le⟩
  have hp₁n : tauFlow ta ((0 : ℝ), (0 : ℂ)) ∉
      range (Subtype.val : sublevel hT.1.continuous a → E0) := by
    rintro ⟨y, hy⟩
    have h1 : T (y : E0) < a := y.2
    rw [hy, hta] at h1
    exact lt_irrefl a h1
  have hfr : tauFlow ta ((0 : ℝ), (0 : ℂ)) ∈
      frontier (range (Subtype.val : sublevel hT.1.continuous a → E0)) := by
    refine ⟨?_, fun hint => hp₁n (interior_subset hint)⟩
    have hc : Continuous fun s : ℝ => tauFlow s ((0 : ℝ), (0 : ℂ)) :=
      tauFlow.continuous continuous_id continuous_const
    refine mem_closure_of_tendsto ((hc.tendsto ta).mono_left (nhdsWithin_le_nhds (s := Iio ta)))
      (eventually_nhdsWithin_of_forall fun s hs => ?_)
    refine ⟨⟨tauFlow s ((0 : ℝ), (0 : ℂ)), ?_⟩, rfl⟩
    show T _ < a
    rw [← hta]
    exact time_lt_of_lt hTs _ hs
  have hne : ((E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∩
      E0.causality.Jminus ⊤ {tauFlow ta ((0 : ℝ), (0 : ℂ))}) \
        {tauFlow ta ((0 : ℝ), (0 : ℂ))}).Nonempty := by
    refine ⟨tauFlow tb ((0 : ℝ), (0 : ℂ)), ⟨⟨_, htb, E0.causality.le_refl trivial⟩,
      Precausality.mem_Jminus_singleton.2 (isCausalFlow_tauFlow.le _ hba.le)⟩, fun he => ?_⟩
    have h1 : T (tauFlow tb ((0 : ℝ), (0 : ℂ))) = T (tauFlow ta ((0 : ℝ), (0 : ℂ))) := by
      rw [mem_singleton_iff.1 he]
    rw [htb, hta] at h1
    linarith
  have hrow := SingularRowsDiamond.passe_pgcd_printed hmin hcov hminN hCN hi hS
    (p := tauFlow ta ((0 : ℝ), (0 : ℂ))) ⟨hfr, by rwa [image_val_preimage hsub]⟩
  rw [image_val_preimage hsub] at hrow
  exact ⟨_, hp₀, hta, hfr, hp₁n, hp₁J, hne, hrow.1, hrow.2.2 hp₀⟩

/-- `lem:passe_pgcd` **as printed, regular branch, at a regular point of the frontier**, out of
`SingularRowsDiamond.passe_pgcd_printed`. `q₁` is the point of the τ-orbit of `(0, 1)` (off the
axis, `tauFlow_mem_axis`) where `T = a`: in `∂ i(M) ∩ J⁺(T⁻¹(b))`, not in `i(M)`, not in
`sing₀(E₀)`. What it exercises: the regular conclusion `I⁻(q₁) ∩ J⁺(T⁻¹(b)) ⊆ i(M)` with that
set non-empty (`q₁ ∈ Z⁻`, `SFALocal.mem_Zminus_iff`), and the `K⁻` form. -/
theorem passe_pgcd_regular_witness {a b : ℝ} (hab : b < a)
    {C : Causality (sublevel hT.1.continuous a)} (hC : SFALocalE0.IsE0Natural C) :
    ∃ q₁ : E0, q₁ ∉ SFALocal.sing E0 0 ∧ T q₁ = a ∧
      q₁ ∈ frontier (range (Subtype.val : sublevel hT.1.continuous a → E0)) ∧
      q₁ ∉ range (Subtype.val : sublevel hT.1.continuous a → E0) ∧
      q₁ ∈ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ∧
      (E0.causality.Iminus ⊤ {q₁} ∩ E0.causality.Jplus ⊤ (T ⁻¹' {b})).Nonempty ∧
      E0.causality.Kminus ⊤ {q₁} ∩ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ⊆
        range (Subtype.val : sublevel hT.1.continuous a → E0) ∧
      E0.causality.Iminus ⊤ {q₁} ∩ E0.causality.Jplus ⊤ (T ⁻¹' {b}) ⊆
        range (Subtype.val : sublevel hT.1.continuous a → E0) := by
  obtain ⟨-, -, h⟩ := cauchyExtension hT hTs a
  obtain ⟨hmin, hcov, -, -, hcs, hi, -⟩ := h C hC
  obtain ⟨hminN, hCN, hsing, -⟩ := SFALocal.nonvacuous_e0
  have hS := hcs b hab
  have hsub := level_subset_sublevel hT.1.continuous hab
  have hx₁ : ((0 : ℝ), (1 : ℂ)) ∉ E0.axis := fun h => one_ne_zero (h : (1 : ℂ) = 0)
  obtain ⟨tb, htb⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (1 : ℂ)) b
  obtain ⟨ta, hta⟩ := exists_tauFlow_level hT hTs ((0 : ℝ), (1 : ℂ)) a
  have hba : tb < ta := lt_of_time_lt hTs _ (by rw [htb, hta]; linarith)
  have hq₀ : tauFlow ta ((0 : ℝ), (1 : ℂ)) ∉ SFALocal.sing E0 0 := by
    rw [hsing]
    exact fun h => hx₁ (tauFlow_mem_axis.1 h)
  have hq₁J : tauFlow ta ((0 : ℝ), (1 : ℂ)) ∈ E0.causality.Jplus ⊤ (T ⁻¹' {b}) :=
    ⟨_, htb, isCausalFlow_tauFlow.le _ hba.le⟩
  have hq₁n : tauFlow ta ((0 : ℝ), (1 : ℂ)) ∉
      range (Subtype.val : sublevel hT.1.continuous a → E0) := by
    rintro ⟨y, hy⟩
    have h1 : T (y : E0) < a := y.2
    rw [hy, hta] at h1
    exact lt_irrefl a h1
  have hfr : tauFlow ta ((0 : ℝ), (1 : ℂ)) ∈
      frontier (range (Subtype.val : sublevel hT.1.continuous a → E0)) := by
    refine ⟨?_, fun hint => hq₁n (interior_subset hint)⟩
    have hc : Continuous fun s : ℝ => tauFlow s ((0 : ℝ), (1 : ℂ)) :=
      tauFlow.continuous continuous_id continuous_const
    refine mem_closure_of_tendsto ((hc.tendsto ta).mono_left (nhdsWithin_le_nhds (s := Iio ta)))
      (eventually_nhdsWithin_of_forall fun s hs => ?_)
    refine ⟨⟨tauFlow s ((0 : ℝ), (1 : ℂ)), ?_⟩, rfl⟩
    show T _ < a
    rw [← hta]
    exact time_lt_of_lt hTs _ hs
  have hne : (E0.causality.Iminus ⊤ {tauFlow ta ((0 : ℝ), (1 : ℂ))} ∩
      E0.causality.Jplus ⊤ (T ⁻¹' {b})).Nonempty := by
    have hZ := (SFALocal.mem_Zminus_iff hminN hCN _).2 hq₀
    have hN : {x : E0 | b < T x} ∈ 𝓝 (tauFlow ta ((0 : ℝ), (1 : ℂ))) :=
      (isOpen_lt continuous_const hT.1.continuous).mem_nhds
        (show b < T _ by rw [hta]; exact hab)
    obtain ⟨x, hxI, hxN⟩ := hZ _ hN
    refine ⟨x, hxI, ?_⟩
    rcases (isCauchySurface_level hT hTs b).cover_of_t1_secondCountable x with hx | ⟨σ, hσ, hxσ⟩
    · exact hx
    · exfalso
      have h1 := time_le_of_le hTs hxσ
      rw [mem_preimage, mem_singleton_iff] at hσ
      have h2 : b < T x := hxN
      linarith
  have hrow := SingularRowsDiamond.passe_pgcd_printed hmin hcov hminN hCN hi hS
    (p := tauFlow ta ((0 : ℝ), (1 : ℂ))) ⟨hfr, by rwa [image_val_preimage hsub]⟩
  rw [image_val_preimage hsub] at hrow
  exact ⟨_, hq₀, hta, hfr, hq₁n, hq₁J, hne, hrow.1, hrow.2.1 hq₀⟩

/-- `lem:Cauchy_plongement_toutes` **at the inclusion `i : {T < a} → E₀`**, out of
`SingularRowsCauchy.cauchy_plongement_toutes_manifolds`: (i) ⇔ (ii) at `i`, (ii) itself (from
`i`'s Cauchy surface `i⁻¹(T⁻¹(a - 1))`), and, as instances of (ii), `i(i⁻¹(T⁻¹(c)))` is a Cauchy
surface of `E₀` for every `c < a`. What it exercises: the transfer of Cauchy surfaces along a
morphism that is not onto. -/
theorem plongement_witness (a : ℝ) {C : Causality (sublevel hT.1.continuous a)}
    (hC : SFALocalE0.IsE0Natural C) :
    ((∃ S, C.IsCauchySurface S ∧ E0.causality.IsCauchySurface (Subtype.val '' S)) ↔
      ∀ S, C.IsCauchySurface S → E0.causality.IsCauchySurface (Subtype.val '' S)) ∧
    (∀ S, C.IsCauchySurface S → E0.causality.IsCauchySurface (Subtype.val '' S)) ∧
    ∀ c < a, C.IsCauchySurface (Subtype.val ⁻¹' (T ⁻¹' {c})) ∧
      E0.causality.IsCauchySurface (Subtype.val '' (Subtype.val ⁻¹' (T ⁻¹' {c}) :
        Set (sublevel hT.1.continuous a))) := by
  obtain ⟨-, -, h⟩ := cauchyExtension hT hTs a
  obtain ⟨hmin, hcov, -, hG, hcs, hi, -⟩ := h C hC
  obtain ⟨hminN, hCN, -, -⟩ := SFALocal.nonvacuous_e0
  have hrow := SingularRowsCauchy.cauchy_plongement_toutes_manifolds hmin hcov hG hminN hCN
    E0.globallyHyperbolic hi.isEMorphism hi.injective
  have hall := hrow.1 hi.exists_cauchy
  exact ⟨hrow, hall, fun c hc => ⟨hcs c hc, hall _ (hcs c hc)⟩⟩

end Construction

/-- **Non-vacuity**: `E₀` has a Cauchy time function strictly increasing along `≤`
(`E0.geroch_sing_i_imp_ii`), so every theorem of this section applies. -/
theorem exists_cauchyTimeFunction :
    ∃ T : E0 → ℝ, E0.causality.IsCauchyTimeFunction T ∧
      ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y :=
  E0.geroch_sing_i_imp_ii

/-- **Non-vacuity, assembled** (kb/0011): for the Cauchy time function `T` of
`E0.geroch_sing_i_imp_ii` and the natural causality `C` of `{T < 1}`
(`SFALocalE0.existsUnique_isE0Natural`), the inclusion is a Cauchy embedding that is not onto,
`T⁻¹(0)` is a Cauchy surface of `{T < 1}`, and the frontier of the image meets `J⁺(T⁻¹(0))` both
at a BTZ point and at a regular point, where `passe_pgcd_btz_witness` and
`passe_pgcd_regular_witness` apply. -/
theorem nonvacuous_e0 :
    ∃ (T : E0 → ℝ) (hT : E0.causality.IsCauchyTimeFunction T),
      (∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) ∧
      ∃ C : Causality (sublevel hT.1.continuous 1), SFALocalE0.IsE0Natural C ∧
        IsCauchyEmbedding C E0.causality Subtype.val ∧
        ¬ Surjective (Subtype.val : sublevel hT.1.continuous 1 → E0) ∧
        C.IsCauchySurface (Subtype.val ⁻¹' (T ⁻¹' {0})) ∧
        (frontier (range (Subtype.val : sublevel hT.1.continuous 1 → E0)) ∩
          SFALocal.sing E0 0 ∩ E0.causality.Jplus ⊤ (T ⁻¹' {0})).Nonempty ∧
        (frontier (range (Subtype.val : sublevel hT.1.continuous 1 → E0)) ∩
          (SFALocal.sing E0 0)ᶜ ∩ E0.causality.Jplus ⊤ (T ⁻¹' {0})).Nonempty := by
  obtain ⟨T, hT, hTs⟩ := exists_cauchyTimeFunction
  obtain ⟨-, ⟨C, hC, -⟩, h⟩ := cauchyExtension hT hTs 1
  obtain ⟨-, -, -, -, hcs, hi, hns⟩ := h C hC
  obtain ⟨p₁, hp₀, -, hfr, -, hpJ, -⟩ := passe_pgcd_btz_witness hT hTs zero_lt_one hC
  obtain ⟨q₁, hq₀, -, hqfr, -, hqJ, -⟩ := passe_pgcd_regular_witness hT hTs zero_lt_one hC
  exact ⟨T, hT, hTs, C, hC, hi, hns, hcs 0 zero_lt_one, ⟨p₁, ⟨hfr, hp₀⟩, hpJ⟩,
    ⟨q₁, ⟨hqfr, hq₀⟩, hqJ⟩⟩

end SingularRowsCauchyExt

end Causal
