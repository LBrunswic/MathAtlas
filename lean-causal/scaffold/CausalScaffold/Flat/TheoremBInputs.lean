import CausalScaffold.Flat.Classification

/-!
# `CausalScaffold.Flat.TheoremBInputs` — the inputs of Theorem B: lemma K's data and Selberg

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). This file
audits the two universal hypotheses of `barbot_B` (`Flat/Classification.lean`) other than the
cited group-theory bundle `BarbotExternals`: lemma K's data `hK : ∀ N, GH N → FlatLemmaKData N`
and Selberg's lemma `hSel : SelbergLemma (Minkowski d)`. **No label is marked**: Theorem B stays
partial (its own upstream `sorry`s, and the one named input below).

* `bthm:cauclo` — `GHFspace.tex:353` (Theorem B), corollaries only, unmarked:
  `barbot_B_of_externals` (`hK` replaced by Geroch's existence theorem for flat spacetimes,
  `FlatGerochGH`), `barbot_B_of_admissible` (by admissible measures, `FlatAdmissibleMeasures`),
  `barbot_B_zero` (at `d = 0`, `hE` and `hSel` discharged, only `FlatGerochGH` left).
* Lemma K's data, **proved, no `sorry`**: `flatLemmaKData_iff_barbotGH` — on every flat spacetime
  `FlatLemmaKData N ↔ BarbotGH N`; six of its seven fields hold on **every** flat spacetime, GH or
  not (`flatCausality_tarentin`, `jplus_ne_singleton_of_isCausalFlow`,
  `jminus_ne_singleton_of_isCausalFlow`, with Splitting's flow, CauchyComplete's arc-connectedness
  and `CurvesExtend`), and the seventh, an acausal Cauchy surface, is exactly Barbot's GH. Hence
  `forall_flatLemmaKData_iff`: `barbot_B`'s `hK` **is** `FlatGerochGH d` — every GH (ETT's: causal
  + compact diamonds) flat spacetime has a Cauchy surface (Barbot's GH, l.498–507).
* Selberg, **proved, no `sorry`**: `selbergLemma_of_linearEquiv` (transport along `V ≃ₗ[ℝ] W`),
  `selbergLemma_minkowski_zero` (`SelbergLemma (Minkowski 0)`, from Externals' `SelbergLemma ℝ`).
* Non-vacuity, **proved, no `sorry`**: `barbot_B_hypotheses_satisfiable` — at `d = 0` the bundle
  and Selberg hold, and in every dimension the static torus `ℤᵈ\𝐌ⁿ` is GH, Cauchy-compact, maximal
  and carries lemma K's data.

> Up to finite coverings, every maximal Cauchy-compact globally hyperbolic flat spacetime is
> isometric to a translation spacetime, a Misner spacetime, or the twisted product of a standart
> spacetime (Cauchy-compact Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

> Actually, (ii) follows from (i), since, as noted previously, closed spacelike hypersurfaces in
> GH spacetimes are always Cauchy hypersurfaces. In other words, maximal Cauchy-compact GH
> spacetimes are also absolutely maximal. (l.3535–3540)

> A spacetime $M$ is \emph{globally hyperbolic\/} (abbreviation GH) if there is a proper time
> function $t: M \rightarrow \mathbb R$ such that every fiber $t^{-1}(t_{0})$ is spacelike. [...]
> In other words, every fiber of $t$ is a \emph{Cauchy hypersurface,\/} meaning precisely that
> this is a hypersurface intersecting every unextendible nonspacelike curve in $M$. (l.498–507)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| B: "closed spacelike hypersurfaces in GH spacetimes are Cauchy" (l.3537–3539), used through lemma K's data `FlatLemmaKData` on every GH target | ⚠ reduced: `FlatLemmaKData N ↔ BarbotGH N` (proved); the universal `hK` is equivalent to `FlatGerochGH d` (ETT-GH ⇒ a Cauchy surface). **Under Barbot's own definition of GH (l.498–507: GH means having Cauchy hypersurfaces) `FlatGerochGH` is a tautology**; it is the gap between ETT's `GloballyHyperbolic` and Barbot's GH, i.e. `theo:geroch` (i)⇒(iii) for flat spacetimes. It is further reduced to admissible measures (`flatGerochGH_of_admissible`, through `barbotGH_of_gh`, i.e. ETT's `geroch_i_imp_iii`) |
| B: π₁ finitely generated ⇒ family (a), through Selberg's lemma (DEC-44) | ⚠ strengthened (unchanged): `SelbergLemma (Minkowski d)` stays a named external for `d ≥ 1` (Selberg in `GL_{n ≥ 2}(ℝ)`, not in mathlib); **discharged at `d = 0`** (`selbergLemma_minkowski_zero`) |
| B: Benoist, Bieberbach, Auslander–Carrière–Dal'bo, Carrière–Dal'bo (`BarbotExternals d`) | ✓ carried as in `barbot_B`; discharged at `d = 0` (`barbotExternals_zero`, Classification) |
| B: `M` maximal Cauchy-compact GH | ✓ carried |

## SCOPE (disclosed)

* **`FlatGerochGH` is not proved here, in any dimension.** It is Geroch's theorem for flat
  spacetimes (ETT's GH, causal + compact diamonds, gives a Cauchy surface). The library proves
  the topological Geroch theorem (`Causality.geroch_i_imp_iii`, `Causal/Geroch.lean`) from a
  pair of admissible measures, so `FlatGerochGH` follows from `FlatAdmissibleMeasures`
  (`flatGerochGH_of_admissible`), and every other hypothesis of `geroch_i_imp_iii` is proved here
  for every flat spacetime (tarentin, arc-connectedness, `J^±(p) ≠ {p}`, first countability).
  Admissible measures are not constructed for a general flat spacetime (even for `𝐌ⁿ` the
  library's `minkowski_exists_measure`, `CausalScaffold/MinkowskiMeasure.lean`, is a tagged
  `sorry`: nullity of achronal boundaries). So `barbot_B_of_externals` carries `FlatGerochGH d`,
  a classical theorem, in place of `hK`. It is a universal statement: its non-vacuity is its
  truth (Geroch 1970; Bernal–Sánchez), not a witness; its instances on the models are proved
  (`flatLemmaKData_torusSpace`, Classification's `flatLemmaKData_minkowskiSpace`).
* **`hK` cannot be narrowed.** `absMax_of_cauchyCompact_of_mgh` uses lemma K on every GH target
  `N` of an isometric embedding, and lemma K needs a splitting of `N`, hence a Cauchy surface of
  `N` (`exists_cauchy`): exactly `BarbotGH N`. Nothing weaker than `FlatGerochGH` discharges it.
* **Is `hSel` used?** Not by any proof term: `barbot_B` passes it only to
  `cauclo_from_embedding`, whose binder is `_hSel` and whose body is a tagged `sorry` (G9, step
  (4): family (b) → (a) needs π₁ finitely generated and Selberg). It is mathematically needed by
  that step and only formally idle; deleting it would hide a real dependency. Likewise
  `cauclo_from_embedding` binds `_hK` unused; `hK` is consumed by
  `absMax_of_cauchyCompact_of_mgh`.
* **No `d ≥ 1` witness of all of Theorem B's hypotheses**: `SelbergLemma (Minkowski d)` for
  `d ≥ 1` and `BarbotExternals d` for `d ≥ 1` are cited theorems not in mathlib.
  `barbot_B_hypotheses_satisfiable` witnesses everything except the universal `FlatGerochGH`, at
  `d = 0` for the externals and in every `d` for the spacetime.
* **Universes.** `barbot_B`'s `hK` ranges over `FlatSpacetime.{0} d`; the reductions here are
  universe-polymorphic and are used at `.{0}`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
package WP-35d-TheoremBInputs.
-/

namespace Causal.Flat

open Set Function Filter Topology TopologicalSpace Metric

universe u

variable {d : ℕ}

/-! ## §1 Lemma K's fields on every flat spacetime -/

section Fields

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))]

/-- **Every flat spacetime is tarentin** (`def:tarentin_spacetime`): in the chart at `x`, the
vertical diamond between `e x ∓ ε e₀` contains the ball of radius `ε/2`, its causal relations are
realised by segments inside the chart image of `U` (`staticLe_of_ball`), and they are carried back
by the chart isomorphism (`flatCausality_chartIso_chartAt`) and enlarged to `⊤` (`le_mono`). -/
theorem flatCausality_tarentin : (flatCausality d X).Tarentin := by
  intro x U hU
  set e := chartAt (Minkowski d) x with he
  have hiso : ChartIso (flatCausality d X) (minkowski d) e := flatCausality_chartIso_chartAt x
  have hxs : x ∈ e.source := mem_chart_source _ x
  let W : Opens X := ⟨interior U ∩ e.source, isOpen_interior.inter e.open_source⟩
  have hxW : x ∈ W := ⟨mem_interior_iff_mem_nhds.2 hU, hxs⟩
  have hWe : W ≤ chartSource e := fun z hz => hz.2
  have hyW : e x ∈ chartImage e W := mem_chartImage_of_mem hxs hxW
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (chartImage e W).isOpen (e x) hyW
  set y := e x with hy
  set ε := ρ / 4 with hε
  have hε0 : 0 < ε := by positivity
  have key : ∀ w : Minkowski d, dist w y < 3 * ε → w ∈ chartImage e W := fun w hw =>
    hball (by rw [mem_ball]; linarith)
  set p' : Minkowski d := (y.1 - ε, y.2) with hp'
  set q' : Minkowski d := (y.1 + ε, y.2) with hq'
  have hp'y : dist p' y = ε := by
    rw [hp', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
    exact max_eq_left hε0.le
  have hq'y : dist q' y = ε := by
    rw [hq', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos hε0]
    exact max_eq_left hε0.le
  obtain ⟨p, -, hpW, hpe, -⟩ := exists_of_mem_chartImage (key p' (by linarith))
  obtain ⟨q, -, hqW, hqe, -⟩ := exists_of_mem_chartImage (key q' (by linarith))
  refine ⟨p, interior_subset hpW.1, q, interior_subset hqW.1, ?_⟩
  have hO : IsOpen ((W : Set X) ∩ (e.source ∩ e ⁻¹' ball y (ε / 2))) :=
    W.isOpen.inter (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball)
  refine interior_maximal (fun z hz => ?_) hO ⟨hxW, hxs, mem_ball_self (by linarith)⟩
  obtain ⟨hzW, -, hzb⟩ := hz
  have hzy : dist (e z) y < ε / 2 := hzb
  rw [mem_preimage, mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hzb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hzb
  rw [Causality.mem_diamond]
  constructor
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe p hpW z hzW).1.2 ?_)
    rw [hpe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w p' y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show y.1 - ε ≤ (e z).1
      linarith
    · show dist y.2 (e z).2 ≤ (e z).1 - (y.1 - ε)
      rw [dist_comm]; linarith
    · show (e z).1 - (y.1 - ε) < 2 * ε
      linarith
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe z hzW q hqW).1.2 ?_)
    rw [hqe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w (e z) y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show (e z).1 ≤ y.1 + ε
      linarith
    · show dist (e z).2 y.2 ≤ y.1 + ε - (e z).1
      linarith
    · show y.1 + ε - (e z).1 < 2 * ε
      linarith

end Fields

section FlowFields

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {φ : Flow ℝ M}

/-- **A causal flow gives `J⁺(p) ≠ {p}`**: if `J⁺(p) = {p}`, the forward orbit of `p` is
constant, hence (group law) the whole orbit, against `nonstationary`. -/
theorem jplus_ne_singleton_of_isCausalFlow (hφ : C.IsCausalFlow φ) (p : M) :
    C.Jplus ⊤ {p} ≠ {p} := by
  intro h
  have hfix : ∀ t : ℝ, 0 ≤ t → φ t p = p := fun t ht => by
    have hmem : φ t p ∈ C.Jplus ⊤ {p} :=
      ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p ht⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨t, ht⟩ := hφ.nonstationary p
  apply ht
  rcases le_total 0 t with h0 | h0
  · exact hfix t h0
  · have h' := hfix (-t) (by linarith)
    calc φ t p = φ t (φ (-t) p) := by rw [h']
      _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

/-- **A causal flow gives `J⁻(p) ≠ {p}`** (the backward orbit). -/
theorem jminus_ne_singleton_of_isCausalFlow (hφ : C.IsCausalFlow φ) (p : M) :
    C.Jminus ⊤ {p} ≠ {p} := by
  intro h
  have hfix : ∀ t : ℝ, t ≤ 0 → φ t p = p := fun t ht => by
    have hmem : φ t p ∈ C.Jminus ⊤ {p} :=
      ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p ht⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨t, ht⟩ := hφ.nonstationary p
  apply ht
  rcases le_total t 0 with h0 | h0
  · exact hfix t h0
  · have h' := hfix (-t) (by linarith)
    calc φ t p = φ t (φ (-t) p) := by rw [h']
      _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

end FlowFields

/-! ## §2 Lemma K's data is Barbot's GH -/

section LemmaK

/-- **Lemma K's data from a Cauchy surface** (no GH needed): every field but `exists_cauchy` holds
on every flat spacetime (second countability, `FlatSpacetime.secondCountableTopology`, feeds
Splitting's flow), and a Cauchy surface is acausal under a causal flow
(`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow`). -/
theorem flatLemmaKData_of_barbotGH (N : FlatSpacetime.{u} d) (hB : BarbotGH N) :
    FlatLemmaKData N := by
  have hflow : (flatCausality d N).HasChronalCausalFlow := flat_hasChronalCausalFlow
  obtain ⟨φ, hφ, -⟩ := id hflow
  obtain ⟨S, hS⟩ := hB
  exact ⟨flatCausality_tarentin, flatCausality_causallyArcConnected d N,
    jminus_ne_singleton_of_isCausalFlow hφ, jplus_ne_singleton_of_isCausalFlow hφ,
    curvesExtend_of_isCausalFlow hφ, hflow, S, hS,
    isAcausal_of_isCauchySurface_of_hasChronalCausalFlow hflow hS⟩

/-- **Lemma K's data is exactly Barbot's GH**, on every flat spacetime. -/
theorem flatLemmaKData_iff_barbotGH (N : FlatSpacetime.{u} d) :
    FlatLemmaKData N ↔ BarbotGH N :=
  ⟨fun h => let ⟨S, hS, _⟩ := h.exists_cauchy; ⟨S, hS⟩, flatLemmaKData_of_barbotGH N⟩

variable (d) in
/-- **Geroch's existence theorem for flat spacetimes**, as a named input: every GH flat
spacetime (ETT's `GloballyHyperbolic`: causal, compact diamonds) has a Cauchy surface, i.e. is GH
in Barbot's sense (l.498–507). `theo:geroch` (i)⇒(iii) in the flat case (Geroch 1970;
Bernal–Sánchez); proved by the library from admissible measures (`flatGerochGH_of_admissible`). -/
def FlatGerochGH : Prop := ∀ N : FlatSpacetime.{u} d, GH N → BarbotGH N

/-- **`barbot_B`'s `hK` is `FlatGerochGH`**, nothing more and nothing less. -/
theorem forall_flatLemmaKData_iff :
    (∀ N : FlatSpacetime.{u} d, GH N → FlatLemmaKData N) ↔ FlatGerochGH.{u} d :=
  ⟨fun h N hN => (flatLemmaKData_iff_barbotGH N).1 (h N hN),
    fun h N hN => flatLemmaKData_of_barbotGH N (h N hN)⟩

theorem flatLemmaKData_of_flatGerochGH (h : FlatGerochGH.{u} d) (N : FlatSpacetime.{u} d)
    (hN : GH N) : FlatLemmaKData N :=
  forall_flatLemmaKData_iff.2 h N hN

variable (d) in
/-- **Admissible measures on GH flat spacetimes** (`defi:mesure_dieckmann`, for the Borel
σ-algebra): the flat case of `prop:mesure_dieckmann_Lorentz` (ETT.tex:1054; a GH spacetime is
strongly causal, `GloballyHyperbolic.stronglyCausal`). -/
def FlatAdmissibleMeasures : Prop :=
  ∀ N : FlatSpacetime.{u} d, GH N →
    letI : MeasurableSpace N := borel N
    ∃ μp μm : MeasureTheory.Measure N,
      (flatCausality d N).AdmissibleFuture μp ∧ (flatCausality d N).AdmissiblePast μm

/-- **Geroch from admissible measures**: `barbotGH_of_gh` (ETT's `geroch_i_imp_iii`), all of whose
other hypotheses hold on every flat spacetime (§1). -/
theorem flatGerochGH_of_admissible (h : FlatAdmissibleMeasures.{u} d) : FlatGerochGH.{u} d := by
  intro N hN
  letI : MeasurableSpace N := borel N
  haveI : BorelSpace N := ⟨rfl⟩
  obtain ⟨μp, μm, hp, hm⟩ := h N hN
  obtain ⟨φ, hφ, -⟩ := (flat_hasChronalCausalFlow : (flatCausality d N).HasChronalCausalFlow)
  exact barbotGH_of_gh hp hm flatCausality_tarentin (flatCausality_causallyArcConnected d N)
    (jminus_ne_singleton_of_isCausalFlow hφ) (jplus_ne_singleton_of_isCausalFlow hφ) hN

/-- Every Cauchy-compact flat spacetime carries lemma K's data. -/
theorem CauchyCompact.flatLemmaKData {N : FlatSpacetime.{u} d} (h : CauchyCompact N) :
    FlatLemmaKData N :=
  flatLemmaKData_of_barbotGH N h.barbotGH

end LemmaK

/-! ## §3 Selberg's lemma: transport, and `d = 0` -/

section Selberg

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Conjugation by a linear equivalence, as a group morphism `GL(V) →* GL(W)`. -/
def linEquivConj (e : V ≃ₗ[ℝ] W) : (V ≃ₗ[ℝ] V) →* (W ≃ₗ[ℝ] W) where
  toFun g := (e.symm.trans g).trans e
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem linEquivConj_injective (e : V ≃ₗ[ℝ] W) : Injective (linEquivConj e) := fun g h hgh => by
  ext v
  have := congrArg (fun k : W ≃ₗ[ℝ] W => e.symm (k (e v))) hgh
  simpa [linEquivConj] using this

/-- **Selberg's lemma descends along an injective group morphism** of the linear groups. -/
theorem selbergLemma_of_injective_hom [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (φ : (W ≃ₗ[ℝ] W) →* (V ≃ₗ[ℝ] V)) (hφ : Injective φ) (hS : SelbergLemma V) :
    SelbergLemma W := by
  intro G hG
  obtain ⟨H', -, hi, htf⟩ := hS (G.map φ) (fg_map_of_fg hG φ)
  refine ⟨G ⊓ H'.comap φ, inf_le_left, ?_, fun g hg hfin => ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    exact hi
  · exact hφ ((htf _ hg.2 (φ.isOfFinOrder hfin)).trans φ.map_one.symm)

/-- **Transport of Selberg's lemma along a linear equivalence** `V ≃ₗ[ℝ] W`. -/
theorem selbergLemma_of_linearEquiv [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hS : SelbergLemma V) (e : V ≃ₗ[ℝ] W) : SelbergLemma W :=
  selbergLemma_of_injective_hom (linEquivConj e.symm) (linEquivConj_injective e.symm) hS

/-- `𝐌¹ = ℝ × ℝ⁰` is linearly `ℝ`. -/
noncomputable def minkowskiZeroEquiv : Minkowski 0 ≃ₗ[ℝ] ℝ :=
  LinearEquiv.prodUnique

/-- **Selberg's lemma in `𝐌¹`** (`d = 0`), from Externals' `selbergLemma_real`. -/
theorem selbergLemma_minkowski_zero : SelbergLemma (Minkowski 0) :=
  selbergLemma_of_linearEquiv selbergLemma_real minkowskiZeroEquiv.symm

end Selberg

/-! ## §4 Theorem B with its inputs reduced; non-vacuity -/

section TheoremB

/-- **Rem 2.3 corrected under Geroch** (`absMax_of_cauchyCompact_of_mgh` with `hK` discharged). -/
theorem absMax_of_cauchyCompact_of_mgh_of_flatGerochGH (hGer : FlatGerochGH.{u} d)
    (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    AbsMax (fun _ => True) M :=
  absMax_of_cauchyCompact_of_mgh (flatLemmaKData_of_flatGerochGH hGer) M hGH hC hM

/-- **Theorem B** (`bthm:cauclo`, l.353–359) with lemma K's data replaced by what it is
equivalent to, Geroch's existence theorem for flat spacetimes (`FlatGerochGH`). Unmarked: rests on
`barbot_B`'s upstream `sorry`s and on the named inputs. -/
theorem barbot_B_of_externals (hE : BarbotExternals d) (hSel : SelbergLemma (Minkowski d))
    (hGer : FlatGerochGH.{0} d) (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M)
    (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B hE hSel (flatLemmaKData_of_flatGerochGH hGer) M hGH hC hM

/-- **Theorem B under admissible measures** in place of `FlatGerochGH`. -/
theorem barbot_B_of_admissible (hE : BarbotExternals d) (hSel : SelbergLemma (Minkowski d))
    (hμ : FlatAdmissibleMeasures.{0} d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_of_externals hE hSel (flatGerochGH_of_admissible hμ) M hGH hC hM

/-- **Theorem B in `𝐌¹`** (`d = 0`): the bundle and Selberg are discharged
(`barbotExternals_zero`, `selbergLemma_minkowski_zero`); only `FlatGerochGH 0` remains. -/
theorem barbot_B_zero (hGer : FlatGerochGH.{0} 0) (M : FlatSpacetime.{u} 0) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} 0) (p : M₁ → M), IsFiniteCover 0 p ∧
      AMGH (CauchyCompleteClass 0) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily 0 M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_of_externals barbotExternals_zero selbergLemma_minkowski_zero hGer M hGH hC hM

/-- The static torus `ℤᵈ\𝐌ⁿ` is maximal (a translation spacetime is absolutely maximal among all
targets, `absMax_of_isTranslationSpacetime`). -/
theorem mgh_torusSpace : MGH (torusSpace d) :=
  MGH.of_absMax gh_torusSpace
    (absMax_of_isTranslationSpacetime _ isTranslationSpacetime_torusSpace)

/-- The static torus carries lemma K's data. -/
theorem flatLemmaKData_torusSpace : FlatLemmaKData (torusSpace d) :=
  cauchyCompact_torusSpace.flatLemmaKData

/-- **Non-vacuity of Theorem B's hypotheses** (kb/0012), except the universal `FlatGerochGH`
(a theorem, whose non-vacuity is its truth): at `d = 0` the bundle and Selberg hold, and in every
dimension the static torus `ℤᵈ\𝐌ⁿ` is GH, Cauchy-compact, maximal, and carries lemma K's data. -/
theorem barbot_B_hypotheses_satisfiable :
    BarbotExternals 0 ∧ SelbergLemma (Minkowski 0) ∧
      ∀ d : ℕ, GH (torusSpace d) ∧ CauchyCompact (torusSpace d) ∧ MGH (torusSpace d) ∧
        FlatLemmaKData (torusSpace d) :=
  ⟨barbotExternals_zero, selbergLemma_minkowski_zero, fun _ =>
    ⟨gh_torusSpace, cauchyCompact_torusSpace, mgh_torusSpace, flatLemmaKData_torusSpace⟩⟩

end TheoremB

end Causal.Flat
