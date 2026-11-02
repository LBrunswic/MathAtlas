import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete

/-!
# Cauchy-completeness descends from an invariant level set to `Γ\Ω`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4 and
§10. Cited UNMARKED (a step of each, not the paper's statement): `bprop:agissons` —
`GHFspace.tex:1174` (l.1173–1200, the clause "Cauchy-complete", given the completeness of the
level set `S₁`, `bcor:level_sets_complete`, as a hypothesis); `bcor:loxo_proper` —
`GHFspace.tex:3214` (l.3213–3228, the clause "Cauchy-complete", same hypothesis).

> If $\Gamma$ preserves a future complete regular convex domain $\Omega$, then, the action of
> $\rho(\Gamma)$ on $\Omega$ is properly discontinuous. If moreover $\Gamma$ is torsionfree, then
> this action is free, and the quotient $\Gamma\backslash\Omega$ is a Cauchy-complete semicomplete
> GH spacetime. (l.1176–1180)

> This function is $\Gamma$-invariant. The action of $\Gamma$ on every level set $S_{t}$ is
> isometric for the induced riemanian metric. (l.1187–1189)

> The action of $\Gamma$ on $\Omega(\widetilde{S})$ is free and properly discontinuous, and the
> quotient space $M(S) = \Gamma \backslash \Omega(\widetilde{S})$ is a Cauchy-complete globally
> hyperbolic spacetime. (l.3215–3218)

## What it is for
It serves `Loxodromic.loxo_cauchyComplete` (Cor 10.3's Cauchy-completeness): with the completeness
of the level set `S₁ ⊆ Ω⁺(Λ)` (L1, `completeSpace_inducedLength_cosmoLevel`), the `sorry` there is
`exact Lox.isCauchyComplete_flatQuotient_cosmo hc (completeSpace_inducedLength_cosmoLevel hc one_pos)`
(both theorems live in `Causal.Flat.Lox`).
The general form `isCauchyComplete_flatQuotient_of_invariant` also gives the descent half of
`Classification`'s Cauchy-completeness items.

## Main declarations (all proved, no `sorry`)
* `isCauchyComplete_flatQuotient_of_invariant`: for `S ⊆ Ω` a `Γ`-invariant spacelike Lipschitz
  hypersurface whose induced length is complete and compatible with the topology, and whose image
  `S̄ = π(S)` is a Cauchy surface of `Γ\Ω`, `Γ\Ω` is Cauchy-complete through `S̄`. Steps:
  `quot_mem_of_proj_mem` (`π⁻¹S̄ = S`, invariance), `quotProj_local` (the charts of `Γ\Ω` read `S̄`
  as an isometric image of `S`, `FlatQuotient.isLocalIsometry_proj`), `isSpacelikeLipschitz_quotSet`
  (the chart picture of `S̄` is `g • S` cut by an open), `edist_quotLen_le` (`π|S` is `1`-Lipschitz
  for the two induced lengths, `pathLength_pulled_eq_of_local`), `exists_lift_quotProj` (paths of
  `S̄` lift through the covering `π⁻¹S̄ → S̄`), `exists_quotLen_edist_lt` (length balls of `S̄` are
  images of length balls of `S`), then completeness along a fast subsequence and the topology
  field by lifting short paths.
* `isCauchyComplete_flatQuotient_cosmo`: the case `Ω = Ω⁺(Λ)`, `S = S₁ = T⁻¹(1)`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Γ` preserves `Ω`, acts freely and properly discontinuously (l.1176–1179) | ✓ carried: `Invariant`, `ProperlyDiscontinuousSMul`, `IsCancelSMul` |
| `Ω` future complete regular convex (l.1176) | ✓ carried: `CosmoRegular Λ` (only for the Cauchy surface `S̄₁`) |
| `S_t` complete for its induced metric (Cor 4.13, l.1109–1110) | ⚠ an added hypothesis (`hlev`), proved by L1 |
| `Γ` torsion-free (l.1178) | ⚠ replaced by freeness (`IsCancelSMul`), which the proof uses |
| Cor 10.3's `h`, `hlox`, `Ω(S̃) = Ω⁺(Λ)` | ⚠ weakened: not used; only `CosmoRegular Λ` and the action enter |

## SCOPE (disclosed)
* The completeness of the level set upstairs is a hypothesis; the descent through the covering
  (the paper's "the action on every level set is isometric") is what is proved. No uniform
  injectivity radius is needed: length balls downstairs are images of length balls upstairs
  (paths lift through the covering with the same length), and a Cauchy sequence is lifted along
  a fast subsequence.
* The general lemma does not use that `S` is a Cauchy surface of `Ω`: `S̄` Cauchy is assumed (`hC`),
  and supplied in the cosmological case by `isCauchySurface_quotient_cosmoLevel`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the Barbot
campaign (Lox round, L2), after the patterns of `Classification.isCauchyComplete_of_isQuotientOf_frameHoriz`
(copied, not imported) and `CauchyComplete.completeSpace_pulledLength_restrict`.
-/

namespace Causal.Flat.Lox

open Causal.Flat
open Set TopologicalSpace Filter Topology Function
open scoped ENNReal NNReal Pointwise unitInterval

variable {d : ℕ}

/-- The chart of an open subset of `𝐌ⁿ` is the inclusion (copy of `Classification`'s
`chartAt_opens_apply`, which cannot be imported). -/
theorem quot_chartAt_opens_apply (Ω : Opens (Minkowski d)) (x y : Ω) :
    chartAt (Minkowski d) x y = (y : Minkowski d) := by
  rw [TopologicalSpace.Opens.chartAt_eq]; simp [OpenPartialHomeomorph.subtypeRestr]

/-- The induced length distance is the infimum of path lengths. -/
theorem edist_inducedLengthSpace_eq_iInf {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] (S : Set M) (a b : InducedLengthSpace d S) :
    edist a b = ⨅ γ : Path (InducedLengthSpace.toSubtype a) (InducedLengthSpace.toSubtype b),
      pathLength (chartSys d S) γ := rfl

section Descent

variable {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
  {S : Set (Minkowski d)}

variable (Γ Ω S) in
/-- The projected set `S̄ = π(S ∩ Ω) ⊆ Γ\Ω`. -/
abbrev quotSet : Set (FlatQuotient Γ Ω) := FlatQuotient.proj Γ Ω '' (Subtype.val ⁻¹' S)

/-- **`π⁻¹(S̄) = S`** for an invariant `S`. -/
theorem quot_mem_of_proj_mem (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S) {y : Ω}
    (hy : FlatQuotient.proj Γ Ω y ∈ quotSet Γ Ω S) : (y : Minkowski d) ∈ S := by
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨γ, hγ, h⟩ := FlatQuotient.proj_eq_proj_iff'.1 hxy
  rw [← h]; exact hinv γ hγ x hx

/-- The projection `S → S̄`. -/
noncomputable def quotProj (hS : S ⊆ Ω) (x : S) : quotSet Γ Ω S :=
  ⟨FlatQuotient.proj Γ Ω ⟨x, hS x.2⟩, ⟨x, hS x.2⟩, x.2, rfl⟩

theorem continuous_quotProj (hS : S ⊆ Ω) : Continuous (quotProj (Γ := Γ) hS) :=
  ((FlatQuotient.continuous_proj Γ Ω).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

variable [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]

/-- The projection between the induced length spaces. -/
noncomputable def quotLen (hS : S ⊆ Ω) :
    InducedLengthSpace d S → InducedLengthSpace d (quotSet Γ Ω S) :=
  fun x => InducedLengthSpace.toSubtype.symm (quotProj hS (InducedLengthSpace.toSubtype x))

theorem quotLen_surjective (hS : S ⊆ Ω) : Surjective (quotLen (Γ := Γ) hS) := by
  rintro ⟨_, y, hy, rfl⟩
  exact ⟨InducedLengthSpace.toSubtype.symm ⟨y, hy⟩, rfl⟩

/-- **The charts of `Γ\Ω` read `S̄` as an isometric image of `S`** near each point. -/
theorem quotProj_local (hS : S ⊆ Ω) (x : S) : ∃ g : isom d, ∀ᶠ x' in 𝓝 x,
    Subtype.val x' = g • chartSys d (quotSet Γ Ω S) (quotProj hS x) (quotProj hS x') := by
  obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 (FlatQuotient.isLocalIsometry_proj Γ Ω)
  obtain ⟨g, hg⟩ := h ⟨x, hS x.2⟩
  refine ⟨g⁻¹, ?_⟩
  have hc : Continuous fun x' : S => (⟨x', hS x'.2⟩ : Ω) := continuous_subtype_val.subtype_mk _
  filter_upwards [hc.continuousAt.eventually hg] with x' hx'
  change _ = g⁻¹ • chartAt (Minkowski d) (FlatQuotient.proj Γ Ω ⟨x, hS x.2⟩)
    (FlatQuotient.proj Γ Ω ⟨x', hS x'.2⟩)
  rw [hx', quot_chartAt_opens_apply, inv_smul_smul]

/-- The upstairs path length is the pulled length of the inclusion. -/
theorem pathLength_chartSys_eq_val {a b : S} (c : Path a b) :
    pathLength (chartSys d S) c = pathLength (fun (_ : S) (y : S) => Subtype.val y) c := by
  rw [chartSys_minkowski]

/-- **`π|S` is `1`-Lipschitz** for the two induced lengths. -/
theorem edist_quotLen_le (hS : S ⊆ Ω) (a b : InducedLengthSpace d S) :
    edist (quotLen (Γ := Γ) hS a) (quotLen hS b) ≤ edist a b := by
  rw [edist_inducedLengthSpace_eq_iInf, edist_inducedLengthSpace_eq_iInf]
  refine le_iInf fun c => ?_
  rw [pathLength_chartSys_eq_val, pathLength_pulled_eq_of_local Subtype.val
    (chartSys d (quotSet Γ Ω S)) (continuous_quotProj hS) (quotProj_local hS) c]
  exact iInf_le (fun γ : Path (quotProj hS (InducedLengthSpace.toSubtype a))
    (quotProj hS (InducedLengthSpace.toSubtype b)) =>
    pathLength (chartSys d (quotSet Γ Ω S)) γ) (c.map (continuous_quotProj hS))

/-- **Paths of `S̄` lift to `S`** through the covering `π⁻¹(S̄) → S̄`. -/
theorem exists_lift_quotProj (hS : S ⊆ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S) {a : S}
    {s : quotSet Γ Ω S} (γ : Path (quotProj hS a) s) :
    ∃ (b : S) (c : Path a b), quotProj hS b = s ∧ ∀ t, quotProj hS (c t) = γ t := by
  have cov := (FlatQuotient.isCoveringMap_proj Γ Ω).restrictPreimage (quotSet Γ Ω S)
  set r : (FlatQuotient.proj Γ Ω ⁻¹' quotSet Γ Ω S) → S :=
    fun z => ⟨((z : Ω) : Minkowski d), quot_mem_of_proj_mem hinv z.2⟩ with hr_def
  have hr : Continuous r := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  obtain ⟨L, hL, hL0⟩ := cov.exists_path_lifts γ.toContinuousMap
    ⟨⟨a, hS a.2⟩, ⟨⟨a, hS a.2⟩, a.2, rfl⟩⟩
    (by simp only [Path.coe_toContinuousMap, Path.source]; rfl)
  have hLt : ∀ t, quotProj hS (r (L t)) = γ t := fun t => by
    apply Subtype.ext
    exact congrArg Subtype.val (congrFun hL t)
  refine ⟨r (L 1), Path.mk ⟨fun t => r (L t), hr.comp L.continuous⟩ ?_ rfl,
    by rw [hLt, γ.target], hLt⟩
  change r (L 0) = a
  rw [hL0]

/-- **Length balls of `S̄` are images of length balls of `S`.** -/
theorem exists_quotLen_edist_lt (hS : S ⊆ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    {a : InducedLengthSpace d S} {s : InducedLengthSpace d (quotSet Γ Ω S)} {r : ℝ≥0∞}
    (h : edist (quotLen (Γ := Γ) hS a) s < r) :
    ∃ b, quotLen hS b = s ∧ edist a b < r := by
  rw [edist_inducedLengthSpace_eq_iInf] at h
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
  obtain ⟨b, c, hb, hc⟩ := exists_lift_quotProj hS hinv (a := InducedLengthSpace.toSubtype a)
    (s := InducedLengthSpace.toSubtype s) γ
  refine ⟨InducedLengthSpace.toSubtype.symm b, hb, lt_of_le_of_lt ?_ hγ⟩
  have hq := continuous_quotProj (Γ := Γ) hS
  calc edist a (InducedLengthSpace.toSubtype.symm b)
      ≤ pathLength (chartSys d S) c := by
        rw [edist_inducedLengthSpace_eq_iInf]; exact iInf_le _ c
    _ = pathLength (chartSys d (quotSet Γ Ω S)) (c.map hq) := by
        rw [pathLength_chartSys_eq_val, pathLength_pulled_eq_of_local Subtype.val
          (chartSys d (quotSet Γ Ω S)) hq (quotProj_local hS) c]
    _ = pathLength (chartSys d (quotSet Γ Ω S)) γ := by
        refine pathLength_congr_extend _ _ _ (funext fun t => ?_)
        simp only [Path.extend, IccExtend, Path.map_coe]
        exact hc _

/-- **`S̄` is spacelike Lipschitz in the charts of `Γ\Ω`**: near `π p`, the chart picture of `S̄`
is `g • S` cut by the open `g • W`. -/
theorem isSpacelikeLipschitz_quotSet (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    (hL : IsSpacelikeLipschitzIn Ω S) : IsSpacelikeLipschitz d (quotSet Γ Ω S) := by
  rintro _ ⟨p, hp, rfl⟩
  have hloc := FlatQuotient.isLocalIsometry_proj Γ Ω
  obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 hloc
  obtain ⟨g, hg⟩ := h p
  set e := chartAt (Minkowski d) (FlatQuotient.proj Γ Ω p)
  have hsrc : ∀ᶠ y in 𝓝 p, FlatQuotient.proj Γ Ω y ∈ e.source :=
    hloc.continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (mem_chart_source _ _))
  obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.1 (hg.and hsrc)
  have hWmo : IsOpen (Subtype.val '' W : Set (Minkowski d)) :=
    Ω.isOpen.isOpenMap_subtype_val W hWo
  set V : Opens (Minkowski d) := smulOpens g ⟨Subtype.val '' W, hWmo⟩ with hVdef
  have hV : ∀ z, z ∈ (V : Set (Minkowski d)) ↔ ∃ y ∈ W, g • (y : Minkowski d) = z := by
    intro z
    rw [hVdef, coe_smulOpens]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  have hW : ∀ y ∈ W, e (FlatQuotient.proj Γ Ω y) = g • (y : Minkowski d) ∧
      FlatQuotient.proj Γ Ω y ∈ e.source := fun y hy => by
    obtain ⟨h1, h2⟩ := hWsub hy
    rw [quot_chartAt_opens_apply] at h1
    exact ⟨h1, h2⟩
  refine ⟨V, (hV _).2 ⟨p, hpW, (hW p hpW).1.symm⟩, fun z hz => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := (hV z).1 hz
    rw [← (hW y hy).1]
    exact e.map_source (hW y hy).2
  have hset : e '' (quotSet Γ Ω S ∩ e.source) ∩ V = g • S ∩ (V : Set (Minkowski d)) := by
    ext z
    constructor
    · rintro ⟨⟨m, ⟨hmS, hmsrc⟩, rfl⟩, hzV⟩
      refine ⟨?_, hzV⟩
      obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
      have hm : FlatQuotient.proj Γ Ω y = m :=
        e.injOn (hW y hy).2 hmsrc ((hW y hy).1.trans hyz)
      rw [← hyz]
      exact smul_mem_smul_set (quot_mem_of_proj_mem hinv (hm ▸ hmS))
    · rintro ⟨⟨w, hw, rfl⟩, hzV⟩
      obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
      have hyw : (y : Minkowski d) = w := (smul_left_cancel_iff g).1 hyz
      refine ⟨⟨FlatQuotient.proj Γ Ω y, ⟨⟨y, by rw [mem_preimage, hyw]; exact hw, rfl⟩,
        (hW _ hy).2⟩, ?_⟩, hzV⟩
      rw [(hW _ hy).1, hyz]
  change IsSpacelikeLipschitzIn V (e '' (quotSet Γ Ω S ∩ e.source) ∩ V)
  rw [hset]
  refine (hL.smul isom_strongMorphism g).restrict fun z hz => ?_
  obtain ⟨y, -, rfl⟩ := (hV z).1 hz
  rw [← SetLike.mem_coe, coe_smulOpens]
  exact smul_mem_smul_set y.2

end Descent

/-- **Cauchy-completeness descends to `Γ\Ω`** from a `Γ`-invariant spacelike Lipschitz `S ⊆ Ω`
with complete induced length (the descent step of `bprop:agissons`, l.1187–1189, and of
`bcor:loxo_proper`, l.3215–3218). -/
theorem isCauchyComplete_flatQuotient_of_invariant {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    [FlatQuotient.Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]
    {S : Set (Minkowski d)} (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    (hL : IsSpacelikeLipschitzIn Ω S) (hc : CompleteSpace (InducedLengthSpace d S))
    (htop : Continuous fun x : InducedLengthSpace d S =>
      (InducedLengthSpace.toSubtype x : Minkowski d))
    (hC : (flatCausality d (FlatQuotient Γ Ω)).IsCauchySurface
      (FlatQuotient.proj Γ Ω '' (Subtype.val ⁻¹' S))) :
    IsCauchyComplete d (FlatQuotient Γ Ω) := by
  have hS : S ⊆ Ω := hL.subset
  set Q := quotLen (Γ := Γ) hS with hQdef
  have hQ : LipschitzWith 1 Q := LipschitzWith.of_edist_le (edist_quotLen_le hS)
  have hsurj := quotLen_surjective (Γ := Γ) hS
  refine ⟨_, hC, isSpacelikeLipschitz_quotSet hinv hL, ?_, ?_⟩
  · -- completeness
    refine EMetric.complete_of_convergent_controlled_sequences (fun n => 1 / 2 ^ n)
      (fun n => ENNReal.div_pos_iff.2 ⟨one_ne_zero, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)
      fun u hu => ?_
    obtain ⟨a0, ha0⟩ := hsurj (u 0)
    have step : ∀ n (x : {x : InducedLengthSpace d S // Q x = u n}),
        ∃ y : {y : InducedLengthSpace d S // Q y = u (n + 1)},
          edist (x : InducedLengthSpace d S) y < 1 / 2 ^ n := by
      rintro n ⟨x, hx⟩
      have h := hu n n (n + 1) le_rfl (by omega)
      rw [← hx] at h
      obtain ⟨b, hb, hlt⟩ := exists_quotLen_edist_lt hS hinv h
      exact ⟨⟨b, hb⟩, hlt⟩
    choose g hg using step
    let a : (n : ℕ) → {x : InducedLengthSpace d S // Q x = u n} := fun n =>
      Nat.rec (motive := fun n => {x : InducedLengthSpace d S // Q x = u n}) ⟨a0, ha0⟩
        (fun n x => g n x) n
    have ha : ∀ n, edist (a n : InducedLengthSpace d S) (a (n + 1)) ≤ 1 / 2 ^ n :=
      fun n => (hg n (a n)).le
    have hcs : CauchySeq fun n => (a n : InducedLengthSpace d S) :=
      cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top ha
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨Q b, ((hQ.continuous.tendsto b).comp hb).congr fun n => (a n).2⟩
  · -- the length topology is finer than the subspace topology
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨x, rfl⟩ := hsurj s
    refine tendsto_nhds.2 fun N hN hxN => ?_
    have hup : Continuous fun y : InducedLengthSpace d S =>
        (InducedLengthSpace.toSubtype (Q y) : FlatQuotient Γ Ω) :=
      (FlatQuotient.continuous_proj Γ Ω).comp
        (htop.subtype_mk fun y => hS (InducedLengthSpace.toSubtype y).2)
    have hpre : (fun y : InducedLengthSpace d S =>
        (InducedLengthSpace.toSubtype (Q y) : FlatQuotient Γ Ω)) ⁻¹' N ∈ 𝓝 x :=
      hup.continuousAt.preimage_mem_nhds (hN.mem_nhds hxN)
    obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.1 hpre
    filter_upwards [Metric.eball_mem_nhds (Q x) hε] with y hy
    rw [Metric.mem_eball, edist_comm] at hy
    obtain ⟨b, rfl, hb⟩ := exists_quotLen_edist_lt hS hinv hy
    exact hball (by rw [Metric.mem_eball, edist_comm]; exact hb)

/-- **`Γ\Ω⁺(Λ)` is Cauchy-complete** through the image of `S₁ = T⁻¹(1)`, given the three fields
of the level set upstairs (`bprop:agissons`, l.1178–1180; `bcor:loxo_proper`, l.3215–3218). -/
theorem isCauchyComplete_flatQuotient_cosmo {Λ : Set (PenroseSphere d × ℝ)} (h : CosmoRegular Λ)
    {Γ : Subgroup (isom d)} [FlatQuotient.Invariant Γ h.regular.opens]
    [ProperlyDiscontinuousSMul Γ h.regular.opens] [IsCancelSMul Γ h.regular.opens]
    (hlev : IsSpacelikeLipschitzIn h.regular.opens (cosmoLevel Λ 1) ∧
      CompleteSpace (InducedLengthSpace d (cosmoLevel Λ 1)) ∧
      Continuous fun x : InducedLengthSpace d (cosmoLevel Λ 1) =>
        (InducedLengthSpace.toSubtype x : Minkowski d)) :
    IsCauchyComplete d (FlatQuotient Γ h.regular.opens) := by
  have hP : PreservesOmega Λ Γ := fun γ hγ => by
    ext p
    constructor
    · intro hp
      have hp' : γ • p ∈ h.regular.opens := hp
      have := FlatQuotient.Invariant.smul_mem (⟨γ⁻¹, Γ.inv_mem hγ⟩ : Γ) _ hp'
      simp only [inv_smul_smul] at this
      exact this
    · intro hp
      exact FlatQuotient.Invariant.smul_mem (⟨γ, hγ⟩ : Γ) p (show p ∈ h.regular.opens from hp)
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ cosmoLevel Λ 1, γ • p ∈ cosmoLevel Λ 1 :=
    fun γ hγ p hp => (smul_mem_cosmoLevel_iff (hP γ hγ)).2 hp
  exact isCauchyComplete_flatQuotient_of_invariant hinv hlev.1 hlev.2.1 hlev.2.2
    (isCauchySurface_quotient_cosmoLevel (h := h) hP one_pos).1

end Causal.Flat.Lox
