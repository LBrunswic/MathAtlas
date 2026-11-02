import Causal.Flat.Penrose
import Causal.Flat.Achronal
import Mathlib.Analysis.Convex.Continuous

/-!
# `Causal.Flat.Cosmological` — the cosmological time of a future regular convex domain

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.2
after `bcor:futetpast` (`papers/barbot/legacy/labeled/GHFspace.tex`; line numbers below are those
of the labelled copy). **No label is marked.** Partial, unmarked (see SCOPE): [4.CT] (prose,
l.1043–1070); `bprop:lip` — `GHFspace.tex:1074` (chordal form); `bprop:regular_cauchy_complete`
— `GHFspace.tex:1148` (GH, and the level sets are Cauchy surfaces, with no `sorry`; completeness
not stated); `bprop:agissons` — `GHFspace.tex:1174` (the `Ω`-level invariance only). Not
attempted: `bcor:level_sets_complete` — `GHFspace.tex:1109` (see SCOPE).

> For any point $p$ in $\Omega^{+}(\Lambda)$, consider every future oriented timelike curve
> starting from a point in $\partial\Omega^{+}(\Lambda)$ and ending at $p$. The proper times of all
> these curves are uniformely bounded: let $T(p)$ be the supremum value of these proper times.
> There is a unique $\pi(p)$ in $\partial\Omega^{+}(\Lambda)$ for which $T(p)$ is equal to
> $-\sqrt{\mid p-\pi(p) \mid^{2}}$ […] The function $T$ […] is a $C^{1}$-convex function […]
> The level sets $S_{t} = T^{-1}(t)$ are convex spacelike hypersurfaces […] the direction of the
> tangent space to $S_{t}$ at some point $p$ is the orthogonal of $p-\pi(p)$. […]
> $S(p+\epsilon n(p)) = S(p) + \epsilon$. (l.1049–1068)

> If $\Lambda$ contains at least $2$ elements, then $\Omega^{\pm}(\Lambda)$, if nonempty, is
> regular. (Def 4.4, l.900–901)

> The Gauss map $n: S_{t} \rightarrow {\mathbb H}^{n-1}$, where ${\mathbb H}^{n-1}$ is equipped
> with its usual hyperbolic metric is $\frac{1}{t}$-Lipschitz. (l.1076–1078)

> Every $S_{t}$ is complete. (l.1110)

> Finally, as it is proved in \cite{bonsante}, lemma $4.9$, every $S_{t}$ is a Cauchy
> hypersurface for $\Omega(\Lambda)$. (l.1144–1145)

> Future complete regular convex domains are globally hyperbolic Cauchy-complete, admitting as
> Cauchy hypersurfaces the level sets of the cosmological time function. (l.1149–1151)

> If $\Gamma$ preserves a future complete regular convex domain $\Omega$, then, the action of
> $\rho(\Gamma)$ on $\Omega$ is properly discontinuous. […] (l.1176–1180)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, and his `ℍⁿ⁻¹` is the unit future hyperboloid of
`Minkowski d`. Two null directions force `d ≥ 1`.

## What is proved (`Ω = Ω⁺(Λ)`, `CosmoRegular Λ`: future regular with two null directions)

* `cosmoTime Λ p = sSup {√(−|p − q|²) | q ∈ ∂Ω, q ≤ p}`; the sup is a **maximum**
  (`isGreatest_cosmoTimes`, `bddAbove_cosmoTimes`), equal to the sup over `cl Ω ∩ J⁻(p)`
  (`cosmoTime_eq_sSup_cosmoPast`), attained at a **unique** `r(p) = cosmoRetract Λ p ∈ ∂Ω`
  (`eq_cosmoRetract`, `eq_cosmoRetract_of_frontier`); `T > 0` on `Ω` (`cosmoTime_pos`).
* `T` is **concave** (`concaveOn_cosmoTime`), hence **continuous** and locally Lipschitz on `Ω`;
  **strictly increasing along `≤`** (`cosmoTime_lt_of_le`, `cosmoTime_lt_of_le_opens`);
  **`T → 0` at `∂Ω`** (`tendsto_cosmoTime_frontier`); **`T → ∞` along future causal rays**
  (`tendsto_cosmoTime_add_smul`) **and along every future-inextensible causal curve of `Ω`**
  (`exists_lt_cosmoTime_of_futureInextensible`); **`T → 0` along every past-inextensible
  causal curve of `Ω`** (`exists_cosmoTime_lt_of_pastInextensible`); the support property
  `minkB_cosmoRetract_le` and the supporting bound `cosmoTime_mul_le`.
* The Gauss map `n = (p − r(p))/T(p)`, future unit timelike (`minkQ_gaussMap`,
  `isFutureTimelike_gaussMap`); **the normal flow** `T(p + εn) = T(p) + ε`, same `r`, same `n`
  (`cosmoTime_add_smul_gaussMap`), and `S_{t+ε} = S_t + εn` (`cosmoLevel_add_eq_image`).
* `S_t` (`t > 0`): **acausal** (`isAcausal_cosmoLevel`), **closed**, **the entire graph of a
  1-Lipschitz function** (`cosmoLevel_eq_graph`, `lipschitzWith_cosmoGraph`), **spacelike
  Lipschitz with a point-local `c < 1`** (`isSpacelikeLipschitz_cosmoLevel`, the fields of
  `IsSpacelikeLipschitzIn` written out), and **a Cauchy surface of `Ω`**
  (`isCauchySurfaceOn_cosmoLevel`, ETT's `IsCauchySurfaceOn`, no `sorry`): Bonsante's Lemma 4.9
  is **proved** here (`bonsante_exhaustion`), so `Bonsante_exhaustion` is no longer an external
  (DEC-36); its cone witness is `bonsante_exhaustion_cone`.
* `bprop:lip`, chordal form: `t² |n(p) − n(p')|² ≤ |p − p'|²` on `S_t`
  (`minkQ_gaussMap_sub_le`, `sqrt_minkQ_gaussMap_sub_le`); `∂Ω` is achronal
  (`minkQ_sub_nonneg_of_mem_frontier`).
* Isometries `g` with `g Ω = Ω`: `T(gp) = T(p)`, `g S_t = S_t`, `r(gp) = g r(p)`
  (`cosmoTime_smul`, `smul_cosmoLevel`, `cosmoRetract_smul`, `agissons_invariant`).
* The future cone (`d ≥ 1`): `CosmoRegular`, `T(p) = √(−|p|²)`, `r(p) = 0`, `n(p) = p/T(p)`
  (`cosmoRegular_cone`, `cosmoTime_cone`, `gaussMap_cone`).
* **Finding** (DEC-27): the printed boundedness is false for a closed `Λ` with two elements and
  one null direction (`not_cosmoBoundedAsPrinted`, `Λ = {(u, 0), (u, 1)}`).
* **The `W`-local extension lemmas** (model-free, namespace `Causal.Causality`): a curve of an
  open `W` converging at an open end to `p ∈ W` is extensible at that end in `W`
  (`pastExtensible_of_tendsto_opens`, `futureExtensible_of_tendsto_opens`; the library states
  `pastExtensible_of_tendsto` for `W = ⊤` only); `futureExtensible_of_isGreatest`;
  `FutureExtensible.of_comp`; the `arctan` reparametrisation `CausalCurveIn.arctanReparam`.
* Lorentzian algebra: reverse Cauchy–Schwarz (`sqrt_mul_sqrt_le_neg_minkB`), reverse triangle
  inequality (`sqrt_neg_minkQ_add_le`), `minkB_neg_of_isFutureTimelike`, `minkQ_sub_pos_of_ne`.

## How Bonsante's Lemma 4.9 is proved

Let `c` be an inextensible causal curve of `Ω`, reparametrised by `arctan` onto a bounded
interval. If `T ≤ B` along it, then at a greatest parameter it is extensible by appending
(`Ω` is open); otherwise its time coordinate is bounded (`T(x)² ≥ 2(z₀ − ‖z⃗‖)(x − p)₀` on
`J⁺(p)`, `z = p − r(p)`, `two_mul_fst_sub_le_cosmoTime_sq`), the spatial displacement is bounded
by the elapsed time, so the curve is Cauchy at its upper end and converges in the complete `𝐌ⁿ`
to a point of `J⁺(Ω) ⊆ Ω`, and it extends there. If `T ≥ ε > 0` along it, the two null planes
bound the time coordinate below (`fst_sub_le_of_mem_closure`), the curve converges at its lower
end to a point of `cl Ω`, which is not on `∂Ω` since `T → 0` there, and it extends there. Both
contradict inextensibility; the intermediate value theorem and strict monotonicity of `T` then
give exactly one point on `S_t` (`isCauchySurfaceOn_cosmoLevel_of`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Λ` future regular (Def 4.5, l.913–919) | ✓ carried (`FutureRegular`) |
| `Λ` has at least two elements (Def 4.4, l.900–901; "not reduced to one point", l.1001–1004) | ⚠ strengthened: two elements with **distinct null directions** (`CosmoRegular.two`). The paper's condition is too weak: `not_cosmoBoundedAsPrinted` refutes the boundedness for `Λ = {(u, 0), (u, 1)}`, two elements sharing a direction. Bonsante's Def 4.1 asks two non-parallel null support planes, which is what `CosmoRegular.two` asks; so Barbot's "completely equivalent" (l.921–922) fails |
| `Λ` closed (standing convention, l.1001–1004) | ⚠ weakened: not used |
| "timelike curves from `∂Ω`" | ⚠ read on straight segments (see SCOPE) |
| `n ≥ 2` | any `d`; two directions force `d ≥ 1` |
| Bonsante's Lemma 4.9 (cited, l.1144–1145) | ✓ proved (`bonsante_exhaustion`), not assumed |
| 4.16: `Γ` discrete, torsion-free | ⚠ weakened: not used (only the invariance part is proved) |

## SCOPE (disclosed)

* **`T` is defined on segments.** Barbot's sup is over timelike curves; in `𝐌ⁿ` the segment
  maximises proper time (reverse triangle inequality), but the curve form is not stated: the
  library's causal curves carry no proper time.
* **"Time function"** is read as continuity on `Ω` (`continuousOn_cosmoTime`) plus strict
  monotonicity along `≤_⊤` and `≤_Ω` (`cosmoTime_lt_of_le`, `cosmoTime_lt_of_le_opens`): the
  library's `IsTimeFunction` (`Causal/Morphism.lean:832`) is global and has no `On`-version for
  an open set.
* **Barbot's typos, read here:** "`T(p) = −√(|p − π(p)|²)`" (l.1055) is `√(−|p − π(p)|²)`;
  `n(p)`'s denominator "`⟨p − π(p) | p − n(p)⟩`" (l.1064) is `⟨p − π(p) | p − π(p)⟩`;
  "`C¹`-convex" (l.1060): `T` is concave (its superlevel sets are convex) — proved; `C¹` is not.
* `bprop:lip` is proved in chordal form (`√|n − n'|²`, the Minkowski-form chord of `ℍᵈ`,
  against `√|p − p'|²`), at `ε = t` (Barbot's `ε < t`, then `ε → t`); the passage to the induced
  length and the hyperbolic metric (infimum of chord sums, l.1087–1091) is not proved.
* `bcor:level_sets_complete` is not attempted, and Cauchy-completeness of 4.14 and the
  isometric action on `(S_t, induced length)` of 4.16 are not stated: `Causal.Flat.InducedLength`
  is not built at this point (no `.olean`), so it is not imported; `isSpacelikeLipschitz_cosmoLevel`
  writes `IsSpacelikeLipschitzIn`'s fields out, to be restated through it at graduation.
* **4.16** beyond invariance (proper discontinuity, freeness, the quotient `Γ\Ω`) is not
  attempted; the quotient is another package's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 4, package WP-33b-Cosmological.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {W : Opens M} {I : Set ℝ}
  {c : ℝ → M} {a b : ℝ}

/-! ### `W`-local extension at an open end (model-free) -/

/-- A causal curve of `⊤` with image in the open set `W` is a causal curve of `W`. -/
theorem CausalCurveIn.of_top_of_mem (hc : C.CausalCurveIn ⊤ I c) (hmem : ∀ t ∈ I, c t ∈ W) :
    C.CausalCurveIn W I c :=
  ⟨hc.nonempty, hc.ordConnected, fun s hs s' hs' =>
    CurveOn.restrict (hc.curve s hs s' hs') le_rfl le_rfl le_top
      fun t ht => hmem t (hc.ordConnected.out hs hs' ht)⟩

/-- **A limit at an open lower end, in an open set `W`**: the `W`-local form of
`pastExtensible_of_tendsto` (`Causal/Inextensible.lean:859`), for a limit `p ∈ W` with
`J⁻_W(p) ≠ {p}`. The library's form is stated for `W = ⊤`; here the limit is adjoined in `⊤`
(`causalCurveIn_insert`), the result restricted to `W` (its image is in `W`), and the prepended
curve is taken in `W`. -/
theorem pastExtensible_of_tendsto_opens (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) {p : M} (hpW : p ∈ W) (haI : ∀ t ∈ I, a < t)
    (hins : (insert a I).OrdConnected) (hlim : Tendsto c (𝓝[>] a) (𝓝 p))
    (hp : C.Jminus W {p} ≠ {p}) : C.PastExtensible W I c := by
  have hcT : C.CausalCurveIn ⊤ I c := hc.mono_opens le_top
  have h₀T := causalCurveIn_insert hJ hSC hC hcT haI hins hlim
  have h₀ : C.CausalCurveIn W (insert a I) (fun t => if t ≤ a then p else c t) := by
    refine h₀T.of_top_of_mem fun t ht => ?_
    by_cases hta : t ≤ a
    · simp only [hta, if_true]; exact hpW
    · simp only [hta, if_false]
      rcases ht with h | h
      · exact absurd h.le hta
      · exact hc.mem h
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl hpW : p ∈ C.Jminus W {p}) hp
  have hq : C.le W q p := by simpa using hqJ
  have hleast : IsLeast (insert a I) a := ⟨mem_insert a I, fun t ht => by
    rcases ht with h | h
    · exact h.ge
    · exact (haI t h).le⟩
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC h₀ hleast (q := q) (by simpa using hq)
  have hcI : ∀ t ∈ I, c' t = c t := fun t ht => by
    rw [heq t (mem_insert_of_mem a ht)]
    simp [not_le.2 (haI t ht)]
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr (mem_insert_of_mem a ht), by
    rw [image_id]; exact hc.ordConnected, hcI, ?_⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  · intro t ht t' ht' htt'
    have hat' : a < t' := (haI t ht).trans_le htt'
    rcases ht' with ht' | ht'
    · exact absurd ht'.2 (not_le.2 hat')
    · rcases ht' with h | h
      · exact absurd h (ne_of_gt hat')
      · exact ⟨t', h, rfl⟩
  · rw [h0] at hqt
    subst hqt
    exact hqne (hcaus (C.le_mono le_top hq) (le_of_tendsto hJ hcT haI hins hlim ht))

/-- **A limit at an open upper end, in an open set `W`**, by time reversal. -/
theorem futureExtensible_of_tendsto_opens (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) {p : M} (hpW : p ∈ W) (hbI : ∀ t ∈ I, t < b)
    (hins : (insert b I).OrdConnected) (hlim : Tendsto c (𝓝[<] b) (𝓝 p))
    (hp : C.Jplus W {p} ≠ {p}) : C.FutureExtensible W I c := by
  apply FutureExtensible.of_dual_reverse
  refine pastExtensible_of_tendsto_opens (C := C.dual) hJ (dual_stronglyCausal.2 hSC)
    (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus) hc.reverse hpW (a := -b)
    (fun t ht => by have := hbI (-t) ht; linarith) ?_ ?_ hp
  · rw [← Set.neg_insert]
    exact ⟨fun x hx y hy z hz => hins.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
  · exact hlim.comp tendsto_neg_nhdsGT_neg

/-- Extensibility at the future end transported along a strictly increasing reparametrisation
(the future-end twin of `PastExtensible.of_comp`, `Causal/Inextensible.lean:475`). -/
theorem FutureExtensible.of_comp {J : Set ℝ} {d : ℝ → M} {ψ : ℝ → ℝ}
    (hd : C.FutureExtensible W J d) (hψ : StrictMonoOn ψ I) (hmaps : MapsTo ψ I J)
    (hsurj : SurjOn ψ I J) (heq : ∀ t ∈ I, d (ψ t) = c t) : C.FutureExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩ := hd
  have himg : (φ ∘ ψ) '' I = φ '' J := by rw [image_comp, hsurj.image_eq_of_mapsTo hmaps]
  refine ⟨I', c', hcurve, ⟨φ ∘ ψ, ?_, ?_, ?_, ?_, ?_⟩, ⟨t', ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact hφ (hmaps hs) (hmaps hs') (hψ hs hs' h)
  · intro s hs
    exact hφmaps (hmaps hs)
  · rw [himg]; exact hφoc
  · intro t ht
    simp only [Function.comp]
    rw [hφeq _ (hmaps ht), heq t ht]
  · intro t ht u hu htu
    rw [himg]
    exact hφend (ψ t) (hmaps ht) u hu htu
  · intro t ht h
    exact hgrow (ψ t) (hmaps ht) (by rw [heq t ht]; exact h)

/-- **Appending at a greatest point is an extension at the future end** (the one-sided form of
`extensible_of_isGreatest`, by time reversal of `pastExtensible_of_isLeast`). -/
theorem futureExtensible_of_isGreatest (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) (hb : IsGreatest I b) (hJ : C.Jplus W {c b} ≠ {c b}) :
    C.FutureExtensible W I c := by
  apply FutureExtensible.of_dual_reverse
  refine pastExtensible_of_isLeast (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus)
    hc.reverse (a := -b) ⟨by simpa using hb.1, fun t ht => ?_⟩ ?_
  · have := hb.2 (show -t ∈ I from ht)
    linarith
  · simpa using hJ

/-- **Reparametrisation onto a bounded interval** by `arctan`: `c ∘ tan` over `arctan '' I` is a
causal curve of `W`, its parameters lie in `]−π/2, π/2[`, and an extension of it at the past
(resp. future) end is one of `c`. -/
theorem CausalCurveIn.arctanReparam (hc : C.CausalCurveIn W I c) :
    C.CausalCurveIn W (Real.arctan '' I) (c ∘ Real.tan) ∧
      Real.arctan '' I ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      (∀ u ∈ Real.arctan '' I, Real.tan u ∈ I) ∧
      (C.PastExtensible W (Real.arctan '' I) (c ∘ Real.tan) → C.PastExtensible W I c) ∧
      (C.FutureExtensible W (Real.arctan '' I) (c ∘ Real.tan) → C.FutureExtensible W I c) := by
  have hsub : Real.arctan '' I ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨Real.neg_pi_div_two_lt_arctan s, Real.arctan_lt_pi_div_two s⟩
  have htan : ∀ u ∈ Real.arctan '' I, Real.tan u ∈ I := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Real.tan_arctan]; exact hs
  have heq : ∀ t ∈ I, (c ∘ Real.tan) (Real.arctan t) = c t := fun t _ => by
    simp [Function.comp, Real.tan_arctan]
  refine ⟨hc.comp (hc.nonempty.image _)
    (isPreconnected_iff_ordConnected.1 (hc.ordConnected.isPreconnected.image _
      Real.continuous_arctan.continuousOn))
    (Real.strictMonoOn_tan.mono hsub) (Real.continuousOn_tan_Ioo.mono hsub) htan, hsub, htan,
    fun hd => hd.of_comp (Real.arctan_strictMono.strictMonoOn I) (mapsTo_image _ _)
      (surjOn_image _ _) heq,
    fun hd => hd.of_comp (Real.arctan_strictMono.strictMonoOn I) (mapsTo_image _ _)
      (surjOn_image _ _) heq⟩

end Causality

end Causal

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Metric
open scoped Pointwise NNReal

variable {d : ℕ}

/-! ### Bilinear algebra (private: `Isometries`, in progress, states public copies) -/

private theorem mB_add_right (v p q : Minkowski d) : minkB v (p + q) = minkB v p + minkB v q := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_right]; ring

private theorem mB_add_left (p q v : Minkowski d) : minkB (p + q) v = minkB p v + minkB q v := by
  rw [minkB_comm, mB_add_right, minkB_comm, minkB_comm v]

private theorem mB_sub_right (v p q : Minkowski d) : minkB v (p - q) = minkB v p - minkB v q := by
  simp only [minkB, Prod.fst_sub, Prod.snd_sub, inner_sub_right]; ring

private theorem mB_sub_left (p q v : Minkowski d) : minkB (p - q) v = minkB p v - minkB q v := by
  rw [minkB_comm, mB_sub_right, minkB_comm, minkB_comm v]

private theorem mB_smul_right (v p : Minkowski d) (c : ℝ) : minkB v (c • p) = c * minkB v p := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring

private theorem mB_smul_left (v p : Minkowski d) (c : ℝ) : minkB (c • v) p = c * minkB v p := by
  rw [minkB_comm, mB_smul_right, minkB_comm]

private theorem mQ_add (v w : Minkowski d) :
    minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  simp only [minkQ, minkB, Prod.fst_add, Prod.snd_add, norm_add_sq_real]; ring

private theorem mQ_sub (v w : Minkowski d) :
    minkQ (v - w) = minkQ v - 2 * minkB v w + minkQ w := by
  simp only [minkQ, minkB, Prod.fst_sub, Prod.snd_sub, norm_sub_sq_real]; ring

/-! ### Lorentzian inequalities on the future cone -/

theorem isFutureCausal_iff_norm_le {v : Minkowski d} : IsFutureCausal v ↔ ‖v.2‖ ≤ v.1 := by
  refine ⟨fun h => ?_, fun h => ⟨(norm_nonneg _).trans h, ?_⟩⟩
  · exact (sq_le_sq₀ (norm_nonneg _) h.1).1 (minkQ_le_zero_iff.1 h.2)
  · exact minkQ_le_zero_iff.2 (pow_le_pow_left₀ (norm_nonneg _) h 2)

/-- **The reverse Cauchy–Schwarz inequality** for future causal vectors:
`√(−|a|²) √(−|b|²) ≤ −⟨a | b⟩`. -/
theorem sqrt_mul_sqrt_le_neg_minkB {a b : Minkowski d} (ha : IsFutureCausal a)
    (hb : IsFutureCausal b) : √(-minkQ a) * √(-minkQ b) ≤ -minkB a b := by
  have ha' := isFutureCausal_iff_norm_le.1 ha
  have hb' := isFutureCausal_iff_norm_le.1 hb
  have hi : inner ℝ a.2 b.2 ≤ ‖a.2‖ * ‖b.2‖ := real_inner_le_norm _ _
  have hna := norm_nonneg a.2
  have hnb := norm_nonneg b.2
  have hR : 0 ≤ a.1 * b.1 - ‖a.2‖ * ‖b.2‖ := by nlinarith
  have hqa : 0 ≤ -minkQ a := by linarith [ha.2]
  rw [← Real.sqrt_mul hqa]
  calc √(-minkQ a * -minkQ b) ≤ a.1 * b.1 - ‖a.2‖ * ‖b.2‖ := by
        refine Real.sqrt_le_iff.2 ⟨hR, ?_⟩
        unfold minkQ; nlinarith [sq_nonneg (a.1 * ‖b.2‖ - b.1 * ‖a.2‖)]
    _ ≤ -minkB a b := by unfold minkB; linarith

theorem minkB_nonpos_of_isFutureCausal {a b : Minkowski d} (ha : IsFutureCausal a)
    (hb : IsFutureCausal b) : minkB a b ≤ 0 := by
  have := sqrt_mul_sqrt_le_neg_minkB ha hb
  have := mul_nonneg (Real.sqrt_nonneg (-minkQ a)) (Real.sqrt_nonneg (-minkQ b))
  linarith

/-- A future timelike vector and a nonzero future causal vector have `⟨a | b⟩ < 0`. -/
theorem minkB_neg_of_isFutureTimelike {a b : Minkowski d} (ha : IsFutureTimelike a)
    (hb : IsFutureCausal b) (hb0 : b ≠ 0) : minkB a b < 0 := by
  have hb1 : 0 < b.1 := lt_of_le_of_ne hb.1 fun h => hb0 (eq_zero_of_fst_eq_zero h.symm hb.2)
  have ha' := isFutureTimelike_iff_norm_lt.1 ha
  have hb' := isFutureCausal_iff_norm_le.1 hb
  have hi : inner ℝ a.2 b.2 ≤ ‖a.2‖ * ‖b.2‖ := real_inner_le_norm _ _
  have hna := norm_nonneg a.2
  unfold minkB
  nlinarith

theorem isFutureCausal_add {a b : Minkowski d} (ha : IsFutureCausal a) (hb : IsFutureCausal b) :
    IsFutureCausal (a + b) := by
  rw [isFutureCausal_iff_norm_le] at *
  simp only [Prod.snd_add, Prod.fst_add]
  exact (norm_add_le _ _).trans (add_le_add ha hb)

theorem isFutureTimelike_add {a b : Minkowski d} (ha : IsFutureTimelike a)
    (hb : IsFutureCausal b) : IsFutureTimelike (a + b) := by
  rw [isFutureTimelike_iff_norm_lt] at *
  rw [isFutureCausal_iff_norm_le] at hb
  simp only [Prod.snd_add, Prod.fst_add]
  exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le ha hb)

theorem IsFutureTimelike.isFutureCausal {a : Minkowski d} (ha : IsFutureTimelike a) :
    IsFutureCausal a := ⟨ha.1.le, ha.2.le⟩

/-- **The reverse triangle inequality**: on the future cone, `√(−|·|²)` is superadditive. -/
theorem sqrt_neg_minkQ_add_le {a b : Minkowski d} (ha : IsFutureCausal a)
    (hb : IsFutureCausal b) : √(-minkQ a) + √(-minkQ b) ≤ √(-minkQ (a + b)) := by
  have hqa : 0 ≤ -minkQ a := by linarith [ha.2]
  have hqb : 0 ≤ -minkQ b := by linarith [hb.2]
  have hab := (isFutureCausal_add ha hb).2
  refine (Real.le_sqrt (by positivity) (by linarith)).2 ?_
  have h := sqrt_mul_sqrt_le_neg_minkB ha hb
  rw [add_sq, Real.sq_sqrt hqa, Real.sq_sqrt hqb, mQ_add]
  linarith

theorem sqrt_neg_minkQ_smul {c : ℝ} (hc : 0 ≤ c) (v : Minkowski d) :
    √(-minkQ (c • v)) = c * √(-minkQ v) := by
  rw [minkQ_smul, show -(c ^ 2 * minkQ v) = c ^ 2 * -minkQ v by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Two distinct future timelike vectors on the same hyperboloid differ by a spacelike vector. -/
theorem minkQ_sub_pos_of_ne {a b : Minkowski d} (ha : IsFutureTimelike a)
    (hb : IsFutureTimelike b) (hq : minkQ a = minkQ b) (hne : a ≠ b) : 0 < minkQ (a - b) := by
  by_contra h
  push Not at h
  rcases le_total 0 (a - b).1 with h0 | h0
  · have hy : IsFutureCausal (a - b) := ⟨h0, h⟩
    have hy0 : a - b ≠ 0 := sub_ne_zero.2 hne
    have hB := minkB_neg_of_isFutureTimelike hb hy hy0
    have := mQ_add b (a - b)
    rw [add_sub_cancel] at this
    linarith
  · have hy : IsFutureCausal (b - a) := ⟨by simpa using h0, by rw [← neg_sub, minkQ_neg]; exact h⟩
    have hy0 : b - a ≠ 0 := sub_ne_zero.2 hne.symm
    have hB := minkB_neg_of_isFutureTimelike ha hy hy0
    have := mQ_add a (b - a)
    rw [add_sub_cancel] at this
    rw [← neg_sub, minkQ_neg] at h
    linarith

/-! ### The domain: future regular with two null directions -/

/-- **A future regular `Λ` with two distinct null directions** — the hypothesis under which the
cosmological time is finite (Bonsante's regular domains have at least two non-parallel null
support planes; Barbot's "at least 2 elements" (Def 4.4, l.900–901) is weaker, since two elements
may share a direction, see `not_cosmoBoundedAsPrinted`). -/
structure CosmoRegular (Λ : Set (PenroseSphere d × ℝ)) : Prop where
  regular : FutureRegular Λ
  two : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, w₁.1 ≠ w₂.1

/-- The proper time `√(−|p − q|²)` of the straight segment from `q` to `p`. -/
noncomputable def segTime (q p : Minkowski d) : ℝ := √(-minkQ (p - q))

/-- `cl Ω ∩ J⁻(p)`: the points of the closure of `Ω = Ω⁺(Λ)` in the causal past of `p`. -/
def cosmoPast (Λ : Set (PenroseSphere d × ℝ)) (p : Minkowski d) : Set (Minkowski d) :=
  closure (omegaPlus Λ) ∩ {q | (minkowski d).le ⊤ q p}

/-- The proper times of the segments from the boundary `∂Ω` to `p`. -/
def cosmoTimes (Λ : Set (PenroseSphere d × ℝ)) (p : Minkowski d) : Set ℝ :=
  (fun q => segTime q p) '' {q | q ∈ frontier (omegaPlus Λ) ∧ (minkowski d).le ⊤ q p}

/-- **The cosmological time** `T(p) = sup {√(−|p − q|²) | q ∈ ∂Ω, q ≤ p}` ([4.CT], l.1048–1052,
read on segments). -/
noncomputable def cosmoTime (Λ : Set (PenroseSphere d × ℝ)) (p : Minkowski d) : ℝ :=
  sSup (cosmoTimes Λ p)

variable {Λ : Set (PenroseSphere d × ℝ)}

theorem segTime_nonneg (q p : Minkowski d) : 0 ≤ segTime q p := Real.sqrt_nonneg _

theorem continuous_segTime_left (p : Minkowski d) : Continuous fun q : Minkowski d => segTime q p :=
  Real.continuous_sqrt.comp ((continuous_minkQ.comp (continuous_const.sub continuous_id)).neg)

theorem sq_segTime {q p : Minkowski d} (h : (minkowski d).le ⊤ q p) :
    segTime q p ^ 2 = -minkQ (p - q) :=
  Real.sq_sqrt (by linarith [(le_top_iff_minkQ.1 h).2])

/-- The closure of `Ω⁺(Λ)` lies in the closed half-spaces. -/
theorem closure_omegaPlus_subset :
    closure (omegaPlus Λ) ⊆ {q | ∀ w ∈ Λ, minkB (nullVec w.1) q ≤ w.2} := by
  refine closure_minimal (fun q hq w hw => (mem_omegaPlus.1 hq w hw).le) ?_
  simp only [setOf_forall]
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    isClosed_le (continuous_minkB_nullVec w.1) continuous_const

theorem norm_add_penroseSphere_le (u u' : PenroseSphere d) :
    ‖(u : EuclideanSpace ℝ (Fin d)) + u'‖ ≤ 2 := by
  have := norm_add_le (u : EuclideanSpace ℝ (Fin d)) u'
  rw [norm_penroseSphere, norm_penroseSphere] at this; linarith

/-- Two distinct directions: `‖u + u'‖ < 2`. -/
theorem norm_add_penroseSphere_lt {u u' : PenroseSphere d} (h : u ≠ u') :
    ‖(u : EuclideanSpace ℝ (Fin d)) + u'‖ < 2 := by
  have h1 := norm_add_sq_real (u : EuclideanSpace ℝ (Fin d)) u'
  have h2 := norm_sub_sq_real (u : EuclideanSpace ℝ (Fin d)) u'
  rw [norm_penroseSphere, norm_penroseSphere] at h1 h2
  have h3 : 0 < ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h' => h (Subtype.ext h'))
  have h4 := norm_nonneg ((u : EuclideanSpace ℝ (Fin d)) + u')
  nlinarith [mul_pos h3 h3]

/-- **The two-direction bound**: for `q ∈ cl Ω` with `q ≤ p`, the time elapsed from `q` to `p` is
controlled by the two null planes `w₁, w₂`. -/
theorem fst_sub_le_of_mem_closure {w₁ w₂ : PenroseSphere d × ℝ} (hw₁ : w₁ ∈ Λ) (hw₂ : w₂ ∈ Λ)
    {p q : Minkowski d} (hq : q ∈ closure (omegaPlus Λ)) (hqp : (minkowski d).le ⊤ q p) :
    (2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖) * (p - q).1 ≤
      (w₁.2 - minkB (nullVec w₁.1) p) + (w₂.2 - minkB (nullVec w₂.1) p) := by
  have hc := closure_omegaPlus_subset hq
  have h1 := hc w₁ hw₁
  have h2 := hc w₂ hw₂
  have hz := minkowski_le_top_iff.1 hqp
  simp only [minkB_nullVec] at h1 h2 ⊢
  have hi : inner ℝ ((w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1) (p.2 - q.2) ≤
      ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖ * ‖p.2 - q.2‖ := real_inner_le_norm _ _
  rw [inner_add_left, inner_sub_right, inner_sub_right] at hi
  have hn := norm_nonneg ((w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1)
  have hm := mul_le_mul_of_nonneg_left hz hn
  simp only [Prod.fst_sub]
  nlinarith

theorem isClosed_le_top_left (p : Minkowski d) :
    IsClosed {q : Minkowski d | (minkowski d).le ⊤ q p} := by
  simp only [minkowski_le_top_iff]
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- **`cl Ω ∩ J⁻(p)` is compact** (two directions). -/
theorem isCompact_cosmoPast (h : CosmoRegular Λ) (p : Minkowski d) : IsCompact (cosmoPast Λ p) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  set D := (w₁.2 - minkB (nullVec w₁.1) p) + (w₂.2 - minkB (nullVec w₂.1) p)
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_closure.inter (isClosed_le_top_left p))
    ((Metric.isBounded_closedBall (x := p) (r := D / κ)).subset fun q hq => ?_)
  have hb := fst_sub_le_of_mem_closure hw₁ hw₂ hq.1 hq.2
  have hz := minkowski_le_top_iff.1 hq.2
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  have h1 : (p - q).1 ≤ D / κ := by rw [le_div_iff₀ hκ]; linarith
  simp only [Prod.fst_sub] at h1
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · rw [Prod.fst_sub, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [norm_nonneg (p.2 - q.2)]
  · rw [Prod.snd_sub]; linarith

/-- Pushing a point to the past by `(t, 0)`: the proper time from it grows. -/
theorem neg_minkQ_add_time (z : Minkowski d) (t : ℝ) :
    -minkQ (z + ((t, 0) : Minkowski d)) = -minkQ z + 2 * t * z.1 + t ^ 2 := by
  simp only [minkQ, Prod.fst_add, Prod.snd_add, add_zero]; ring

/-- **The sup is attained on the boundary**: some `r ∈ ∂Ω`, `r ≤ p`, maximises the proper time
over `cl Ω ∩ J⁻(p)`. -/
theorem exists_isMax_cosmoPast (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    ∃ r, r ∈ frontier (omegaPlus Λ) ∧ (minkowski d).le ⊤ r p ∧
      ∀ q ∈ cosmoPast Λ p, segTime q p ≤ segTime r p := by
  have hne : (cosmoPast Λ p).Nonempty :=
    ⟨p, subset_closure hp, (minkowski d).le_refl (show p ∈ (⊤ : Opens (Minkowski d)) from trivial)⟩
  obtain ⟨r, hr, hmax⟩ :=
    (isCompact_cosmoPast h p).exists_isMaxOn hne (continuous_segTime_left p).continuousOn
  have hmax' : ∀ q ∈ cosmoPast Λ p, segTime q p ≤ segTime r p := fun q hq => isMaxOn_iff.1 hmax q hq
  refine ⟨r, ?_, hr.2, hmax'⟩
  rw [h.regular.2.frontier_eq]
  refine ⟨hr.1, fun hrΩ => ?_⟩
  obtain ⟨t, ht, ht0⟩ := ((((tendsto_sub_time r).mono_left nhdsWithin_le_nhds).eventually
    (h.regular.2.mem_nhds hrΩ)).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have ht0 : (0 : ℝ) < t := ht0
  have hz := le_top_iff_minkQ.1 hr.2
  have he : p - (r - ((t, 0) : Minkowski d)) = (p - r) + ((t, 0) : Minkowski d) := by abel
  have hmem : r - ((t, 0) : Minkowski d) ∈ cosmoPast Λ p := by
    refine ⟨subset_closure ht, le_top_iff_minkQ.2 ?_⟩
    rw [he]
    exact isFutureCausal_add hz ⟨ht0.le, by simp [minkQ, sq_nonneg]⟩
  have hle := hmax' _ hmem
  unfold segTime at hle
  rw [he, neg_minkQ_add_time] at hle
  have hlt : -minkQ (p - r) < -minkQ (p - r) + 2 * t * (p - r).1 + t ^ 2 := by
    nlinarith [hz.1]
  exact absurd hle (not_le.2 (Real.sqrt_lt_sqrt (by linarith [hz.2]) hlt))

open scoped Classical in
/-- **The point `r(p) ∈ ∂Ω`** realising `T(p)` (Bonsante's retraction; Barbot's `π(p)`). -/
noncomputable def cosmoRetract (Λ : Set (PenroseSphere d × ℝ)) (p : Minkowski d) : Minkowski d :=
  if h : ∃ r, r ∈ frontier (omegaPlus Λ) ∧ (minkowski d).le ⊤ r p ∧
      ∀ q ∈ cosmoPast Λ p, segTime q p ≤ segTime r p then h.choose else p

theorem cosmoRetract_spec (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    cosmoRetract Λ p ∈ frontier (omegaPlus Λ) ∧ (minkowski d).le ⊤ (cosmoRetract Λ p) p ∧
      ∀ q ∈ cosmoPast Λ p, segTime q p ≤ segTime (cosmoRetract Λ p) p := by
  have hex := exists_isMax_cosmoPast h hp
  rw [cosmoRetract, dif_pos hex]
  exact hex.choose_spec

/-- **The sup is a maximum**, attained at `r(p)`. -/
theorem isGreatest_cosmoTimes (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    IsGreatest (cosmoTimes Λ p) (segTime (cosmoRetract Λ p) p) := by
  obtain ⟨hf, hle, hmax⟩ := cosmoRetract_spec h hp
  refine ⟨⟨_, ⟨hf, hle⟩, rfl⟩, ?_⟩
  rintro x ⟨q, ⟨hqf, hqle⟩, rfl⟩
  exact hmax q ⟨frontier_subset_closure hqf, hqle⟩

/-- **The proper times from the boundary are uniformly bounded** (l.1050–1051), under two
directions. -/
theorem bddAbove_cosmoTimes (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    BddAbove (cosmoTimes Λ p) :=
  (isGreatest_cosmoTimes h hp).bddAbove

theorem cosmoTime_eq_segTime (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    cosmoTime Λ p = segTime (cosmoRetract Λ p) p :=
  (isGreatest_cosmoTimes h hp).csSup_eq

/-- Every point of `cl Ω ∩ J⁻(p)` gives a proper time at most `T(p)`: `T` is also the sup over
`cl Ω`, not only over `∂Ω`. -/
theorem segTime_le_cosmoTime (h : CosmoRegular Λ) {p q : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hq : q ∈ cosmoPast Λ p) : segTime q p ≤ cosmoTime Λ p := by
  rw [cosmoTime_eq_segTime h hp]; exact (cosmoRetract_spec h hp).2.2 q hq

theorem cosmoTime_eq_sSup_cosmoPast (h : CosmoRegular Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) :
    cosmoTime Λ p = sSup ((fun q => segTime q p) '' cosmoPast Λ p) := by
  have hG : IsGreatest ((fun q => segTime q p) '' cosmoPast Λ p) (cosmoTime Λ p) := by
    refine ⟨⟨cosmoRetract Λ p, ⟨frontier_subset_closure (cosmoRetract_spec h hp).1,
      (cosmoRetract_spec h hp).2.1⟩, (cosmoTime_eq_segTime h hp).symm⟩, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    exact segTime_le_cosmoTime h hp hq
  exact hG.csSup_eq.symm

/-- **`T` is positive on `Ω`.** -/
theorem cosmoTime_pos (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    0 < cosmoTime Λ p := by
  obtain ⟨t, ht, ht0⟩ := ((((tendsto_sub_time p).mono_left nhdsWithin_le_nhds).eventually
    (h.regular.2.mem_nhds hp)).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have ht0 : (0 : ℝ) < t := ht0
  have he : p - (p - ((t, 0) : Minkowski d)) = ((t, 0) : Minkowski d) := by abel
  have hmem : p - ((t, 0) : Minkowski d) ∈ cosmoPast Λ p :=
    ⟨subset_closure ht, le_top_iff_minkQ.2 (by rw [he]; exact ⟨ht0.le, by simp [minkQ, sq_nonneg]⟩)⟩
  have h1 := segTime_le_cosmoTime h hp hmem
  have h2 : segTime (p - ((t, 0) : Minkowski d)) p = t := by
    rw [segTime, he]; simp [minkQ, Real.sqrt_sq ht0.le]
  linarith

/-- The basic facts at `r(p)`: `p − r(p)` is future timelike and `−|p − r(p)|² = T(p)²`. -/
theorem cosmoRetract_facts (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    IsFutureTimelike (p - cosmoRetract Λ p) ∧ -minkQ (p - cosmoRetract Λ p) = cosmoTime Λ p ^ 2 := by
  have hT := cosmoTime_pos h hp
  have hle := (cosmoRetract_spec h hp).2.1
  have hsq : -minkQ (p - cosmoRetract Λ p) = cosmoTime Λ p ^ 2 := by
    rw [cosmoTime_eq_segTime h hp, sq_segTime hle]
  have hc := le_top_iff_minkQ.1 hle
  refine ⟨⟨lt_of_le_of_ne hc.1 fun h0 => ?_, by nlinarith⟩, hsq⟩
  have := minkQ_nonneg_of_fst_eq_zero h0.symm
  nlinarith

/-- **Uniqueness of `r(p)`** (l.1053–1055; Bonsante Prop 4.3): a point of `cl Ω ∩ J⁻(p)`
realising `T(p)` is `r(p)` — strict concavity of the proper time on the future cone. -/
theorem eq_cosmoRetract (h : CosmoRegular Λ) {p q : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hq : q ∈ cosmoPast Λ p) (hqT : segTime q p = cosmoTime Λ p) : q = cosmoRetract Λ p := by
  obtain ⟨hrf, hrp, hmax⟩ := cosmoRetract_spec h hp
  obtain ⟨ht₂, hq₂⟩ := cosmoRetract_facts h hp
  have hT := cosmoTime_pos h hp
  set r := cosmoRetract Λ p
  set T := cosmoTime Λ p
  by_contra hne
  have hq₁ : -minkQ (p - q) = T ^ 2 := by rw [← sq_segTime hq.2, hqT]
  have hc₁ := le_top_iff_minkQ.1 hq.2
  have ht₁ : IsFutureTimelike (p - q) := by
    refine ⟨lt_of_le_of_ne hc₁.1 fun h0 => ?_, by nlinarith⟩
    have := minkQ_nonneg_of_fst_eq_zero h0.symm
    nlinarith
  have hne' : p - q ≠ p - r := fun he => hne (sub_right_injective he)
  have hsp := minkQ_sub_pos_of_ne ht₁ ht₂ (by linarith) hne'
  have hm : (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • r ∈ cosmoPast Λ p := by
    refine ⟨(convex_omegaPlus Λ).closure hq.1 (frontier_subset_closure hrf) (by norm_num)
      (by norm_num) (by norm_num), le_top_iff_minkQ.2 ?_⟩
    have he : p - ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • r) =
        (1 / 2 : ℝ) • (p - q) + (1 / 2 : ℝ) • (p - r) := by module
    rw [he]
    exact isFutureCausal_add (isFutureCausal_smul (by norm_num) hc₁)
      (isFutureCausal_smul (by norm_num) ht₂.isFutureCausal)
  have hle := hmax _ hm
  have he : p - ((1 / 2 : ℝ) • q + (1 / 2 : ℝ) • r) =
      (1 / 2 : ℝ) • (p - q) + (1 / 2 : ℝ) • (p - r) := by module
  have hsub := mQ_sub (p - q) (p - r)
  have hadd := mQ_add ((1 / 2 : ℝ) • (p - q)) ((1 / 2 : ℝ) • (p - r))
  rw [minkQ_smul, minkQ_smul, mB_smul_left, mB_smul_right] at hadd
  unfold segTime at hle
  rw [he] at hle
  have hTr : segTime r p = T := (cosmoTime_eq_segTime h hp).symm
  unfold segTime at hTr
  rw [hTr] at hle
  have hlt : T ^ 2 < -minkQ ((1 / 2 : ℝ) • (p - q) + (1 / 2 : ℝ) • (p - r)) := by
    rw [hadd]; nlinarith
  have := (Real.lt_sqrt hT.le).2 hlt
  linarith

/-- **`r(p)` is unique in `∂Ω`** (l.1053): the only boundary point realising the sup. -/
theorem eq_cosmoRetract_of_frontier (h : CosmoRegular Λ) {p q : Minkowski d}
    (hp : p ∈ omegaPlus Λ) (hq : q ∈ frontier (omegaPlus Λ)) (hqp : (minkowski d).le ⊤ q p)
    (hqT : segTime q p = cosmoTime Λ p) : q = cosmoRetract Λ p :=
  eq_cosmoRetract h hp ⟨frontier_subset_closure hq, hqp⟩ hqT

/-- **The support property**: the spacelike hyperplane through `r(p)` orthogonal to `p − r(p)`
supports `cl Ω` — `⟨p − r(p) | q − r(p)⟩ ≤ 0` for every `q ∈ cl Ω` (first-order optimality of
the maximum). -/
theorem minkB_cosmoRetract_le (h : CosmoRegular Λ) {p q : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hq : q ∈ closure (omegaPlus Λ)) :
    minkB (p - cosmoRetract Λ p) (q - cosmoRetract Λ p) ≤ 0 := by
  obtain ⟨hrf, hrp, hmax⟩ := cosmoRetract_spec h hp
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp
  set r := cosmoRetract Λ p
  set z := p - r
  set y := q - r
  by_contra hpos
  push Not at hpos
  have ho : IsOpen {v : Minkowski d | IsFutureTimelike v} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_minkQ continuous_const)
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsFutureTimelike (z - ε • y) := by
    have hc : Continuous fun ε : ℝ => z - ε • y := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, sub_zero] at this
    exact (this.eventually (ho.mem_nhds hzt)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 2 * minkB z y - ε * minkQ y := by
    have hc : Continuous fun ε : ℝ => 2 * minkB z y - ε * minkQ y := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, sub_zero] at this
    exact (this.eventually (lt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨⟨he1, he2⟩, he3⟩, he0⟩ :=
    (((h1.and h2).and h3).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have he0 : (0 : ℝ) < ε := he0
  have hrε : r + ε • y ∈ closure (omegaPlus Λ) :=
    (convex_omegaPlus Λ).closure.add_smul_sub_mem (frontier_subset_closure hrf) hq
      ⟨he0.le, he3.le⟩
  have he : p - (r + ε • y) = z - ε • y := by simp only [z]; abel
  have hmem : r + ε • y ∈ cosmoPast Λ p :=
    ⟨hrε, le_top_iff_minkQ.2 (by rw [he]; exact he1.isFutureCausal)⟩
  have hle := hmax _ hmem
  unfold segTime at hle
  rw [he, mQ_sub, mB_smul_right, minkQ_smul] at hle
  have hlt : -minkQ z < -(minkQ z - 2 * (ε * minkB z y) + ε ^ 2 * minkQ y) := by nlinarith
  exact absurd hle (not_le.2 (Real.sqrt_lt_sqrt (by change 0 ≤ -minkQ z; rw [hzq]; positivity) hlt))

/-- **The supporting bound** (`T` is concave with supergradient `−n(p)`):
`T(p) T(p') ≤ T(p)² − ⟨p − r(p) | p' − p⟩` on `Ω`. -/
theorem cosmoTime_mul_le (h : CosmoRegular Λ) {p p' : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hp' : p' ∈ omegaPlus Λ) :
    cosmoTime Λ p * cosmoTime Λ p' ≤
      cosmoTime Λ p ^ 2 - minkB (p - cosmoRetract Λ p) (p' - p) := by
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp
  obtain ⟨hzt', hzq'⟩ := cosmoRetract_facts h hp'
  have hsupp := minkB_cosmoRetract_le h hp (frontier_subset_closure (cosmoRetract_spec h hp').1)
  have hcs := sqrt_mul_sqrt_le_neg_minkB hzt.isFutureCausal hzt'.isFutureCausal
  have hT := (cosmoTime_pos h hp).le
  have hT' := (cosmoTime_pos h hp').le
  rw [hzq, hzq', Real.sqrt_sq hT, Real.sqrt_sq hT'] at hcs
  set r := cosmoRetract Λ p
  set r' := cosmoRetract Λ p'
  have he : p' - r' = (p' - p) + (p - r) - (r' - r) := by abel
  rw [he, mB_sub_right, mB_add_right, ← minkQ_eq_minkB] at hcs
  linarith

/-- **`T` is concave on `Ω`** (Bonsante; Barbot's "C¹-convex", l.1059, read for the function:
its superlevel sets `{T ≥ t}` are convex). From the reverse triangle inequality. -/
theorem concaveOn_cosmoTime (h : CosmoRegular Λ) : ConcaveOn ℝ (omegaPlus Λ) (cosmoTime Λ) := by
  refine ⟨convex_omegaPlus Λ, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨hrx, hrxp, -⟩ := cosmoRetract_spec h hx
  obtain ⟨hry, hryp, -⟩ := cosmoRetract_spec h hy
  have hzx := le_top_iff_minkQ.1 hrxp
  have hzy := le_top_iff_minkQ.1 hryp
  have hpm : a • x + b • y ∈ omegaPlus Λ := convex_omegaPlus Λ hx hy ha hb hab
  have he : a • x + b • y - (a • cosmoRetract Λ x + b • cosmoRetract Λ y) =
      a • (x - cosmoRetract Λ x) + b • (y - cosmoRetract Λ y) := by module
  have hm : a • cosmoRetract Λ x + b • cosmoRetract Λ y ∈ cosmoPast Λ (a • x + b • y) := by
    refine ⟨(convex_omegaPlus Λ).closure (frontier_subset_closure hrx)
      (frontier_subset_closure hry) ha hb hab, le_top_iff_minkQ.2 ?_⟩
    rw [he]
    exact isFutureCausal_add (isFutureCausal_smul ha hzx) (isFutureCausal_smul hb hzy)
  have h1 := segTime_le_cosmoTime h hpm hm
  have h2 := sqrt_neg_minkQ_add_le (isFutureCausal_smul ha hzx) (isFutureCausal_smul hb hzy)
  rw [sqrt_neg_minkQ_smul ha, sqrt_neg_minkQ_smul hb] at h2
  rw [cosmoTime_eq_segTime h hx, cosmoTime_eq_segTime h hy, smul_eq_mul, smul_eq_mul]
  unfold segTime at h1 ⊢
  rw [he] at h1
  linarith

/-- **`T` is continuous on `Ω`** (indeed locally Lipschitz), being concave and finite on an open
convex set of a finite-dimensional space. -/
theorem continuousOn_cosmoTime (h : CosmoRegular Λ) :
    ContinuousOn (cosmoTime Λ) (omegaPlus Λ) :=
  (concaveOn_cosmoTime h).continuousOn h.regular.2

theorem locallyLipschitzOn_cosmoTime (h : CosmoRegular Λ) :
    LocallyLipschitzOn (omegaPlus Λ) (cosmoTime Λ) :=
  (concaveOn_cosmoTime h).locallyLipschitzOn h.regular.2

/-- **`T` is strictly increasing along the causal relation** (a time function on `Ω`). -/
theorem cosmoTime_lt_of_le (h : CosmoRegular Λ) {p q : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hpq : (minkowski d).le ⊤ p q) (hne : p ≠ q) : cosmoTime Λ p < cosmoTime Λ q := by
  have hq : q ∈ omegaPlus Λ := Jplus_omegaPlus_subset Λ ⟨p, hp, hpq⟩
  obtain ⟨hrf, hrp, -⟩ := cosmoRetract_spec h hp
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp
  have hy := le_top_iff_minkQ.1 hpq
  have hy0 : q - p ≠ 0 := sub_ne_zero.2 hne.symm
  have he : q - cosmoRetract Λ p = (p - cosmoRetract Λ p) + (q - p) := by abel
  have hqr : IsFutureCausal (q - cosmoRetract Λ p) := by
    rw [he]; exact isFutureCausal_add hzt.isFutureCausal hy
  have hmem : cosmoRetract Λ p ∈ cosmoPast Λ q :=
    ⟨frontier_subset_closure hrf, le_top_iff_minkQ.2 hqr⟩
  have h1 := segTime_le_cosmoTime h hq hmem
  have hB := minkB_neg_of_isFutureTimelike hzt hy hy0
  unfold segTime at h1
  rw [he, mQ_add] at h1
  have hT := cosmoTime_pos h hp
  have hlt : cosmoTime Λ p ^ 2 < -(minkQ (p - cosmoRetract Λ p) +
      2 * minkB (p - cosmoRetract Λ p) (q - p) + minkQ (q - p)) := by nlinarith [hy.2]
  have := (Real.lt_sqrt hT.le).2 hlt
  linarith

theorem cosmoTime_le_of_le (h : CosmoRegular Λ) {p q : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (hpq : (minkowski d).le ⊤ p q) : cosmoTime Λ p ≤ cosmoTime Λ q := by
  rcases eq_or_ne p q with rfl | hne
  · exact le_rfl
  · exact (cosmoTime_lt_of_le h hp hpq hne).le

/-- The same along `≤_Ω`: by `le_iff_of_convex`, it is the cone relation. -/
theorem cosmoTime_lt_of_le_opens (h : CosmoRegular Λ) {p q : Minkowski d}
    (hpq : (minkowski d).le h.regular.opens p q) (hne : p ≠ q) :
    cosmoTime Λ p < cosmoTime Λ q :=
  cosmoTime_lt_of_le h ((minkowski d).le_mem_left hpq) ((minkowski d).le_mono le_top hpq) hne

/-- **The bound by one null plane** `w ∈ Λ`:
`κ T(p)² ≤ 2 D(p) (s_w − ⟨v_w | p⟩)` with `κ = 2 − ‖u₁ + u₂‖`, `D` the two-direction bound. -/
theorem cosmoTime_sq_le (h : CosmoRegular Λ) {w₁ w₂ w : PenroseSphere d × ℝ} (hw₁ : w₁ ∈ Λ)
    (hw₂ : w₂ ∈ Λ) (hw : w ∈ Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    (2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖) * cosmoTime Λ p ^ 2 ≤
      2 * ((w₁.2 - minkB (nullVec w₁.1) p) + (w₂.2 - minkB (nullVec w₂.1) p)) *
        (w.2 - minkB (nullVec w.1) p) := by
  obtain ⟨hrf, hrp, -⟩ := cosmoRetract_spec h hp
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp
  set r := cosmoRetract Λ p
  have hb := fst_sub_le_of_mem_closure hw₁ hw₂ (frontier_subset_closure hrf) hrp
  have hw' := closure_omegaPlus_subset (frontier_subset_closure hrf) w hw
  have hκ : 0 ≤ 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖ :=
    sub_nonneg.2 (norm_add_penroseSphere_le _ _)
  have hz := isFutureCausal_iff_norm_le.1 hzt.isFutureCausal
  have hi : inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) (p.2 - r.2) ≤ ‖p.2 - r.2‖ := by
    have := real_inner_le_norm (w.1 : EuclideanSpace ℝ (Fin d)) (p.2 - r.2)
    rwa [norm_penroseSphere, one_mul] at this
  simp only [minkB_nullVec] at hw' hb ⊢
  rw [inner_sub_right] at hi
  simp only [Prod.fst_sub, Prod.snd_sub] at hz hb
  rw [← hzq]
  simp only [minkQ, Prod.fst_sub, Prod.snd_sub]
  have hn := norm_nonneg (p.2 - r.2)
  -- `δ := s_w − ⟨v_w | p⟩ ≥ (p − r)₀ − ⟨u, p₂ − r₂⟩ ≥ 0`
  have hδ : (p.1 - r.1) - (inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2 -
      inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) r.2) ≤
      w.2 - (-p.1 + inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2) := by linarith
  have hδ0 : 0 ≤ (p.1 - r.1) - (inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2 -
      inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) r.2) := by linarith
  have hT2 : -(-(p.1 - r.1) ^ 2 + ‖p.2 - r.2‖ ^ 2) ≤ 2 * (p.1 - r.1) *
      ((p.1 - r.1) - (inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2 -
        inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) r.2)) := by
    nlinarith [sq_nonneg (p.1 - r.1 - ‖p.2 - r.2‖)]
  have hz0 : 0 ≤ p.1 - r.1 := hn.trans hz
  calc (2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖) * -(-(p.1 - r.1) ^ 2 + ‖p.2 - r.2‖ ^ 2)
      ≤ (2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖) * (2 * (p.1 - r.1) *
        ((p.1 - r.1) - (inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2 -
          inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) r.2))) := mul_le_mul_of_nonneg_left hT2 hκ
    _ = 2 * ((2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖) * (p.1 - r.1)) *
        ((p.1 - r.1) - (inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) p.2 -
          inner ℝ (w.1 : EuclideanSpace ℝ (Fin d)) r.2)) := by ring
    _ ≤ _ := by
      apply mul_le_mul (by linarith) hδ hδ0
      have := mul_nonneg hκ hz0
      linarith

/-- **`T → 0` at the boundary** (Bonsante): for `q ∈ ∂Ω`, `T(p) → 0` as `p → q` in `Ω`. -/
theorem tendsto_cosmoTime_frontier (h : CosmoRegular Λ) {q : Minkowski d}
    (hq : q ∈ frontier (omegaPlus Λ)) :
    Tendsto (cosmoTime Λ) (𝓝[omegaPlus Λ] q) (𝓝 0) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  have hqΩ : q ∉ omegaPlus Λ := by rw [h.regular.2.frontier_eq] at hq; exact hq.2
  obtain ⟨w, hw, hwq⟩ : ∃ w ∈ Λ, w.2 ≤ minkB (nullVec w.1) q := by
    by_contra hc
    push Not at hc
    exact hqΩ (mem_omegaPlus.2 hc)
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  set D : Minkowski d → ℝ := fun p =>
    (w₁.2 - minkB (nullVec w₁.1) p) + (w₂.2 - minkB (nullVec w₂.1) p)
  set g : Minkowski d → ℝ := fun p => √(2 * |D p| * max (w.2 - minkB (nullVec w.1) p) 0 / κ)
  have hgc : Continuous g := by
    have h1 := continuous_minkB_nullVec (d := d) w₁.1
    have h2 := continuous_minkB_nullVec (d := d) w₂.1
    have h3 := continuous_minkB_nullVec (d := d) w.1
    simp only [g, D]
    fun_prop
  have hgq : g q = 0 := by
    simp only [g, max_eq_right (sub_nonpos.2 hwq), mul_zero, zero_div, Real.sqrt_zero]
  refine squeeze_zero' (eventually_nhdsWithin_of_forall fun p hp => (cosmoTime_pos h hp).le)
    (eventually_nhdsWithin_of_forall fun p hp => ?_)
    (by rw [← hgq]; exact hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hb := cosmoTime_sq_le h hw₁ hw₂ hw hp
  have hδ : 0 < w.2 - minkB (nullVec w.1) p := sub_pos.2 (mem_omegaPlus.1 hp w hw)
  have hD : D p ≤ |D p| := le_abs_self _
  simp only [g]
  rw [max_eq_left hδ.le]
  refine (Real.le_sqrt (cosmoTime_pos h hp).le (by positivity)).2 ?_
  rw [le_div_iff₀ hκ]
  have : 2 * D p * (w.2 - minkB (nullVec w.1) p) ≤ 2 * |D p| * (w.2 - minkB (nullVec w.1) p) := by
    have := mul_le_mul_of_nonneg_right hD hδ.le; linarith
  simp only [D] at this hb ⊢
  linarith

/-- **Growth along future causal rays**: `T(p + s v)² ≥ T(p)² − 2s⟨p − r(p) | v⟩ − s²|v|²`. -/
theorem cosmoTime_sq_add_smul_ge (h : CosmoRegular Λ) {p v : Minkowski d}
    (hp : p ∈ omegaPlus Λ) (hv : IsFutureCausal v) {s : ℝ} (hs : 0 ≤ s) :
    cosmoTime Λ p ^ 2 - 2 * s * minkB (p - cosmoRetract Λ p) v - s ^ 2 * minkQ v ≤
      cosmoTime Λ (p + s • v) ^ 2 := by
  have hps : p + s • v ∈ omegaPlus Λ := add_smul_mem_omegaPlus hp hv hs
  obtain ⟨hrf, -, -⟩ := cosmoRetract_spec h hp
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp
  have he : p + s • v - cosmoRetract Λ p = (p - cosmoRetract Λ p) + s • v := by abel
  have hc : IsFutureCausal (p + s • v - cosmoRetract Λ p) := by
    rw [he]; exact isFutureCausal_add hzt.isFutureCausal (isFutureCausal_smul hs hv)
  have hmem : cosmoRetract Λ p ∈ cosmoPast Λ (p + s • v) :=
    ⟨frontier_subset_closure hrf, le_top_iff_minkQ.2 hc⟩
  have h1 := segTime_le_cosmoTime h hps hmem
  have h2 := sq_segTime (le_top_iff_minkQ.2 hc)
  have h3 : segTime (cosmoRetract Λ p) (p + s • v) ^ 2 ≤ cosmoTime Λ (p + s • v) ^ 2 :=
    pow_le_pow_left₀ (segTime_nonneg _ _) h1 2
  rw [h2, he, mQ_add, mB_smul_right, minkQ_smul] at h3
  linarith

/-- **`T → ∞` along every future causal ray** from a point of `Ω` (future completeness). -/
theorem tendsto_cosmoTime_add_smul (h : CosmoRegular Λ) {p v : Minkowski d}
    (hp : p ∈ omegaPlus Λ) (hv : IsFutureCausal v) (hv0 : v ≠ 0) :
    Tendsto (fun s : ℝ => cosmoTime Λ (p + s • v)) atTop atTop := by
  obtain ⟨hzt, -⟩ := cosmoRetract_facts h hp
  have hB := minkB_neg_of_isFutureTimelike hzt hv hv0
  set c := -minkB (p - cosmoRetract Λ p) v
  have hc : 0 < c := by simp only [c]; linarith
  have hlim : Tendsto (fun s : ℝ => √(2 * c * s)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with s hs
  have h1 := cosmoTime_sq_add_smul_ge h hp hv hs
  have hps : p + s • v ∈ omegaPlus Λ := add_smul_mem_omegaPlus hp hv hs
  refine Real.sqrt_le_iff.2 ⟨(cosmoTime_pos h hps).le, ?_⟩
  have := sq_nonneg (cosmoTime Λ p)
  have := mul_nonneg (sq_nonneg s) (neg_nonneg.2 hv.2)
  simp only [c] at *
  nlinarith

/-- Vertically, `T(p + (s, 0)) ≥ s`. -/
theorem le_cosmoTime_add_time (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ)
    {s : ℝ} (hs : 0 ≤ s) : s ≤ cosmoTime Λ (p + ((s, 0) : Minkowski d)) := by
  have hv : IsFutureCausal ((1, 0) : Minkowski d) := ⟨zero_le_one, by simp [minkQ]⟩
  have h1 := cosmoTime_sq_add_smul_ge h hp hv hs
  have he : s • ((1, 0) : Minkowski d) = ((s, 0) : Minkowski d) := by simp
  rw [he] at h1
  obtain ⟨hzt, -⟩ := cosmoRetract_facts h hp
  have hps : p + ((s, 0) : Minkowski d) ∈ omegaPlus Λ := by
    have := add_smul_mem_omegaPlus hp hv hs; rwa [he] at this
  have hT := (cosmoTime_pos h hps).le
  have hB : minkB (p - cosmoRetract Λ p) ((1, 0) : Minkowski d) = -(p - cosmoRetract Λ p).1 := by
    simp [minkB]
  have hQ : minkQ ((1, 0) : Minkowski d) = -1 := by simp [minkQ]
  rw [hB, hQ] at h1
  nlinarith [hzt.1, sq_nonneg (cosmoTime Λ p)]

/-! ### The Gauss map and the normal flow -/

/-- **The Gauss map** `n(p) = (p − r(p)) / T(p)` (l.1062–1066), a future unit timelike vector. -/
noncomputable def gaussMap (Λ : Set (PenroseSphere d × ℝ)) (p : Minkowski d) : Minkowski d :=
  (cosmoTime Λ p)⁻¹ • (p - cosmoRetract Λ p)

theorem smul_gaussMap (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    cosmoTime Λ p • gaussMap Λ p = p - cosmoRetract Λ p := by
  rw [gaussMap, smul_smul, mul_inv_cancel₀ (cosmoTime_pos h hp).ne', one_smul]

theorem cosmoRetract_add_smul_gaussMap (h : CosmoRegular Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) : cosmoRetract Λ p + cosmoTime Λ p • gaussMap Λ p = p := by
  rw [smul_gaussMap h hp]; abel

/-- `|n(p)|² = −1`. -/
theorem minkQ_gaussMap (h : CosmoRegular Λ) {p : Minkowski d} (hp : p ∈ omegaPlus Λ) :
    minkQ (gaussMap Λ p) = -1 := by
  obtain ⟨-, hzq⟩ := cosmoRetract_facts h hp
  have hT := (cosmoTime_pos h hp).ne'
  rw [gaussMap, minkQ_smul]
  field_simp
  linarith

/-- `n(p)` is future timelike. -/
theorem isFutureTimelike_gaussMap (h : CosmoRegular Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) : IsFutureTimelike (gaussMap Λ p) := by
  obtain ⟨hzt, -⟩ := cosmoRetract_facts h hp
  refine ⟨?_, by rw [minkQ_gaussMap h hp]; norm_num⟩
  rw [gaussMap, Prod.smul_fst, smul_eq_mul]
  exact mul_pos (inv_pos.2 (cosmoTime_pos h hp)) hzt.1

/-- **The normal flow** (l.1067–1070, Bonsante Cor 4.5): `T(p + ε n(p)) = T(p) + ε`, with the
same retraction and the same normal, for `ε ≥ 0`. -/
theorem cosmoTime_add_smul_gaussMap (h : CosmoRegular Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) {ε : ℝ} (hε : 0 ≤ ε) :
    cosmoTime Λ (p + ε • gaussMap Λ p) = cosmoTime Λ p + ε ∧
      cosmoRetract Λ (p + ε • gaussMap Λ p) = cosmoRetract Λ p ∧
        gaussMap Λ (p + ε • gaussMap Λ p) = gaussMap Λ p := by
  have hn := isFutureTimelike_gaussMap h hp
  have hT := cosmoTime_pos h hp
  set T := cosmoTime Λ p
  set n := gaussMap Λ p
  set r := cosmoRetract Λ p
  set p' := p + ε • n
  have hp' : p' ∈ omegaPlus Λ := add_smul_mem_omegaPlus hp hn.isFutureCausal hε
  have hzn : p - r = T • n := (smul_gaussMap h hp).symm
  have he : p' - r = (T + ε) • n := by simp only [p']; rw [add_smul, ← hzn]; abel
  have hc : IsFutureCausal (p' - r) := by
    rw [he]; exact isFutureCausal_smul (by linarith) hn.isFutureCausal
  have hmem : r ∈ cosmoPast Λ p' :=
    ⟨frontier_subset_closure (cosmoRetract_spec h hp).1, le_top_iff_minkQ.2 hc⟩
  have hseg : segTime r p' = T + ε := by
    rw [segTime, he, sqrt_neg_minkQ_smul (by linarith), minkQ_gaussMap h hp]; simp
  have hlow : T + ε ≤ cosmoTime Λ p' := hseg ▸ segTime_le_cosmoTime h hp' hmem
  have hup := cosmoTime_mul_le h hp hp'
  have hpp : p' - p = ε • n := by simp only [p']; abel
  rw [hpp, hzn, mB_smul_left, mB_smul_right, ← minkQ_eq_minkB, minkQ_gaussMap h hp] at hup
  have hT' : cosmoTime Λ p' = T + ε := by
    refine le_antisymm ?_ hlow
    by_contra hlt
    push Not at hlt
    nlinarith
  have hr' : cosmoRetract Λ p' = r := (eq_cosmoRetract h hp' hmem (by rw [hseg, hT'])).symm
  refine ⟨hT', hr', ?_⟩
  rw [gaussMap, hT', hr', he, smul_smul, inv_mul_cancel₀ (by linarith), one_smul]

/-! ### The level sets `S_t = T⁻¹(t)` -/

/-- **The level set** `S_t = T⁻¹(t) ⊆ Ω`. -/
def cosmoLevel (Λ : Set (PenroseSphere d × ℝ)) (t : ℝ) : Set (Minkowski d) :=
  {p | p ∈ omegaPlus Λ ∧ cosmoTime Λ p = t}

theorem cosmoLevel_subset (t : ℝ) : cosmoLevel Λ t ⊆ omegaPlus Λ := fun _ hp => hp.1

/-- **`S_t` is acausal** in `𝐌ⁿ` (Barbot's `|x − y|² > 0`, l.2326, for the level sets). -/
theorem isAcausal_cosmoLevel (h : CosmoRegular Λ) (t : ℝ) :
    (minkowski d).IsAcausal (cosmoLevel Λ t) := fun x hx y hy hxy => by
  by_contra hne
  have := cosmoTime_lt_of_le h hx.1 hxy hne
  rw [hx.2, hy.2] at this
  exact lt_irrefl _ this

/-- The normal flow maps `S_t` into `S_{t+ε}` (`S_{t+ε} = S_t + ε n`, one inclusion). -/
theorem add_smul_gaussMap_mem_cosmoLevel (h : CosmoRegular Λ) {t ε : ℝ} (hε : 0 ≤ ε)
    {p : Minkowski d} (hp : p ∈ cosmoLevel Λ t) :
    p + ε • gaussMap Λ p ∈ cosmoLevel Λ (t + ε) :=
  ⟨add_smul_mem_omegaPlus hp.1 (isFutureTimelike_gaussMap h hp.1).isFutureCausal hε,
    by rw [(cosmoTime_add_smul_gaussMap h hp.1 hε).1, hp.2]⟩

/-- **The normal flow is onto**: every point of `S_{t+ε}` (`0 ≤ ε < t + ε`) is `p + ε n(p)` for
some `p ∈ S_t`, namely `p' − ε n(p')`. -/
theorem exists_add_smul_gaussMap_eq (h : CosmoRegular Λ) {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε)
    {p' : Minkowski d} (hp' : p' ∈ cosmoLevel Λ (t + ε)) :
    ∃ p ∈ cosmoLevel Λ t, p + ε • gaussMap Λ p = p' := by
  rcases hε.eq_or_lt with rfl | hε0
  · exact ⟨p', by simpa using hp', by simp⟩
  have hT' := hp'.2
  set n := gaussMap Λ p'
  set r := cosmoRetract Λ p'
  have hrp : r + (t + ε) • n = p' := by rw [← hT']; exact cosmoRetract_add_smul_gaussMap h hp'.1
  set p := r + t • n
  have hpe : p = p' - ε • n := by rw [← hrp]; simp only [p, add_smul]; abel
  have hne : t + ε ≠ 0 := by positivity
  -- `p` lies on the open segment from `r ∈ cl Ω` to `p' ∈ Ω`
  have hpΩ : p ∈ omegaPlus Λ := by
    have hseg := (convex_omegaPlus Λ).openSegment_closure_interior_subset_interior
      (frontier_subset_closure (cosmoRetract_spec h hp'.1).1)
      (h.regular.2.interior_eq.symm ▸ hp'.1 : p' ∈ interior (omegaPlus Λ))
    rw [h.regular.2.interior_eq] at hseg
    refine hseg ⟨ε / (t + ε), t / (t + ε), by positivity, by positivity,
      by rw [← add_div, add_comm ε t, div_self hne], ?_⟩
    show (ε / (t + ε)) • r + (t / (t + ε)) • p' = r + t • n
    rw [← hrp, smul_add, smul_smul, ← add_assoc, ← add_smul, ← add_div, add_comm ε t,
      div_self hne, one_smul, div_mul_cancel₀ t hne]
  have hpr : p - r = t • n := by simp only [p]; abel
  have hmem : r ∈ cosmoPast Λ p := by
    refine ⟨frontier_subset_closure (cosmoRetract_spec h hp'.1).1, le_top_iff_minkQ.2 ?_⟩
    rw [hpr]
    exact isFutureCausal_smul ht.le (isFutureTimelike_gaussMap h hp'.1).isFutureCausal
  have hseg : segTime r p = t := by
    rw [segTime, hpr, sqrt_neg_minkQ_smul ht.le, minkQ_gaussMap h hp'.1]; simp
  have hlow : t ≤ cosmoTime Λ p := hseg ▸ segTime_le_cosmoTime h hpΩ hmem
  have hup := cosmoTime_mul_le h hp'.1 hpΩ
  have hzn : p' - r = (t + ε) • n := by rw [← hrp]; abel
  have hd : p - p' = (-ε) • n := by rw [hpe, neg_smul]; abel
  rw [hzn, hT', hd, mB_smul_left, mB_smul_right, ← minkQ_eq_minkB, minkQ_gaussMap h hp'.1] at hup
  have hTp : cosmoTime Λ p = t := by
    refine le_antisymm ?_ hlow
    by_contra hlt
    push Not at hlt
    have : 0 < t + ε := by linarith
    nlinarith
  refine ⟨p, ⟨hpΩ, hTp⟩, ?_⟩
  have hr : cosmoRetract Λ p = r := (eq_cosmoRetract h hpΩ hmem (by rw [hseg, hTp])).symm
  have hn : gaussMap Λ p = n := by
    rw [gaussMap, hTp, hr, hpr, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [hn, hpe]; abel

/-- `S_{t+ε} = S_t + ε n` (l.1067–1070), for `t > 0`, `ε ≥ 0`. -/
theorem cosmoLevel_add_eq_image (h : CosmoRegular Λ) {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) :
    cosmoLevel Λ (t + ε) = (fun p => p + ε • gaussMap Λ p) '' cosmoLevel Λ t := by
  ext p'
  refine ⟨fun hp' => ?_, ?_⟩
  · obtain ⟨p, hp, he⟩ := exists_add_smul_gaussMap_eq h ht hε hp'
    exact ⟨p, hp, he⟩
  · rintro ⟨p, hp, rfl⟩
    exact add_smul_gaussMap_mem_cosmoLevel h hε hp

/-- **Every vertical line meets `S_t`** (`t > 0`). -/
theorem exists_mk_mem_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin d)) : ∃ s : ℝ, ((s, x) : Minkowski d) ∈ cosmoLevel Λ t := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  set A : Set ℝ := {s | ((s, x) : Minkowski d) ∈ omegaPlus Λ}
  have hup : ∀ {s s'}, s ∈ A → s ≤ s' → s' ∈ A := fun {s s'} hs hss' =>
    Jplus_omegaPlus_subset Λ ⟨_, hs, minkowski_le_top_iff.2 (by simpa using hss')⟩
  have hinner : ∀ u : PenroseSphere d, inner ℝ (u : EuclideanSpace ℝ (Fin d)) x ≤ ‖x‖ := fun u => by
    have := real_inner_le_norm (u : EuclideanSpace ℝ (Fin d)) x
    rwa [norm_penroseSphere, one_mul] at this
  obtain ⟨C, hC⟩ := omegaPlus_nonempty_iff.1 h.regular.1
  have hAne : A.Nonempty := ⟨‖x‖ - C + 1, mem_omegaPlus.2 fun w hw => by
    rw [minkB_nullVec]; have := hC w hw; have := hinner w.1; simp only; linarith⟩
  have hAbdd : BddBelow A := ⟨inner ℝ (w₁.1 : EuclideanSpace ℝ (Fin d)) x - w₁.2, fun s hs => by
    have := mem_omegaPlus.1 hs w₁ hw₁
    rw [minkB_nullVec] at this; simp only at this; linarith⟩
  set σ := sInf A
  have hcont : Continuous fun s : ℝ => ((s, x) : Minkowski d) := by fun_prop
  have hAopen : IsOpen A := h.regular.2.preimage hcont
  have hσA : σ ∉ A := by
    intro hσ
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hAopen σ hσ
    have : σ - η / 2 ∈ A := hball (by rw [mem_ball, Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
    have := csInf_le hAbdd this
    linarith
  obtain ⟨w, hw, hwσ⟩ : ∃ w ∈ Λ, w.2 ≤ minkB (nullVec w.1) ((σ, x) : Minkowski d) := by
    by_contra hc
    push Not at hc
    exact hσA (mem_omegaPlus.2 hc)
  have hση : ∀ η > 0, σ + η ∈ A := fun η hη => by
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hAne (show σ < σ + η by linarith)
    exact hup ha hlt.le
  -- the bound by the plane `w` near the boundary point `(σ, x)`
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  set D₀ := (w₁.2 - minkB (nullVec w₁.1) ((σ, x) : Minkowski d)) +
    (w₂.2 - minkB (nullVec w₂.1) ((σ, x) : Minkowski d))
  have hlim : Tendsto (fun η : ℝ => 2 * (|D₀| + 2 * η) * η) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun η : ℝ => 2 * (|D₀| + 2 * η) * η := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨η, hηt, hη0⟩ := ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < κ * t ^ 2 by
    positivity))).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hη0 : (0 : ℝ) < η := hη0
  set p₁ : Minkowski d := (σ + η, x)
  have hp₁ : p₁ ∈ omegaPlus Λ := hση η hη0
  have hb := cosmoTime_sq_le h hw₁ hw₂ hw hp₁
  have hB : ∀ u : PenroseSphere d, minkB (nullVec u) p₁ =
      minkB (nullVec u) ((σ, x) : Minkowski d) - η := fun u => by
    simp only [p₁, minkB_nullVec]; ring
  rw [hB, hB, hB] at hb
  have hδ : 0 < w.2 - (minkB (nullVec w.1) ((σ, x) : Minkowski d) - η) :=
    sub_pos.2 (by rw [← hB]; exact mem_omegaPlus.1 hp₁ w hw)
  have hT₁ : cosmoTime Λ p₁ < t := by
    have hD : D₀ + 2 * η ≤ |D₀| + 2 * η := by linarith [le_abs_self D₀]
    have h1 : κ * cosmoTime Λ p₁ ^ 2 ≤ 2 * (|D₀| + 2 * η) * η := by
      refine hb.trans ?_
      have hδη : w.2 - (minkB (nullVec w.1) ((σ, x) : Minkowski d) - η) ≤ η := by linarith
      have hD0 : 0 ≤ |D₀| + 2 * η := by positivity
      calc 2 * (w₁.2 - (minkB (nullVec w₁.1) ((σ, x) : Minkowski d) - η) +
            (w₂.2 - (minkB (nullVec w₂.1) ((σ, x) : Minkowski d) - η))) *
            (w.2 - (minkB (nullVec w.1) ((σ, x) : Minkowski d) - η))
          = 2 * (D₀ + 2 * η) * (w.2 - (minkB (nullVec w.1) ((σ, x) : Minkowski d) - η)) := by
            simp only [D₀]; ring
        _ ≤ 2 * (|D₀| + 2 * η) * (w.2 - (minkB (nullVec w.1) ((σ, x) : Minkowski d) - η)) := by
            have := mul_le_mul_of_nonneg_right hD hδ.le; linarith
        _ ≤ 2 * (|D₀| + 2 * η) * η := by
            have := mul_le_mul_of_nonneg_left hδη hD0; linarith
    have h2 : κ * cosmoTime Λ p₁ ^ 2 < κ * t ^ 2 := h1.trans_lt hηt
    have h3 : cosmoTime Λ p₁ ^ 2 < t ^ 2 := lt_of_mul_lt_mul_left h2 hκ.le
    exact lt_of_pow_lt_pow_left₀ 2 ht.le h3
  -- a high point
  have hT₂ := le_cosmoTime_add_time h hp₁ (s := t + 1) (by linarith)
  have hp₂ : p₁ + ((t + 1, 0) : Minkowski d) = ((σ + η + (t + 1), x) : Minkowski d) := by
    simp only [p₁, Prod.mk_add_mk, add_zero]
  rw [hp₂] at hT₂
  -- the intermediate value theorem on the vertical segment
  have hsub : MapsTo (fun s : ℝ => ((s, x) : Minkowski d)) (Icc (σ + η) (σ + η + (t + 1)))
      (omegaPlus Λ) := fun s hs => hup hp₁ hs.1
  have hc : ContinuousOn (fun s : ℝ => cosmoTime Λ ((s, x) : Minkowski d))
      (Icc (σ + η) (σ + η + (t + 1))) :=
    (continuousOn_cosmoTime h).comp hcont.continuousOn hsub
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc (by linarith) hc ⟨hT₁.le, by linarith⟩
  exact ⟨s, hsub hs, hst⟩

/-- `S_t` meets every vertical line at most once. -/
theorem eq_of_mk_mem_cosmoLevel (h : CosmoRegular Λ) {t s s' : ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hs : ((s, x) : Minkowski d) ∈ cosmoLevel Λ t)
    (hs' : ((s', x) : Minkowski d) ∈ cosmoLevel Λ t) : s = s' := by
  have hac := isAcausal_cosmoLevel h t
  rcases le_total s s' with hle | hle
  · have := hac _ hs _ hs' (minkowski_le_top_iff.2 (by simpa using hle))
    exact congrArg Prod.fst this
  · have := hac _ hs' _ hs (minkowski_le_top_iff.2 (by simpa using hle))
    exact (congrArg Prod.fst this).symm

open scoped Classical in
/-- The function whose graph is `S_t`. -/
noncomputable def cosmoGraph (Λ : Set (PenroseSphere d × ℝ)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if hx : ∃ s : ℝ, ((s, x) : Minkowski d) ∈ cosmoLevel Λ t then hx.choose else 0

theorem mk_cosmoGraph_mem (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin d)) : ((cosmoGraph Λ t x, x) : Minkowski d) ∈ cosmoLevel Λ t := by
  have hx := exists_mk_mem_cosmoLevel h ht x
  rw [cosmoGraph, dif_pos hx]
  exact hx.choose_spec

/-- **`S_t` is an entire graph** over `ℝᵈ` (`t > 0`). -/
theorem cosmoLevel_eq_graph (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    cosmoLevel Λ t = graph (cosmoGraph Λ t) := by
  ext p
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have h1 : ((p.1, p.2) : Minkowski d) ∈ cosmoLevel Λ t := hp
    exact eq_of_mk_mem_cosmoLevel h h1 (mk_cosmoGraph_mem h ht p.2)
  · have h1 := mk_cosmoGraph_mem h ht p.2
    have he : p = (cosmoGraph Λ t p.2, p.2) := Prod.ext (mem_graph.1 hp) rfl
    rw [he]
    exact h1

/-- **`S_t` is the graph of a `1`-Lipschitz function** (achronal and entire). -/
theorem lipschitzWith_cosmoGraph (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    LipschitzWith 1 (cosmoGraph Λ t) :=
  isAchronal_graph_iff.1 (by
    rw [← cosmoLevel_eq_graph h ht]
    exact minkowski_isAchronal_of_isAcausal (isAcausal_cosmoLevel h t))

/-- **`S_t` is closed** in `𝐌ⁿ`. -/
theorem isClosed_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    IsClosed (cosmoLevel Λ t) := by
  rw [cosmoLevel_eq_graph h ht]
  exact isClosed_graph (lipschitzWith_cosmoGraph h ht).continuous

/-- **The slope bound on `S_t`**: if `p, p' ∈ S_t` have `p − r(p)` and `p' − r(p')` of time
component at most `B`, then `|Δt| ≤ √(1 − t²/B²) ‖Δx‖`. -/
theorem abs_fst_sub_le_of_mem_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} {p p' : Minkowski d} (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) {B : ℝ}
    (hB : (p - cosmoRetract Λ p).1 ≤ B) (hB' : (p' - cosmoRetract Λ p').1 ≤ B) :
    |p'.1 - p.1| ≤ √(1 - t ^ 2 / B ^ 2) * ‖p'.2 - p.2‖ := by
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp.1
  obtain ⟨hzt', hzq'⟩ := cosmoRetract_facts h hp'.1
  rw [hp.2] at hzq; rw [hp'.2] at hzq'
  have h1 := cosmoTime_mul_le h hp.1 hp'.1
  have h2 := cosmoTime_mul_le h hp'.1 hp.1
  rw [hp.2, hp'.2] at h1 h2
  have hBpos : 0 < B := hzt.1.trans_le hB
  -- `‖z₂‖ ≤ c z₁` for `z = p − r(p)`, `−|z|² = t²`, `z₁ ≤ B`
  have key : ∀ z : Minkowski d, IsFutureTimelike z → -minkQ z = t ^ 2 → z.1 ≤ B →
      ‖z.2‖ ≤ √(1 - t ^ 2 / B ^ 2) * z.1 := fun z hz hzq hzB => by
    have hz1 := hz.1
    have hsq : ‖z.2‖ ^ 2 ≤ (1 - t ^ 2 / B ^ 2) * z.1 ^ 2 := by
      have : ‖z.2‖ ^ 2 = z.1 ^ 2 - t ^ 2 := by unfold minkQ at hzq; linarith
      rw [this, sub_mul, one_mul, div_mul_eq_mul_div, sub_le_sub_iff_left,
        div_le_iff₀ (by positivity)]
      have : z.1 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hz1.le hzB 2
      nlinarith [sq_nonneg t]
    calc ‖z.2‖ = √(‖z.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √((1 - t ^ 2 / B ^ 2) * z.1 ^ 2) := Real.sqrt_le_sqrt hsq
      _ = √(1 - t ^ 2 / B ^ 2) * z.1 := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hz1.le]
  have k1 := key _ hzt hzq hB
  have k2 := key _ hzt' hzq' hB'
  set c := √(1 - t ^ 2 / B ^ 2)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set z := p - cosmoRetract Λ p
  set z' := p' - cosmoRetract Λ p'
  have hn := norm_nonneg (p'.2 - p.2)
  have i1 : -(inner ℝ z.2 (p'.2 - p.2)) ≤ ‖z.2‖ * ‖p'.2 - p.2‖ := by
    have := real_inner_le_norm z.2 (-(p'.2 - p.2))
    rwa [inner_neg_right, norm_neg] at this
  have i2 : inner ℝ z'.2 (p'.2 - p.2) ≤ ‖z'.2‖ * ‖p'.2 - p.2‖ := real_inner_le_norm _ _
  have hB1 : minkB z (p' - p) ≤ 0 := by nlinarith
  have hB2 : minkB z' (p - p') ≤ 0 := by nlinarith
  simp only [minkB, Prod.fst_sub, Prod.snd_sub] at hB1 hB2
  have hB2' : -(z'.1 * (p.1 - p'.1)) - inner ℝ z'.2 (p'.2 - p.2) ≤ 0 := by
    rw [← neg_sub p'.2 p.2, inner_neg_right] at hB2; linarith
  have e1 : z.1 * (p'.1 - p.1) ≥ -(c * z.1) * ‖p'.2 - p.2‖ := by
    nlinarith [mul_le_mul_of_nonneg_right k1 hn]
  have e2 : z'.1 * (p'.1 - p.1) ≤ (c * z'.1) * ‖p'.2 - p.2‖ := by
    nlinarith [mul_le_mul_of_nonneg_right k2 hn]
  rw [abs_le]
  constructor
  · by_contra hlt; push Not at hlt
    have := mul_lt_mul_of_pos_left hlt hzt.1
    nlinarith
  · by_contra hlt; push Not at hlt
    have := mul_lt_mul_of_pos_left hlt hzt'.1
    nlinarith

/-- **`S_t` is a spacelike Lipschitz hypersurface of `Ω`** (`t > 0`): the three fields of
`InducedLength.IsSpacelikeLipschitzIn Ω S_t`, written out (that module is not importable in this
wave), in the frame `g = 1`, with a slope `c < 1` **depending on the point** (contract item (f)). -/
theorem isSpacelikeLipschitz_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    cosmoLevel Λ t ⊆ omegaPlus Λ ∧
    (∀ p ∈ cosmoLevel Λ t, ∀ q ∈ cosmoLevel Λ t, ¬ (minkowski d).lt h.regular.opens p q) ∧
    ∀ p₀ ∈ cosmoLevel Λ t, ∃ (O : Opens (Minkowski d)) (U : Set (EuclideanSpace ℝ (Fin d)))
      (f : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ≥0), c < 1 ∧ p₀ ∈ O ∧ O ≤ h.regular.opens ∧
        IsOpen U ∧ LipschitzOnWith c f U ∧
        cosmoLevel Λ t ∩ (O : Set (Minkowski d)) =
          (O : Set (Minkowski d)) ∩ {q | q.2 ∈ U ∧ q.1 = f q.2} := by
  refine ⟨cosmoLevel_subset t, fun p hp q hq hlt => ?_, fun p₀ hp₀ => ?_⟩
  · have hv := lt_top_iff_minkQ.1 ((minkowski d).lt_mono le_top hlt)
    have := isAcausal_cosmoLevel h t p hp q hq (le_top_iff_minkQ.2 hv.isFutureCausal)
    have h0 := hv.1
    rw [this, sub_self] at h0
    exact lt_irrefl _ h0
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  set f := cosmoGraph Λ t
  have hf := lipschitzWith_cosmoGraph h ht
  set x₀ := p₀.2
  set U := ball x₀ 1
  set R := |f x₀| + ‖x₀‖ + 1
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  set Bd := (w₁.2 + w₂.2 + 4 * R) / κ
  have hnorm : ∀ x ∈ U, ‖((f x, x) : Minkowski d)‖ ≤ R := fun x hx => by
    have hd : dist x x₀ < 1 := hx
    have h1 : |f x - f x₀| ≤ dist x x₀ := by
      have := hf.dist_le_mul x x₀; rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
    have h2 : ‖x‖ ≤ ‖x₀‖ + dist x x₀ := by
      rw [dist_eq_norm]; linarith [norm_sub_norm_le x x₀]
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]
      linarith [abs_sub_abs_le_abs_sub (f x) (f x₀), norm_nonneg x₀]
    · linarith [abs_nonneg (f x₀)]
  have hzB : ∀ x ∈ U, (((f x, x) : Minkowski d) - cosmoRetract Λ ((f x, x) : Minkowski d)).1 ≤ Bd :=
    fun x hx => by
      have hpx := mk_cosmoGraph_mem h ht x
      obtain ⟨hrf, hrp, -⟩ := cosmoRetract_spec h hpx.1
      have hb := fst_sub_le_of_mem_closure hw₁ hw₂ (frontier_subset_closure hrf) hrp
      have h1 := abs_minkB_nullVec_le_two_mul_norm w₁.1 ((f x, x) : Minkowski d)
      have h2 := abs_minkB_nullVec_le_two_mul_norm w₂.1 ((f x, x) : Minkowski d)
      have h3 := hnorm x hx
      rw [le_div_iff₀ hκ]
      linarith [neg_abs_le (minkB (nullVec w₁.1) ((f x, x) : Minkowski d)),
        neg_abs_le (minkB (nullVec w₂.1) ((f x, x) : Minkowski d))]
  have hp₀e : ((f x₀, x₀) : Minkowski d) = p₀ := by
    have := hp₀; rw [cosmoLevel_eq_graph h ht] at this
    exact Prod.ext (mem_graph.1 this).symm rfl
  have hBpos : 0 < Bd := by
    have := hzB x₀ (mem_ball_self one_pos)
    rw [hp₀e] at this
    exact (cosmoRetract_facts h hp₀.1).1.1.trans_le this
  set c : ℝ≥0 := ⟨√(1 - t ^ 2 / Bd ^ 2), Real.sqrt_nonneg _⟩
  have hc : c < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    show √(1 - t ^ 2 / Bd ^ 2) < 1
    rw [Real.sqrt_lt' one_pos]
    have : 0 < t ^ 2 / Bd ^ 2 := by positivity
    linarith
  set O : Opens (Minkowski d) := ⟨omegaPlus Λ ∩ Prod.snd ⁻¹' U,
    h.regular.2.inter (isOpen_ball.preimage continuous_snd)⟩
  refine ⟨O, U, f, c, hc, ⟨hp₀.1, mem_ball_self one_pos⟩, fun q hq => hq.1, isOpen_ball, ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have := abs_fst_sub_le_of_mem_cosmoLevel h (mk_cosmoGraph_mem h ht y)
      (mk_cosmoGraph_mem h ht x) (hzB y hy) (hzB x hx)
    rw [Real.dist_eq, dist_eq_norm]
    exact this
  · ext q
    constructor
    · rintro ⟨hqS, hqΩ, hqU⟩
      refine ⟨⟨hqΩ, hqU⟩, hqU, ?_⟩
      rw [cosmoLevel_eq_graph h ht] at hqS
      exact hqS
    · rintro ⟨⟨hqΩ, hqU⟩, -, hqf⟩
      refine ⟨?_, hqΩ, hqU⟩
      rw [cosmoLevel_eq_graph h ht]
      exact hqf

/-! ### Curves of `Ω` along which `T` is bounded converge, and extend -/

/-- `J⁺_Ω(x) ≠ {x}` on `Ω = Ω⁺(Λ)`. -/
theorem Jplus_opens_ne_singleton (h : FutureRegular Λ) {x : Minkowski d}
    (hx : x ∈ omegaPlus Λ) : (minkowski d).Jplus h.opens {x} ≠ {x} := by
  intro he
  have hv : IsFutureCausal ((1, 0) : Minkowski d) := ⟨zero_le_one, by simp [minkQ]⟩
  have hy : x + ((1, 0) : Minkowski d) ∈ omegaPlus Λ := by
    simpa using add_smul_mem_omegaPlus hx hv zero_le_one
  have hmem : x + ((1, 0) : Minkowski d) ∈ (minkowski d).Jplus h.opens {x} :=
    ⟨x, rfl, (le_iff_of_convex (V := h.opens) (convex_omegaPlus Λ)).2 ⟨hx, hy, by
      rw [minkowski_le_top_iff]; simp⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this

/-- `J⁻_Ω(x) ≠ {x}` on `Ω = Ω⁺(Λ)` (`Ω` is open). -/
theorem Jminus_opens_ne_singleton (h : FutureRegular Λ) {x : Minkowski d}
    (hx : x ∈ omegaPlus Λ) : (minkowski d).Jminus h.opens {x} ≠ {x} := by
  intro he
  obtain ⟨t, ht, ht0⟩ := ((((tendsto_sub_time x).mono_left nhdsWithin_le_nhds).eventually
    (h.2.mem_nhds hx)).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have ht0 : (0 : ℝ) < t := ht0
  have hmem : x - ((t, 0) : Minkowski d) ∈ (minkowski d).Jminus h.opens {x} :=
    ⟨x, rfl, (le_iff_of_convex (V := h.opens) (convex_omegaPlus Λ)).2 ⟨ht, hx, by
      rw [minkowski_le_top_iff]; simp [ht0.le]⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this
  linarith

/-- In `𝐌ⁿ`, `x ≤ y` gives `dist x y ≤ y₀ − x₀` (sup distance on `ℝ × ℝᵈ`). -/
theorem dist_le_of_le_top {x y : Minkowski d} (h : (minkowski d).le ⊤ x y) :
    dist x y ≤ y.1 - x.1 := by
  have h1 := minkowski_le_top_iff.1 h
  have h0 : 0 ≤ y.1 - x.1 := (norm_nonneg _).trans h1
  rw [Prod.dist_eq, Real.dist_eq, dist_comm, dist_eq_norm]
  exact max_le (by rw [abs_le]; constructor <;> linarith) h1

/-- An interval with supremum `β` contains `]u, β[` for each of its points `u`. -/
theorem Ioo_subset_of_isLUB {J : Set ℝ} (hJc : J.OrdConnected) {β : ℝ} (hβ : IsLUB J β)
    {u : ℝ} (hu : u ∈ J) : Ioo u β ⊆ J := fun z hz => by
  obtain ⟨w, hw, hzw, -⟩ := hβ.exists_between hz.2
  exact hJc.out hu hw ⟨hz.1.le, hzw.le⟩

/-- An interval with infimum `α` contains `]α, u[` for each of its points `u`. -/
theorem Ioo_subset_of_isGLB {J : Set ℝ} (hJc : J.OrdConnected) {α : ℝ} (hα : IsGLB J α)
    {u : ℝ} (hu : u ∈ J) : Ioo α u ⊆ J := fun z hz => by
  obtain ⟨w, hw, -, hwz⟩ := hα.exists_between hz.1
  exact hJc.out hw hu ⟨hwz.le, hz.2.le⟩

/-- **A causal curve whose time is bounded above converges at its upper end** (`𝐌ⁿ` is complete;
the spatial displacement is bounded by the elapsed time). -/
theorem exists_tendsto_of_bddAbove {J : Set ℝ} {γ : ℝ → Minkowski d} {β : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hβ : IsLUB J β) (hβJ : β ∉ J)
    (hbdd : BddAbove ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[<] β) (𝓝 p) := by
  have hlt : ∀ u ∈ J, u < β := fun u hu =>
    lt_of_le_of_ne (hβ.1 hu) fun he => hβJ (he ▸ hu)
  set τ := sSup ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[<] β)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hτ⟩ := exists_lt_of_lt_csSup (hJ.image _) (sub_lt_self τ hε)
    have hsub := Ioo_subset_of_isLUB hJc hβ hu₁
    refine ⟨γ '' Ioo u₁ β, mem_map.2 (mem_of_superset (Ioo_mem_nhdsLT (hlt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo u₁ β, ∀ u' ∈ Ioo u₁ β, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := dist_le_of_le_top (hle u (hsub hu) u' (hsub hu') huu')
        have h2 := minkowski_le_top_iff.1 (hle u₁ hu₁ u (hsub hu) hu.1.le)
        have h3 : (γ u').1 ≤ τ := le_csSup hbdd ⟨u', hsub hu', rfl⟩
        linarith [norm_nonneg ((γ u).2 - (γ u₁).2)]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- **A causal curve whose time is bounded below converges at its lower end.** -/
theorem exists_tendsto_of_bddBelow {J : Set ℝ} {γ : ℝ → Minkowski d} {α : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hα : IsGLB J α) (hαJ : α ∉ J)
    (hbdd : BddBelow ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[>] α) (𝓝 p) := by
  have hgt : ∀ u ∈ J, α < u := fun u hu =>
    lt_of_le_of_ne (hα.1 hu) fun he => hαJ (he ▸ hu)
  set σ := sInf ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[>] α)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hσ⟩ := exists_lt_of_csInf_lt (hJ.image _) (lt_add_of_pos_right σ hε)
    have hsub := Ioo_subset_of_isGLB hJc hα hu₁
    refine ⟨γ '' Ioo α u₁, mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT (hgt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo α u₁, ∀ u' ∈ Ioo α u₁, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := dist_le_of_le_top (hle u (hsub hu) u' (hsub hu') huu')
        have h2 := minkowski_le_top_iff.1 (hle u' (hsub hu') u₁ hu₁ hu'.2.le)
        have h3 : σ ≤ (γ u).1 := csInf_le hbdd ⟨u, hsub hu, rfl⟩
        linarith [norm_nonneg ((γ u₁).2 - (γ u').2)]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- `insert β J` is an interval when `β = sup J`. -/
theorem ordConnected_insert_of_isLUB {J : Set ℝ} (hJc : J.OrdConnected) {β : ℝ}
    (hβ : IsLUB J β) : (insert β J).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hyβ : y ≤ β := by
    rcases hy with rfl | hy
    · exact le_rfl
    · exact hβ.1 hy
  rcases eq_or_lt_of_le (hz.2.trans hyβ) with hzβ | hzβ
  · exact hzβ ▸ mem_insert _ _
  right
  rcases hx with rfl | hx
  · exact absurd hz.1 (not_le.2 hzβ)
  rcases eq_or_lt_of_le hz.1 with rfl | hxz
  · exact hx
  · exact Ioo_subset_of_isLUB hJc hβ hx ⟨hxz, hzβ⟩

/-- `insert α J` is an interval when `α = inf J`. -/
theorem ordConnected_insert_of_isGLB {J : Set ℝ} (hJc : J.OrdConnected) {α : ℝ}
    (hα : IsGLB J α) : (insert α J).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hαx : α ≤ x := by
    rcases hx with rfl | hx
    · exact le_rfl
    · exact hα.1 hx
  rcases eq_or_lt_of_le (hαx.trans hz.1) with hzα | hzα
  · exact hzα ▸ mem_insert _ _
  right
  rcases hy with rfl | hy
  · exact absurd hz.2 (not_le.2 hzα)
  rcases eq_or_lt_of_le hz.2 with rfl | hzy
  · exact hy
  · exact Ioo_subset_of_isGLB hJc hα hy ⟨hzα, hzy⟩

/-- **The time elapsed along `J⁺(p)` is controlled by `T`**:
`2 (z₀ − ‖z⃗‖) (x − p)₀ ≤ T(x)²` for `x ≥ p`, `z = p − r(p)` (future timelike, so `z₀ > ‖z⃗‖`). -/
theorem two_mul_fst_sub_le_cosmoTime_sq (h : CosmoRegular Λ) {p x : Minkowski d}
    (hp : p ∈ omegaPlus Λ) (hpx : (minkowski d).le ⊤ p x) :
    2 * ((p - cosmoRetract Λ p).1 - ‖(p - cosmoRetract Λ p).2‖) * (x - p).1 ≤
      cosmoTime Λ x ^ 2 := by
  have hv : IsFutureCausal (x - p) := le_top_iff_minkQ.1 hpx
  have h1 := cosmoTime_sq_add_smul_ge h hp hv zero_le_one
  rw [one_smul, add_sub_cancel] at h1
  have hv' := isFutureCausal_iff_norm_le.1 hv
  have hi : inner ℝ (p - cosmoRetract Λ p).2 (x - p).2 ≤
      ‖(p - cosmoRetract Λ p).2‖ * ‖(x - p).2‖ := real_inner_le_norm _ _
  have hm := mul_le_mul_of_nonneg_left hv' (norm_nonneg (p - cosmoRetract Λ p).2)
  have hq := hv.2
  have hT := sq_nonneg (cosmoTime Λ p)
  unfold minkB at h1
  nlinarith

/-- **A causal curve of `Ω` over a bounded-above interval, along which `T ≤ B`, is extensible in
`Ω` at its future end**: at a greatest parameter, append; otherwise the time coordinate is bounded
(`two_mul_fst_sub_le_cosmoTime_sq`), the curve converges at its upper end to a point of
`J⁺(Ω) ⊆ Ω`, and `futureExtensible_of_tendsto_opens` applies. -/
theorem futureExtensible_of_cosmoTime_le (h : CosmoRegular Λ) {J : Set ℝ}
    {γ : ℝ → Minkowski d} (hγ : (minkowski d).CausalCurveIn h.regular.opens J γ)
    (hJ : BddAbove J) {B : ℝ} (hB : ∀ u ∈ J, cosmoTime Λ (γ u) ≤ B) :
    (minkowski d).FutureExtensible h.regular.opens J γ := by
  by_cases hmax : ∃ b, IsGreatest J b
  · obtain ⟨b, hb⟩ := hmax
    exact Causality.futureExtensible_of_isGreatest minkowski_causallyArcConnected
      minkowski_isCausal
      hγ hb (Jplus_opens_ne_singleton h.regular (hγ.mem hb.1))
  have hlub : IsLUB J (sSup J) := isLUB_csSup hγ.nonempty hJ
  have hβJ : sSup J ∉ J := fun hβ => hmax ⟨_, hβ, hlub.1⟩
  have hlt : ∀ u ∈ J, u < sSup J := fun u hu =>
    lt_of_le_of_ne (hlub.1 hu) fun he => hβJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski d).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hp₀ : γ u₀ ∈ omegaPlus Λ := hγ.mem hu₀
  have hz := isFutureTimelike_iff_norm_lt.1 (cosmoRetract_facts h hp₀).1
  set κ := (γ u₀ - cosmoRetract Λ (γ u₀)).1 - ‖(γ u₀ - cosmoRetract Λ (γ u₀)).2‖
  have hκ : 0 < κ := by simp only [κ]; linarith
  have hbdd : BddAbove ((fun u => (γ u).1) '' J) := by
    refine ⟨max (γ u₀).1 ((γ u₀).1 + B ^ 2 / (2 * κ)), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rcases le_total u u₀ with huu | huu
    · have := minkowski_le_top_iff.1 (hle u hu u₀ hu₀ huu)
      exact le_max_of_le_left (by linarith [norm_nonneg ((γ u₀).2 - (γ u).2)])
    · have h1 := two_mul_fst_sub_le_cosmoTime_sq h hp₀ (hle u₀ hu₀ u hu huu)
      have h2 : cosmoTime Λ (γ u) ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (cosmoTime_pos h (hγ.mem hu)).le (hB u hu) 2
      refine le_max_of_le_right ?_
      show (γ u).1 ≤ (γ u₀).1 + B ^ 2 / (2 * κ)
      rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
      change 2 * κ * ((γ u).1 - (γ u₀).1) ≤ _ at h1
      nlinarith
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddAbove hle hγ.nonempty hγ.ordConnected hlub hβJ hbdd
  have hpΩ : p ∈ omegaPlus Λ := by
    have hcl : IsClosed {y : Minkowski d | (minkowski d).le ⊤ (γ u₀) y} := by
      simp only [minkowski_le_top_iff]
      exact isClosed_le (by fun_prop) (by fun_prop)
    have : (minkowski d).le ⊤ (γ u₀) p := by
      refine hcl.mem_of_tendsto hp ?_
      filter_upwards [Ioo_mem_nhdsLT (hlt u₀ hu₀)] with u hu
      exact hle u₀ hu₀ u (Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀ hu) hu.1.le
    exact Jplus_omegaPlus_subset Λ ⟨γ u₀, hp₀, this⟩
  exact (Causality.futureExtensible_of_tendsto_opens staticCausality.isClosed_Jplus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hlt
    (ordConnected_insert_of_isLUB hγ.ordConnected hlub) hp
    (Jplus_opens_ne_singleton h.regular hpΩ))

/-- **A causal curve of `Ω` over a bounded-below interval, along which `T ≥ ε > 0`, is extensible
in `Ω` at its past end**: at a least parameter, prepend; otherwise the time coordinate is bounded below (the two
null planes, `fst_sub_le_of_mem_closure`), the curve converges at its lower end to a point of
`cl Ω`, which is not on `∂Ω` because `T → 0` there (`tendsto_cosmoTime_frontier`), and
`pastExtensible_of_tendsto_opens` applies. -/
theorem pastExtensible_of_le_cosmoTime (h : CosmoRegular Λ) {J : Set ℝ}
    {γ : ℝ → Minkowski d} (hγ : (minkowski d).CausalCurveIn h.regular.opens J γ)
    (hJ : BddBelow J) {ε : ℝ} (hε : 0 < ε) (hT : ∀ u ∈ J, ε ≤ cosmoTime Λ (γ u)) :
    (minkowski d).PastExtensible h.regular.opens J γ := by
  by_cases hmin : ∃ a, IsLeast J a
  · obtain ⟨a, ha⟩ := hmin
    exact Causality.pastExtensible_of_isLeast minkowski_causallyArcConnected minkowski_isCausal
      hγ ha (Jminus_opens_ne_singleton h.regular (hγ.mem ha.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski d).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  set D := (w₁.2 - minkB (nullVec w₁.1) (γ u₀)) + (w₂.2 - minkB (nullVec w₂.1) (γ u₀))
  have hbdd : BddBelow ((fun u => (γ u).1) '' J) := by
    refine ⟨min (γ u₀).1 ((γ u₀).1 - D / κ), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rcases le_total u u₀ with huu | huu
    · have h1 := fst_sub_le_of_mem_closure hw₁ hw₂ (subset_closure (hγ.mem hu))
        (hle u hu u₀ hu₀ huu)
      refine min_le_of_right_le ?_
      show (γ u₀).1 - D / κ ≤ (γ u).1
      have h2 : (γ u₀ - γ u).1 ≤ D / κ := by rw [le_div_iff₀ hκ]; linarith
      simp only [Prod.fst_sub] at h2
      linarith
    · have := minkowski_le_top_iff.1 (hle u₀ hu₀ u hu huu)
      exact min_le_of_left_le (by linarith [norm_nonneg ((γ u).2 - (γ u₀).2)])
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddBelow hle hγ.nonempty hγ.ordConnected hglb hαJ hbdd
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) (Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀)
  have hpΩ : p ∈ omegaPlus Λ := by
    have hpcl : p ∈ closure (omegaPlus Λ) :=
      mem_closure_of_tendsto hp (hev.mono fun u hu => hγ.mem hu)
    by_contra hpΩ
    have hpf : p ∈ frontier (omegaPlus Λ) := ⟨hpcl, by rwa [h.regular.2.interior_eq]⟩
    have h2 : Tendsto γ (𝓝[>] (sInf J)) (𝓝[omegaPlus Λ] p) :=
      tendsto_nhdsWithin_iff.2 ⟨hp, hev.mono fun u hu => hγ.mem hu⟩
    obtain ⟨u, hu1, hu2⟩ :=
      (((tendsto_cosmoTime_frontier h hpf).comp h2).eventually (gt_mem_nhds hε)).and hev |>.exists
    exact absurd (hT u hu2) (not_le.2 hu1)
  exact (Causality.pastExtensible_of_tendsto_opens staticCausality.isClosed_Jminus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hgt
    (ordConnected_insert_of_isGLB hγ.ordConnected hglb) hp
    (Jminus_opens_ne_singleton h.regular hpΩ))

/-- **`T → ∞` along every future-inextensible causal curve of `Ω`** (Bonsante; future
completeness): for every `B`, `T > B` on a final segment of the curve. -/
theorem exists_lt_cosmoTime_of_futureInextensible (h : CosmoRegular Λ) {I : Set ℝ}
    {c : ℝ → Minkowski d} (hc : (minkowski d).FutureInextensible h.regular.opens I c) (B : ℝ) :
    ∃ s ∈ I, ∀ s' ∈ I, s ≤ s' → B < cosmoTime Λ (c s') := by
  obtain ⟨hd, hsub, htan, -, hfut⟩ := hc.1.arctanReparam
  have : ∃ s ∈ I, B < cosmoTime Λ (c s) := by
    by_contra hcon
    push Not at hcon
    exact hc.2 (hfut (futureExtensible_of_cosmoTime_le h hd
      ⟨Real.pi / 2, fun u hu => (hsub hu).2.le⟩ fun u hu => hcon _ (htan u hu)))
  obtain ⟨s, hs, hB⟩ := this
  exact ⟨s, hs, fun s' hs' hss' => hB.trans_le (cosmoTime_le_of_le h (hc.1.mem hs)
    ((minkowski d).le_mono le_top (hc.1.le_of_le hs hs' hss')))⟩

/-- **`T → 0` along every past-inextensible causal curve of `Ω`** (Bonsante): for every `ε > 0`,
`T < ε` on an initial segment of the curve. -/
theorem exists_cosmoTime_lt_of_pastInextensible (h : CosmoRegular Λ) {I : Set ℝ}
    {c : ℝ → Minkowski d} (hc : (minkowski d).PastInextensible h.regular.opens I c) {ε : ℝ}
    (hε : 0 < ε) : ∃ s ∈ I, ∀ s' ∈ I, s' ≤ s → cosmoTime Λ (c s') < ε := by
  obtain ⟨hd, hsub, htan, hpast, -⟩ := hc.1.arctanReparam
  have : ∃ s ∈ I, cosmoTime Λ (c s) < ε := by
    by_contra hcon
    push Not at hcon
    exact hc.2 (hpast (pastExtensible_of_le_cosmoTime h hd
      ⟨-(Real.pi / 2), fun u hu => (hsub hu).1.le⟩ hε fun u hu => hcon _ (htan u hu)))
  obtain ⟨s, hs, hB⟩ := this
  exact ⟨s, hs, fun s' hs' hss' => (cosmoTime_le_of_le h (hc.1.mem hs')
    ((minkowski d).le_mono le_top (hc.1.le_of_le hs' hs hss'))).trans_lt hB⟩

/-! ### Cauchy surfaces -/

/-- **Bonsante's exhaustion** (the curve content of Bonsante's Lemma 4.9, cited by Barbot
l.1144–1145): along every inextensible causal curve of `Ω`, the cosmological time takes values
below and above every `t > 0`. Introduced as a DEC-36 named hypothesis; it is **proved** for
every `CosmoRegular Λ` below (`bonsante_exhaustion`), with the cone witness
`bonsante_exhaustion_cone`. -/
def Bonsante_exhaustion (h : CosmoRegular Λ) : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → Minkowski d), (minkowski d).Inextensible h.regular.opens I c →
    ∀ t > 0, (∃ s ∈ I, cosmoTime Λ (c s) < t) ∧ ∃ s ∈ I, t < cosmoTime Λ (c s)

/-- **`S_t` is a Cauchy surface of `Ω`** (ETT's `IsCauchySurfaceOn Ω`, DEC-14), given the
exhaustion: existence by the intermediate value theorem along the curve, uniqueness because `T`
is strictly increasing along `≤_Ω`. -/
theorem isCauchySurfaceOn_cosmoLevel_of (h : CosmoRegular Λ) (hex : Bonsante_exhaustion h)
    {t : ℝ} (ht : 0 < t) : (minkowski d).IsCauchySurfaceOn h.regular.opens (cosmoLevel Λ t) := by
  intro I c hc
  obtain ⟨⟨s₁, hs₁, h₁⟩, s₂, hs₂, h₂⟩ := hex I c hc t ht
  have hmemΩ : ∀ s ∈ I, c s ∈ omegaPlus Λ := fun s hs => hc.1.mem hs
  have hle : ∀ {a b : ℝ}, a ∈ I → b ∈ I → a ≤ b → (minkowski d).le ⊤ (c a) (c b) :=
    fun ha hb hab => (minkowski d).le_mono le_top (hc.1.le_of_le ha hb hab)
  have h12 : s₁ ≤ s₂ := by
    by_contra hlt
    push Not at hlt
    have := cosmoTime_le_of_le h (hmemΩ _ hs₂) (hle hs₂ hs₁ hlt.le)
    linarith
  have hsub : Icc s₁ s₂ ⊆ I := hc.1.ordConnected.out hs₁ hs₂
  have hcont : ContinuousOn (fun s => cosmoTime Λ (c s)) (Icc s₁ s₂) :=
    (continuousOn_cosmoTime h).comp (hc.1.continuousOn_Icc hs₁ hs₂)
      fun s hs => hmemΩ s (hsub hs)
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc h12 hcont ⟨h₁.le, h₂.le⟩
  refine ⟨c s, ⟨⟨s, hsub hs, rfl⟩, hmemΩ s (hsub hs), hst⟩, ?_⟩
  rintro y ⟨⟨s', hs', rfl⟩, hy⟩
  by_contra hne
  rcases le_total s s' with hss | hss
  · have := cosmoTime_lt_of_le h (hmemΩ s (hsub hs)) (hle (hsub hs) hs' hss) fun he => hne he.symm
    rw [show cosmoTime Λ (c s) = t from hst, hy.2] at this
    exact lt_irrefl _ this
  · have := cosmoTime_lt_of_le h (hmemΩ s' hs') (hle hs' (hsub hs) hss) hne
    rw [show cosmoTime Λ (c s) = t from hst, hy.2] at this
    exact lt_irrefl _ this

/-- **Bonsante's exhaustion is a theorem** (Bonsante Lemma 4.9, curve form): from the two
one-sided limits `exists_cosmoTime_lt_of_pastInextensible` and
`exists_lt_cosmoTime_of_futureInextensible`. -/
theorem bonsante_exhaustion (h : CosmoRegular Λ) : Bonsante_exhaustion h := by
  intro I c hc t ht
  obtain ⟨hp, hf⟩ := Causality.inextensible_iff.1 hc
  obtain ⟨s, hs, h₁⟩ := exists_cosmoTime_lt_of_pastInextensible h hp ht
  obtain ⟨s', hs', h₂⟩ := exists_lt_cosmoTime_of_futureInextensible h hf t
  exact ⟨⟨s, hs, h₁ s hs le_rfl⟩, s', hs', h₂ s' hs' le_rfl⟩

/-- **`S_t` is a Cauchy surface of `Ω`** (Bonsante Lemma 4.9, l.1144–1145), with no `sorry`. -/
theorem isCauchySurfaceOn_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    (minkowski d).IsCauchySurfaceOn h.regular.opens (cosmoLevel Λ t) :=
  isCauchySurfaceOn_cosmoLevel_of h (bonsante_exhaustion h) ht

/-! ### `bprop:lip`: the Gauss map is `1/t`-Lipschitz (chordal form) -/

/-- **`∂Ω` is achronal**: two boundary points are never chronologically related. -/
theorem minkQ_sub_nonneg_of_mem_frontier (h : FutureRegular Λ) {a b : Minkowski d}
    (ha : a ∈ frontier (omegaPlus Λ)) (hb : b ∈ frontier (omegaPlus Λ)) : 0 ≤ minkQ (a - b) := by
  by_contra hneg
  push Not at hneg
  have key : ∀ {x y : Minkowski d}, x ∈ frontier (omegaPlus Λ) → y ∈ frontier (omegaPlus Λ) →
      ¬ IsFutureTimelike (y - x) := by
    intro x y hx hy hxy
    have ho : IsOpen {x' : Minkowski d | IsFutureTimelike (y - x')} :=
      (isOpen_lt continuous_const (continuous_fst.comp (continuous_const.sub continuous_id))).inter
        (isOpen_lt (continuous_minkQ.comp (continuous_const.sub continuous_id)) continuous_const)
    obtain ⟨x', hx'o, hx'Ω⟩ := mem_closure_iff.1 (frontier_subset_closure hx) _ ho hxy
    have hyΩ : y ∈ omegaPlus Λ :=
      Jplus_omegaPlus_subset Λ ⟨x', hx'Ω, le_top_iff_minkQ.2 (show IsFutureTimelike (y - x') from
        hx'o).isFutureCausal⟩
    rw [h.2.frontier_eq] at hy
    exact hy.2 hyΩ
  rcases isFutureTimelike_or_neg hneg with h1 | h1
  · exact key hb ha h1
  · exact key ha hb (by rwa [neg_sub] at h1)

/-- `|n(p) − n(p')|² ≥ 0`: two unit future timelike vectors differ by a spacelike (or zero) vector. -/
theorem minkQ_gaussMap_sub_nonneg (h : CosmoRegular Λ) {p p' : Minkowski d}
    (hp : p ∈ omegaPlus Λ) (hp' : p' ∈ omegaPlus Λ) :
    0 ≤ minkQ (gaussMap Λ p - gaussMap Λ p') := by
  have hcs := sqrt_mul_sqrt_le_neg_minkB (isFutureTimelike_gaussMap h hp).isFutureCausal
    (isFutureTimelike_gaussMap h hp').isFutureCausal
  rw [minkQ_gaussMap h hp, minkQ_gaussMap h hp'] at hcs
  rw [mQ_sub, minkQ_gaussMap h hp, minkQ_gaussMap h hp']
  norm_num at hcs
  linarith

/-- `bprop:lip`, **chordal form** (the inequality of Barbot's proof, l.1083–1105, taken at
`ε = t`): for `p, p' ∈ S_t`, `t² |n(p) − n(p')|² ≤ |p − p'|²`. -/
theorem minkQ_gaussMap_sub_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) :
    t ^ 2 * minkQ (gaussMap Λ p - gaussMap Λ p') ≤ minkQ (p - p') := by
  have hrf := (cosmoRetract_spec h hp.1).1
  have hrf' := (cosmoRetract_spec h hp'.1).1
  have hs1 := minkB_cosmoRetract_le h hp.1 (frontier_subset_closure hrf')
  have hs2 := minkB_cosmoRetract_le h hp'.1 (frontier_subset_closure hrf)
  have hQ := minkQ_sub_nonneg_of_mem_frontier h.regular hrf hrf'
  have hpe : cosmoRetract Λ p + t • gaussMap Λ p = p := by
    rw [← hp.2]; exact cosmoRetract_add_smul_gaussMap h hp.1
  have hpe' : cosmoRetract Λ p' + t • gaussMap Λ p' = p' := by
    rw [← hp'.2]; exact cosmoRetract_add_smul_gaussMap h hp'.1
  have hz : p - cosmoRetract Λ p = t • gaussMap Λ p := by rw [← smul_gaussMap h hp.1, hp.2]
  have hz' : p' - cosmoRetract Λ p' = t • gaussMap Λ p' := by
    rw [← smul_gaussMap h hp'.1, hp'.2]
  rw [hz, mB_smul_left] at hs1
  rw [hz', mB_smul_left] at hs2
  set n := gaussMap Λ p
  set n' := gaussMap Λ p'
  set r := cosmoRetract Λ p
  set r' := cosmoRetract Λ p'
  have he : (r + t • n) - (r' + t • n') = (r - r') + t • (n - n') := by module
  rw [hpe, hpe'] at he
  rw [he, mQ_add, mB_smul_right, minkQ_smul, mB_sub_left, mB_sub_right, mB_sub_right,
    minkB_comm r n, minkB_comm r n', minkB_comm r' n, minkB_comm r' n']
  rw [mB_sub_right] at hs1 hs2
  have h1 : minkB n r' - minkB n r ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : minkB n' r - minkB n' r' ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- `bprop:lip` with square roots: `√|n(p) − n(p')|² ≤ (1/t) √|p − p'|²` on `S_t`. -/
theorem sqrt_minkQ_gaussMap_sub_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) :
    √(minkQ (gaussMap Λ p - gaussMap Λ p')) ≤ t⁻¹ * √(minkQ (p - p')) := by
  have h1 := minkQ_gaussMap_sub_le h ht hp hp'
  have h0 := minkQ_gaussMap_sub_nonneg h hp.1 hp'.1
  rw [le_inv_mul_iff₀ ht, ← Real.sqrt_sq ht.le, ← Real.sqrt_mul (sq_nonneg t)]
  exact Real.sqrt_le_sqrt h1

/-! ### Isometries preserving `Ω` -/

/-- An isometry preserving `Ω` preserves the proper times from the boundary. -/
theorem cosmoTimes_smul {g : isom d} (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ)
    (p : Minkowski d) : cosmoTimes Λ (g • p) = cosmoTimes Λ p := by
  have hf : (fun p => g • p) ⁻¹' frontier (omegaPlus Λ) = frontier (omegaPlus Λ) := by
    have := (isom.toHomeomorph g).preimage_frontier (omegaPlus Λ)
    simp only [isom.coe_toHomeomorph] at this
    rw [this, hg]
  have hfm : ∀ q, g • q ∈ frontier (omegaPlus Λ) ↔ q ∈ frontier (omegaPlus Λ) := fun q => by
    rw [← mem_preimage (f := fun p => g • p), hf]
  ext x
  constructor
  · rintro ⟨q, ⟨hqf, hqle⟩, rfl⟩
    refine ⟨g⁻¹ • q, ⟨(hfm _).1 (by rwa [smul_inv_smul]),
      (isom_le_top_iff g).1 (by rwa [smul_inv_smul])⟩, ?_⟩
    show segTime (g⁻¹ • q) p = segTime q (g • p)
    unfold segTime
    rw [← isom_minkQ_sub g (g⁻¹ • q) p, smul_inv_smul]
  · rintro ⟨q, ⟨hqf, hqle⟩, rfl⟩
    refine ⟨g • q, ⟨(hfm q).2 hqf, (isom_le_top_iff g).2 hqle⟩, ?_⟩
    show segTime (g • q) (g • p) = segTime q p
    unfold segTime
    rw [isom_minkQ_sub]

/-- **`T` is `Isom`-invariant**: `T(g p) = T(p)` for every isometry preserving `Ω` (the input of
`bprop:agissons`, l.1186–1187). -/
theorem cosmoTime_smul {g : isom d} (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ)
    (p : Minkowski d) : cosmoTime Λ (g • p) = cosmoTime Λ p := by
  rw [cosmoTime, cosmoTime, cosmoTimes_smul hg]

theorem smul_mem_cosmoLevel_iff {g : isom d}
    (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ) {t : ℝ} {p : Minkowski d} :
    g • p ∈ cosmoLevel Λ t ↔ p ∈ cosmoLevel Λ t := by
  have hm : g • p ∈ omegaPlus Λ ↔ p ∈ omegaPlus Λ := by
    rw [← mem_preimage (f := fun p => g • p), hg]
  simp only [cosmoLevel, mem_setOf_eq, cosmoTime_smul hg, hm]

/-- **Every level set is invariant**: `g(S_t) = S_t`. -/
theorem smul_cosmoLevel {g : isom d} (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ)
    (t : ℝ) : (fun p => g • p) '' cosmoLevel Λ t = cosmoLevel Λ t := by
  ext q
  refine ⟨?_, fun hq => ⟨g⁻¹ • q, smul_mem_cosmoLevel_iff hg |>.1 (by rwa [smul_inv_smul]),
    smul_inv_smul g q⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact (smul_mem_cosmoLevel_iff hg).2 hp

/-- An isometry with `g.Λ = Λ` preserves `Ω⁺(Λ)`. -/
theorem preimage_omegaPlus_of_isomPenrose {g : isom d} (hΛ : isomPenrose g '' Λ = Λ) :
    (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ := by
  have := isom_preimage_omegaPlus g Λ
  rwa [hΛ] at this

/-- The retraction and the Gauss map are equivariant. -/
theorem cosmoRetract_smul (h : CosmoRegular Λ) {g : isom d}
    (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) : cosmoRetract Λ (g • p) = g • cosmoRetract Λ p := by
  have hgp : g • p ∈ omegaPlus Λ := by rw [← mem_preimage (f := fun p => g • p), hg]; exact hp
  have hf : (fun p => g • p) ⁻¹' frontier (omegaPlus Λ) = frontier (omegaPlus Λ) := by
    have := (isom.toHomeomorph g).preimage_frontier (omegaPlus Λ)
    simp only [isom.coe_toHomeomorph] at this
    rw [this, hg]
  obtain ⟨hrf, hrp, -⟩ := cosmoRetract_spec h hp
  have hgrf : g • cosmoRetract Λ p ∈ frontier (omegaPlus Λ) := by
    rw [← mem_preimage (f := fun p => g • p), hf]; exact hrf
  refine (eq_cosmoRetract_of_frontier h hgp hgrf ((isom_le_top_iff g).2 hrp) ?_).symm
  rw [cosmoTime_smul hg, cosmoTime_eq_segTime h hp]
  unfold segTime
  rw [isom_minkQ_sub]

/-! ### `bprop:agissons`, the `Ω`-level part -/

/-- `bprop:agissons`, **`Ω`-level part** (l.1185–1188): a group `Γ` of isometries preserving `Ω`
leaves `T` and every level set `S_t` invariant. -/
theorem agissons_invariant (Γ : Subgroup (isom d))
    (hΓ : ∀ γ ∈ Γ, (fun p => γ • p) ⁻¹' omegaPlus Λ = omegaPlus Λ) :
    (∀ γ ∈ Γ, ∀ p, cosmoTime Λ (γ • p) = cosmoTime Λ p) ∧
      ∀ γ ∈ Γ, ∀ t, (fun p => γ • p) '' cosmoLevel Λ t = cosmoLevel Λ t :=
  ⟨fun γ hγ p => cosmoTime_smul (hΓ γ hγ) p, fun γ hγ t => smul_cosmoLevel (hΓ γ hγ) t⟩

/-! ### `bprop:regular_cauchy_complete`, as far as it goes -/

/-- `bprop:regular_cauchy_complete`, **partial**: a regular domain (two directions) is globally
hyperbolic, and each level set `S_t` (`t > 0`) is a closed acausal Cauchy surface of `Ω`.
Cauchy-completeness is not stated (SCOPE). -/
theorem regular_cauchy (h : CosmoRegular Λ) :
    (minkowski d).GloballyHyperbolicOn h.regular.opens ∧ ∀ t > 0,
      (minkowski d).IsCauchySurfaceOn h.regular.opens (cosmoLevel Λ t) ∧
        (minkowski d).IsAcausal (cosmoLevel Λ t) ∧ IsClosed (cosmoLevel Λ t) :=
  ⟨h.regular.globallyHyperbolicOn, fun _ ht =>
    ⟨isCauchySurfaceOn_cosmoLevel h ht, isAcausal_cosmoLevel h _, isClosed_cosmoLevel h ht⟩⟩

/-! ### The standard example: the future cone -/

/-- `Λ = 𝒮 × {0}`: `Ω⁺(Λ)` is the open future cone `I⁺(0)` (`d ≥ 1`). -/
theorem omegaPlus_cone (hd : 0 < d) :
    omegaPlus (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) = {p | IsFutureTimelike p} := by
  ext p
  rw [mem_omegaPlus, mem_setOf_eq, isFutureTimelike_iff_norm_lt]
  constructor
  · intro hp
    have key : ∀ u : PenroseSphere d, -p.1 + inner ℝ (u : EuclideanSpace ℝ (Fin d)) p.2 < 0 :=
      fun u => by
        have := hp (u, 0) ⟨mem_univ _, rfl⟩
        rwa [minkB_nullVec] at this
    by_cases h0 : p.2 = 0
    · have := key (sphereBase hd)
      rw [h0, inner_zero_right] at this
      rw [h0, norm_zero]; linarith
    · have hn : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.2 h0
      set u : PenroseSphere d := ⟨‖p.2‖⁻¹ • p.2, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
      have hi : inner ℝ (u : EuclideanSpace ℝ (Fin d)) p.2 = ‖p.2‖ := by
        show inner ℝ (‖p.2‖⁻¹ • p.2) p.2 = ‖p.2‖
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      have := key u
      linarith
  · intro hp w hw
    have hw2 : w.2 = 0 := hw.2
    rw [hw2, minkB_nullVec]
    have := real_inner_le_norm (w.1 : EuclideanSpace ℝ (Fin d)) p.2
    rw [norm_penroseSphere, one_mul] at this
    linarith

/-- **The future cone is a regular domain with two directions** (`d ≥ 1`). -/
theorem cosmoRegular_cone (hd : 0 < d) :
    CosmoRegular (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) := by
  refine ⟨futureRegular_and_pastRegular_cone.1, ?_⟩
  set u := sphereBase hd
  set u' : PenroseSphere d := ⟨-(u : EuclideanSpace ℝ (Fin d)), by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_penroseSphere]⟩
  refine ⟨(u, 0), ⟨mem_univ _, rfl⟩, (u', 0), ⟨mem_univ _, rfl⟩, fun he => ?_⟩
  have he' : (u : EuclideanSpace ℝ (Fin d)) = -(u : EuclideanSpace ℝ (Fin d)) :=
    congrArg Subtype.val he
  have h2 : (2 : ℝ) • (u : EuclideanSpace ℝ (Fin d)) = 0 := by
    rw [two_smul]; nth_rewrite 2 [he']; exact add_neg_cancel _
  have := congrArg norm h2
  rw [norm_smul, norm_penroseSphere, norm_zero] at this
  norm_num at this

/-- **The cosmological time of the future cone**: `T(p) = √(−|p|²)` and `r(p) = 0` (`d ≥ 1`),
the standard example of [4.CT]. -/
theorem cosmoTime_cone (hd : 0 < d) {p : Minkowski d} (hp : IsFutureTimelike p) :
    cosmoTime (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) p = √(-minkQ p) ∧
      cosmoRetract (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) p = 0 := by
  set Λc : Set (PenroseSphere d × ℝ) := univ ×ˢ {0}
  have h := cosmoRegular_cone hd
  have hΩ := omegaPlus_cone hd
  have hpΩ : p ∈ omegaPlus Λc := by rw [hΩ]; exact hp
  have hcl : closure (omegaPlus Λc) ⊆ {v : Minkowski d | IsFutureCausal v} := by
    refine closure_minimal (fun v hv => ?_)
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_minkQ continuous_const))
    rw [hΩ] at hv
    exact (show IsFutureTimelike v from hv).isFutureCausal
  have h0cl : (0 : Minkowski d) ∈ closure (omegaPlus Λc) := by
    have hc : Continuous fun t : ℝ => ((t, 0) : Minkowski d) := by fun_prop
    have ht : Tendsto (fun t : ℝ => ((t, 0) : Minkowski d)) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto 0; rw [Prod.mk_zero_zero] at this; exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
    rw [hΩ]
    exact isFutureTimelike_iff_norm_lt.2 (by simpa using ht0)
  have h0 : (0 : Minkowski d) ∈ cosmoPast Λc p :=
    ⟨h0cl, le_top_iff_minkQ.2 (by simpa using hp.isFutureCausal)⟩
  have hseg0 : segTime 0 p = √(-minkQ p) := by simp [segTime]
  have hup : ∀ q ∈ cosmoPast Λc p, segTime q p ≤ √(-minkQ p) := fun q hq => by
    have hq1 : IsFutureCausal q := hcl hq.1
    have hq2 := le_top_iff_minkQ.1 hq.2
    have := sqrt_neg_minkQ_add_le hq1 hq2
    rw [add_sub_cancel] at this
    unfold segTime
    linarith [Real.sqrt_nonneg (-minkQ q)]
  have hT : cosmoTime Λc p = √(-minkQ p) := by
    refine le_antisymm ?_ (hseg0 ▸ segTime_le_cosmoTime h hpΩ h0)
    rw [cosmoTime_eq_segTime h hpΩ]
    exact hup _ ⟨frontier_subset_closure (cosmoRetract_spec h hpΩ).1, (cosmoRetract_spec h hpΩ).2.1⟩
  exact ⟨hT, (eq_cosmoRetract h hpΩ h0 (by rw [hseg0, hT])).symm⟩

/-- On the future cone the level sets are the hyperboloids `{|p|² = −t²}` and the Gauss map is
`n(p) = p / T(p)` (`d ≥ 1`). -/
theorem gaussMap_cone (hd : 0 < d) {p : Minkowski d} (hp : IsFutureTimelike p) :
    gaussMap (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) p = (√(-minkQ p))⁻¹ • p := by
  obtain ⟨hT, hr⟩ := cosmoTime_cone hd hp
  rw [gaussMap, hT, hr, sub_zero]

/-- **Non-vacuity witness** (kb/0012) for `Bonsante_exhaustion`: the future cone (`d ≥ 1`). -/
theorem bonsante_exhaustion_cone (hd : 0 < d) : Bonsante_exhaustion (cosmoRegular_cone hd) :=
  bonsante_exhaustion _

/-! ### Finding: the printed boundedness fails for two points with one null direction -/

/-- [4.CT] **as printed** (l.1048–1051), kept as a `Prop` (kb/0022, DEC-27), with the paper's own
hypotheses on `Λ`: closed and with at least two elements ("If `Λ` contains at least `2`
elements, then `Ω^±(Λ)`, if nonempty, is regular", Def 4.4, l.900–901; "closed sets `Λ` in `𝒥`
not reduced to one point", l.1001–1004), and future regular (Def 4.5, l.913–919): the proper
times from the boundary to a point of `Ω` are uniformly bounded. -/
def CosmoBoundedAsPrinted (d : ℕ) : Prop :=
  ∀ Λ : Set (PenroseSphere d × ℝ), IsClosed Λ → Λ.Nontrivial → FutureRegular Λ →
    ∀ p ∈ omegaPlus Λ, BddAbove (cosmoTimes Λ p)

/-- **Finding: the printed claim is false** for `d ≥ 1` (Barbot's `n ≥ 2`), under the paper's
own hypotheses: `Λ = {(u, 0), (u, 1)}` is closed, has two elements, and is future regular, with
`Ω⁺(Λ) = P⁺(u, 0)` the open half-space (the second plane is parallel and redundant); from the
boundary null plane the proper times to `(1, 0)` are unbounded (`√(2a − 1)` along
`q_a = (1 − a, (1 − a)u)`). Two elements may share their null direction: the paper's "at least
2 elements / not reduced to one point" does not give Bonsante's two non-parallel null support
planes (Bonsante Def 4.1), which `CosmoRegular.two` asks; under it the bound holds
(`bddAbove_cosmoTimes`). -/
theorem not_cosmoBoundedAsPrinted (hd : 0 < d) : ¬ CosmoBoundedAsPrinted d := by
  intro hP
  set u := sphereBase hd
  set Λ₂ : Set (PenroseSphere d × ℝ) := {(u, 0), (u, 1)}
  have hΩ : omegaPlus Λ₂ = halfPlus u 0 := by
    ext p
    simp only [Λ₂, mem_omegaPlus, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq, mem_halfPlus]
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans one_pos⟩⟩
  have hp : ((1, 0) : Minkowski d) ∈ omegaPlus Λ₂ := by
    rw [hΩ, mem_halfPlus, minkB_nullVec]; simp
  have hreg : FutureRegular Λ₂ := ⟨⟨_, hp⟩, by rw [hΩ]; exact isOpen_halfPlus u 0⟩
  have hcl : IsClosed Λ₂ := (Set.toFinite Λ₂).isClosed
  have hnt : Λ₂.Nontrivial :=
    ⟨(u, 0), mem_insert _ _, (u, 1), mem_insert_of_mem _ rfl, by simp⟩
  obtain ⟨M, hM⟩ := hP Λ₂ hcl hnt hreg _ hp
  set a := M ^ 2 + 1
  have ha : 1 ≤ a := by simp only [a]; nlinarith [sq_nonneg M]
  set q : Minkowski d := (1 - a, -(a - 1) • (u : EuclideanSpace ℝ (Fin d)))
  have hu : inner ℝ (u : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_penroseSphere]; norm_num
  have hqf : q ∈ frontier (omegaPlus Λ₂) := by
    rw [hΩ, frontier_halfPlus]
    show minkB (nullVec u) q = 0
    rw [minkB_nullVec]
    simp only [q, real_inner_smul_right, hu]
    ring
  have hdiff : ((1, 0) : Minkowski d) - q = (a, (a - 1) • (u : EuclideanSpace ℝ (Fin d))) := by
    simp only [q, Prod.mk_sub_mk, zero_sub, neg_smul, neg_neg]
    congr 1; ring
  have hqle : (minkowski d).le ⊤ q (1, 0) := by
    rw [minkowski_le_top_iff]
    have := congrArg Prod.snd hdiff
    have h1 := congrArg Prod.fst hdiff
    simp only [Prod.snd_sub, Prod.fst_sub] at this h1
    rw [this, h1, norm_smul, norm_penroseSphere, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hle : segTime q ((1, 0) : Minkowski d) ≤ M := hM ⟨q, ⟨hqf, hqle⟩, rfl⟩
  have hval : segTime q ((1, 0) : Minkowski d) = √(2 * M ^ 2 + 1) := by
    rw [segTime, hdiff]
    congr 1
    simp only [minkQ, norm_smul, norm_penroseSphere, Real.norm_eq_abs, mul_one, sq_abs, a]
    ring
  rw [hval] at hle
  rcases lt_or_ge M 0 with hM0 | hM0
  · linarith [Real.sqrt_nonneg (2 * M ^ 2 + 1)]
  · have := (Real.lt_sqrt hM0).2 (by nlinarith : M ^ 2 < 2 * M ^ 2 + 1)
    linarith

end Causal.Flat
