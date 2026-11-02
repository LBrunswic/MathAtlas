import Causal.Splitting
import Causal.Geroch
import Causal.Flat.GerochFlat
import Causal.Flat.Develop
import Causal.Flat.CauchyComplete

/-!
# `Causal.Flat.SplittingFull` — a splitting `M ≅ S × ℝ` all of whose slices are Cauchy

# `Causal.Flat.SplittingFull` — a splitting `M ≅ S × ℝ` all of whose slices are Cauchy

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8.
Label certified (line in `papers/barbot/legacy/labeled/GHFspace.tex`), ruling DEC-100:

* **`bprop:splitting`** — `GHFspace.tex:2460` (Prop 8.11, l.2459–2463; marked, DEC-100: "every
  `S × {∗}` Cauchy" read as *for a suitable splitting*, `S` acausal disclosed — here derived, not
  assumed; **no `sorry`**) — `bprop_splitting_full`, with the richer
  `flat_exists_isCauchySurface_slices`:

> From now, we assume that $M$ is a Cauchy-complete globally hyperbolic spacetime admitting $S$ as
> a complete Cauchy hypersurface of $M$. (l.2454–2456)

> $M$ is homeomorphic to $ S \times {\mathbb R}$, where every $S \times \{ \ast \}$ are Cauchy
> hypersurfaces. Any nonspacelike geodesic in $\widetilde{M}$ intersect $\widetilde{S}$.
> (l.2461–2463; proof: "See \cite{beem}", l.2467)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

**Construction.** The flow splitting `ψ (x, s) = φ s x` of `Causal.Splitting`
(`IsCausalFlow.splitting`, a chronal causal flow `flat_hasChronalCausalFlow`) has slices
`φ_s(S)`, which need not be Cauchy (`minkowski_skew_slice_not_isCauchySurface`). Each orbit is
reparametrised by a Cauchy time function `T` strictly increasing along `≤` (Geroch's
`T = log(−t⁻/t⁺)`, `Causality.geroch_i_imp_ii`, from the admissible measure of
`Flat.exists_admissible_measure`): `Φ (x, t)` is the point of the orbit of `x ∈ S` where `T = t`.
Its inverse is `p ↦ (π p, T p)`; the reparametrisation `(x, s) ↦ (x, T (φ s x))` is a
homeomorphism of `S × ℝ` (`fibreReparam`, `continuous_fibreIso_symm`). So `Φ (S × {t}) = T⁻¹(t)`,
a Cauchy surface (`IsCauchyTimeFunction.isCauchySurface_level`).

## Main declarations

* `fibreReparam` — `(x, s) ↦ (x, F (x, s))` is a homeomorphism of `X × ℝ` when `F` is
  continuous and each `F (x, ·)` strictly increasing and onto.
* `Causality.IsCauchyTimeFunction.isCauchySurface_level` — every level set of a strictly
  increasing Cauchy time function is a Cauchy surface.
* `Causality.IsCausalFlow.exists_homeomorph_level` (abstract: causal flow, acausal Cauchy `S`,
  `J^±(S)` closed) and `IsCausalFlow.exists_homeomorph_isCauchySurface_slices` (chronal flow).
* `Flat.flat_exists_isCauchySurface_slices`, `Flat.bprop_splitting_full`;
  witness `Flat.bprop_splitting_full_minkowskiSpace`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` globally hyperbolic | ✓ carried: `GH M` (ETT's: causal, compact diamonds — the library's reading of Barbot's GH, `FlatSpacetime.lean`) |
| `M` Cauchy-complete, `S` complete | ⚠ weakened: not used |
| `S` a Cauchy hypersurface | ✓ carried: `IsCauchySurface S` (DEC-14); acausality of `S` is **derived** (`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow`) and returned, not assumed |
| `M` a manifold (second countable, Hausdorff) | ✓ carried by `FlatSpacetime` (T2, connected); second countability proved (`FlatSpacetime.secondCountableTopology`, DEC-49) |
| "every `S × {∗}` Cauchy" | ⚠ reading (DEC-100): for a **suitable** splitting, which is constructed; not for every splitting (finding below) |
| "nonspacelike geodesic of `M̃` meets `S̃`" | ⚠ reading: lift form, as in `Flat/Develop.lean` — `p⁻¹(S)` is a Cauchy surface of `M̃` (every inextensible causal curve, in particular every inextensible nonspacelike geodesic, meets it exactly once) |

## SCOPE (disclosed)

* **The slices are Cauchy for this splitting, not for every one.** The finding of
  `Causal/Splitting.lean` stands: on `𝐌ⁿ`, `n ≥ 2`, the chronal causal flow
  `φ_t(s, x) = (s + t(1 + |x|), x)` splits along `{t = 0}` and its slice at time `1` is not
  Cauchy (`minkowski_skew_slice_not_isCauchySurface`). DEC-100 reads the printed sentence as the
  existence of a splitting with Cauchy slices, which is what `bprop_splitting_full` states.
* **`Φ (x, 0) = x` is not asked and does not hold in general**: `S × {0}` goes to `T⁻¹(0)`, not
  to `S`; what holds is `Φ (x, T x) = x` (the identity on the graph of `T|S`). So `Φ` is not an
  `IsCauchySplitting` in the sense of `Causal.CauchyDiamond` (its `zero` field); its lines
  `t ↦ Φ (x, t)` are future causal (returned). A splitting with both `S × {0} ↦ S` and all slices
  Cauchy would need a Cauchy time function with `S = T⁻¹(0)`, which the library does not build.
* **"Geodesic"**: the library has no geodesics of a flat spacetime; the sentence is read in the
  lift form of `Flat/Develop.lean` (`isCauchySurface_liftSet`), through which the paper uses it.
* Smoothness of the slices (hypersurfaces) is not asserted: the Cauchy surfaces are ETT's,
  topological (DEC-14).
* **No `sorry` in this file or beneath it**; `#print axioms` of `bprop_splitting_full` and
  `flat_exists_isCauchySurface_slices`: `propext`, `Classical.choice`, `Quot.sound`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
ruling DEC-100.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

/-! ### A fibrewise reparametrisation of `X × ℝ` -/

section Fibre

variable {X : Type*} [TopologicalSpace X] (F : X × ℝ → ℝ)
  (hmono : ∀ x, StrictMono fun s => F (x, s)) (hsurj : ∀ x, Surjective fun s => F (x, s))

/-- The order isomorphism `s ↦ F (x, s)` of `ℝ`. -/
noncomputable def fibreIso (x : X) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (hmono x) (hsurj x)

omit [TopologicalSpace X] in
theorem fibreIso_apply (x : X) (s : ℝ) : fibreIso F hmono hsurj x s = F (x, s) := rfl

/-- **The inverse of a continuous, fibrewise strictly increasing and onto `F` is continuous**:
`a < g(x, t) ↔ F(x, a) < t` and `g(x, t) < a ↔ t < F(x, a)`, two open conditions. -/
theorem continuous_fibreIso_symm (hF : Continuous F) :
    Continuous fun q : X × ℝ => (fibreIso F hmono hsurj q.1).symm q.2 := by
  have hFa : ∀ a : ℝ, Continuous fun q : X × ℝ => F (q.1, a) := fun a =>
    hF.comp (continuous_fst.prodMk continuous_const)
  refine continuous_iff_continuousAt.2 fun q => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hiff : ∀ r : X × ℝ, a < (fibreIso F hmono hsurj r.1).symm r.2 ↔ F (r.1, a) < r.2 :=
      fun r => (fibreIso F hmono hsurj r.1).lt_symm_apply
    have hopen : IsOpen {r : X × ℝ | F (r.1, a) < r.2} := isOpen_lt (hFa a) continuous_snd
    filter_upwards [hopen.mem_nhds ((hiff q).1 ha)] with r hr using (hiff r).2 hr
  · have hiff : ∀ r : X × ℝ, (fibreIso F hmono hsurj r.1).symm r.2 < a ↔ r.2 < F (r.1, a) :=
      fun r => by
        rw [← (fibreIso F hmono hsurj r.1).lt_iff_lt, OrderIso.apply_symm_apply]
        rfl
    have hopen : IsOpen {r : X × ℝ | r.2 < F (r.1, a)} := isOpen_lt continuous_snd (hFa a)
    filter_upwards [hopen.mem_nhds ((hiff q).1 ha)] with r hr using (hiff r).2 hr

/-- **The fibrewise reparametrisation** `(x, s) ↦ (x, F (x, s))`, a homeomorphism of `X × ℝ`
when `F` is continuous and each `F (x, ·)` is strictly increasing and onto. -/
noncomputable def fibreReparam (hF : Continuous F) : X × ℝ ≃ₜ X × ℝ where
  toFun q := (q.1, F q)
  invFun q := (q.1, (fibreIso F hmono hsurj q.1).symm q.2)
  left_inv q := by
    rcases q with ⟨x, s⟩
    refine Prod.ext rfl ?_
    show (fibreIso F hmono hsurj x).symm (fibreIso F hmono hsurj x s) = s
    exact (fibreIso F hmono hsurj x).symm_apply_apply s
  right_inv q := by
    rcases q with ⟨x, t⟩
    refine Prod.ext rfl ?_
    show fibreIso F hmono hsurj x ((fibreIso F hmono hsurj x).symm t) = t
    exact (fibreIso F hmono hsurj x).apply_symm_apply t
  continuous_toFun := continuous_fst.prodMk hF
  continuous_invFun := continuous_fst.prodMk (continuous_fibreIso_symm F hmono hsurj hF)

theorem fibreReparam_apply (hF : Continuous F) (q : X × ℝ) :
    fibreReparam F hmono hsurj hF q = (q.1, F q) := rfl

theorem fibreReparam_symm_apply (hF : Continuous F) (q : X × ℝ) :
    (fibreReparam F hmono hsurj hF).symm q = (q.1, (fibreIso F hmono hsurj q.1).symm q.2) := rfl

end Fibre

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {φ : Flow ℝ M} {S : Set M}

/-! ### Level sets of a strictly increasing Cauchy time function -/

/-- **Every level set `T⁻¹(t)` of a Cauchy time function strictly increasing along `≤` is a
Cauchy surface** (`IsCauchyTimeFunction.isCauchySurface` is the level `0`). -/
theorem IsCauchyTimeFunction.isCauchySurface_level [T1Space M] (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {T : M → ℝ} (hT : C.IsCauchyTimeFunction T)
    (hstrict : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (t : ℝ) :
    C.IsCauchySurface (T ⁻¹' {t}) := by
  intro I c hc
  obtain ⟨ψ, -, -, hψr, hcψ⟩ := hc.reparam hC hSC.isCausal hJm hJp
  obtain ⟨hbot, htop⟩ := hT.2 _ hcψ
  have hcont : Continuous (T ∘ (c ∘ ψ)) := hT.1.continuous.comp hcψ.1.continuous
  obtain ⟨s₁, hs₁⟩ := (hbot.eventually (eventually_le_atBot t)).exists
  obtain ⟨s₂, hs₂⟩ := (htop.eventually (eventually_ge_atTop t)).exists
  obtain ⟨s, hs⟩ := intermediate_value_univ s₁ s₂ hcont ⟨hs₁, hs₂⟩
  refine ⟨c (ψ s), ⟨⟨ψ s, hψr ▸ mem_range_self s, rfl⟩, hs⟩, ?_⟩
  rintro y ⟨⟨r, hr, rfl⟩, hy⟩
  have hψs : ψ s ∈ I := hψr ▸ mem_range_self s
  have hy' : T (c r) = t := hy
  have hs' : T (c (ψ s)) = t := hs
  by_contra hne
  rcases le_total r (ψ s) with h | h
  · have := hstrict _ _ (hc.1.le_of_le hr hψs h) hne
    linarith
  · have := hstrict _ _ (hc.1.le_of_le hψs hr h) (Ne.symm hne)
    linarith

/-! ### The splitting with Cauchy slices -/

/-- **A splitting along `S` all of whose slices are Cauchy surfaces.** A causal flow `φ`, an
acausal Cauchy surface `S` with `J^±(S)` closed (so that the flow splitting
`ψ (x, s) = φ s x` exists, `IsCausalFlow.splitting`), and a Cauchy time function `T` strictly
increasing along `≤`: reparametrising each orbit by `T`, `Φ (x, t)` is the point of the orbit of
`x ∈ S` at which `T = t`. Then `Φ (S × {t}) = T⁻¹(t)`, `T (Φ (x, t)) = t`, `Φ (x, T x) = x`, and
the lines `t ↦ Φ (x, t)` are future causal. -/
theorem IsCausalFlow.exists_homeomorph_level (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) {T : M → ℝ}
    (hT : C.IsCauchyTimeFunction T) (hstrict : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) :
    ∃ Φ : S × ℝ ≃ₜ M, (∀ t : ℝ, Φ '' (univ ×ˢ {t}) = T ⁻¹' {t}) ∧
      (∀ (x : S) (t : ℝ), T (Φ (x, t)) = t) ∧ (∀ x : S, Φ (x, T x) = x) ∧
      (∀ (x : S) ⦃s t : ℝ⦄, s ≤ t → C.le ⊤ (Φ (x, s)) (Φ (x, t))) := by
  set ψ := hφ.splitting hcaus hS hac hJp hJm with hψdef
  have hψ : ∀ q : S × ℝ, ψ q = φ q.2 q.1 := fun q => rfl
  set F : S × ℝ → ℝ := fun q => T (φ q.2 q.1) with hFdef
  have hF : Continuous F :=
    hT.1.continuous.comp (φ.continuous continuous_snd (continuous_subtype_val.comp continuous_fst))
  have hmono : ∀ x : S, StrictMono fun s => F (x, s) := fun x s s' hss' =>
    hstrict _ _ (hφ.le x hss'.le) fun h => hss'.ne (hφ.injective hcaus x h)
  have hsurj : ∀ x : S, Surjective fun s => F (x, s) := fun x => by
    obtain ⟨hbot, htop⟩ := hT.2 _ (hφ.inextensible x)
    have hc : Continuous fun s => F (x, s) := hF.comp (continuous_const.prodMk continuous_id)
    exact hc.surjective htop hbot
  set Θ := fibreReparam F hmono hsurj hF with hΘdef
  refine ⟨Θ.symm.trans ψ, ?_, ?_, ?_, ?_⟩
  · -- the slices are the level sets
    intro t
    ext p
    constructor
    · rintro ⟨⟨x, s⟩, ⟨-, hs⟩, rfl⟩
      rw [mem_singleton_iff] at hs
      subst hs
      show T (ψ (Θ.symm (x, s))) = s
      rw [hψ, fibreReparam_symm_apply]
      exact (fibreIso F hmono hsurj x).apply_symm_apply s
    · intro hp
      have hp' : T p = t := hp
      obtain ⟨⟨x, s⟩, rfl⟩ := ψ.surjective p
      refine ⟨(x, t), ⟨trivial, rfl⟩, ?_⟩
      show ψ (Θ.symm (x, t)) = ψ (x, s)
      congr 1
      rw [Homeomorph.symm_apply_eq, fibreReparam_apply]
      refine Prod.ext rfl ?_
      show t = T (φ s x)
      rw [← hp']
      rfl
  · intro x t
    show T (ψ (Θ.symm (x, t))) = t
    rw [hψ, fibreReparam_symm_apply]
    exact (fibreIso F hmono hsurj x).apply_symm_apply t
  · intro x
    show ψ (Θ.symm (x, T x)) = x
    have h0 : Θ (x, 0) = (x, T x) := by
      rw [fibreReparam_apply]
      refine Prod.ext rfl ?_
      show T (φ 0 x) = T x
      rw [Flow.map_zero_apply]
    rw [← h0, Homeomorph.symm_apply_apply, hψ]
    exact Flow.map_zero_apply _ _
  · intro x s t hst
    show C.le ⊤ (ψ (Θ.symm (x, s))) (ψ (Θ.symm (x, t)))
    rw [hψ, hψ, fibreReparam_symm_apply, fibreReparam_symm_apply]
    exact hφ.le x ((fibreIso F hmono hsurj x).symm.monotone hst)

/-- **The splitting with Cauchy slices**, for a chronal causal flow (no closedness hypothesis):
`Φ : S × ℝ ≃ₜ M` with every `Φ (S × {t})` a Cauchy surface. -/
theorem IsCausalFlow.exists_homeomorph_isCauchySurface_slices [T1Space M]
    (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hφ : C.IsCausalFlow φ)
    (hch : C.IsChronalFlow φ) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) {T : M → ℝ}
    (hT : C.IsCauchyTimeFunction T) (hstrict : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) :
    ∃ Φ : S × ℝ ≃ₜ M, (∀ t : ℝ, C.IsCauchySurface (Φ '' (univ ×ˢ {t}))) ∧
      (∀ x : S, Φ (x, T x) = x) ∧
      (∀ (x : S) ⦃s t : ℝ⦄, s ≤ t → C.le ⊤ (Φ (x, s)) (Φ (x, t))) := by
  have hcaus := hSC.isCausal
  have hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p} := fun p => by
    intro h
    obtain ⟨t, ht⟩ := hφ.nonstationary p
    rcases le_total t 0 with h0 | h0
    · exact ht (by
        have hm : φ t p ∈ C.Jminus ⊤ {p} := ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p h0⟩
        rw [h] at hm; exact hm)
    · have hm : φ (-t) p ∈ C.Jminus ⊤ {p} :=
        ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p (show -t ≤ 0 by linarith)⟩
      rw [h] at hm
      apply ht
      calc φ t p = φ t (φ (-t) p) := by rw [show φ (-t) p = p from hm]
        _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p} := fun p => by
    intro h
    obtain ⟨t, ht⟩ := hφ.nonstationary p
    rcases le_total 0 t with h0 | h0
    · exact ht (by
        have hm : φ t p ∈ C.Jplus ⊤ {p} := ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p h0⟩
        rw [h] at hm; exact hm)
    · have hm : φ (-t) p ∈ C.Jplus ⊤ {p} :=
        ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p (show 0 ≤ -t by linarith)⟩
      rw [h] at hm
      apply ht
      calc φ t p = φ t (φ (-t) p) := by rw [show φ (-t) p = p from hm]
        _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  obtain ⟨Φ, hlev, -, hT0, hmon⟩ := hφ.exists_homeomorph_level hcaus hS hac
    (hφ.isClosed_Jplus hcaus hch hS hac) (hφ.isClosed_Jminus hcaus hch hS hac) hT hstrict
  refine ⟨Φ, fun t => ?_, hT0, hmon⟩
  rw [hlev t]
  exact hT.isCauchySurface_level hC hSC hJm hJp hstrict t

end Causality

/-! ### Flat spacetimes: `bprop:splitting` -/

namespace Flat

variable {d : ℕ}

/-- **A GH flat spacetime splits along any Cauchy surface `S` with all slices Cauchy.**
`Φ : S × ℝ ≃ₜ M`, every slice `Φ (S × {t})` a Cauchy surface, the lines `t ↦ Φ (x, t)` future
causal, and `Φ (x, T x) = x` on `S` for a Cauchy time function `T` (Geroch's, from the admissible
measure of `exists_admissible_measure`). `S` is acausal: a consequence, not a hypothesis
(`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow`). The flow is
`flat_hasChronalCausalFlow`; second countability is `FlatSpacetime.secondCountableTopology`. -/
theorem flat_exists_isCauchySurface_slices (M : FlatSpacetime.{u} d) (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    (flatCausality d M).IsAcausal S ∧ ∃ (T : M → ℝ) (Φ : S × ℝ ≃ₜ M),
      (flatCausality d M).IsCauchyTimeFunction T ∧
      (∀ x y, (flatCausality d M).le ⊤ x y → x ≠ y → T x < T y) ∧
      (∀ t : ℝ, Φ '' (univ ×ˢ {t}) = T ⁻¹' {t}) ∧
      (∀ t : ℝ, (flatCausality d M).IsCauchySurface (Φ '' (univ ×ˢ {t}))) ∧
      (∀ x : S, Φ (x, T x) = x) ∧
      (∀ (x : S) ⦃s t : ℝ⦄, s ≤ t → (flatCausality d M).le ⊤ (Φ (x, s)) (Φ (x, t))) := by
  have hflow : (flatCausality d M).HasChronalCausalFlow := flat_hasChronalCausalFlow
  obtain ⟨φ, hφ, hch⟩ := id hflow
  have hac := isAcausal_of_isCauchySurface_of_hasChronalCausalFlow hflow hS
  have hcaus : (flatCausality d M).IsCausal := hGH.1
  have hT : (flatCausality d M).Tarentin := flatCausality_tarentin
  have hC := flatCausality_causallyArcConnected d M
  have hJm := jminus_ne_singleton_of_isCausalFlow hφ
  have hJp := jplus_ne_singleton_of_isCausalFlow hφ
  have hSC := Causality.GloballyHyperbolic.stronglyCausal hT hGH
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμp, hμm⟩ := exists_admissible_measure M hGH
  obtain ⟨T, hTc, hstrict⟩ := Causality.geroch_i_imp_ii hμp hμm hT hC hJm hJp hGH
  obtain ⟨Φ, hlev, -, hT0, hmon⟩ := hφ.exists_homeomorph_level hcaus hS hac
    (hφ.isClosed_Jplus hcaus hch hS hac) (hφ.isClosed_Jminus hcaus hch hS hac) hTc hstrict
  refine ⟨hac, T, Φ, hTc, hstrict, hlev, fun t => ?_, hT0, hmon⟩
  rw [hlev t]
  exact hTc.isCauchySurface_level hC hSC hJm hJp hstrict t

/-- **`bprop:splitting`** (Prop 8.11, `GHFspace.tex:2459`, l.2461–2463), in the printed form, the
splitting chosen suitably (DEC-100): a GH flat spacetime `M` with a Cauchy surface `S` is
homeomorphic to `S × ℝ` by a homeomorphism all of whose slices `S × {t}` are Cauchy surfaces, and
every inextensible causal curve of the universal cover `M̃` (in particular every inextensible
nonspacelike geodesic) meets `S̃ = p⁻¹(S)`, exactly once (`isCauchySurface_liftSet`). -/
theorem bprop_splitting_full (M : FlatSpacetime.{u} d) (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (x₀ : M) :
    (∃ Φ : S × ℝ ≃ₜ M, ∀ t : ℝ, (flatCausality d M).IsCauchySurface (Φ '' (univ ×ˢ {t}))) ∧
    (letI := flatCoverChartedSpace d M x₀
     haveI := hasGroupoid_flatCover (d := d) M x₀
     (flatCausality d (UniversalCover M x₀)).IsCauchySurface
       (UniversalCover.proj M x₀ ⁻¹' S)) := by
  obtain ⟨-, -, Φ, -, -, -, hslice, -⟩ := flat_exists_isCauchySurface_slices M hGH hS
  exact ⟨⟨Φ, hslice⟩, isCauchySurface_liftSet x₀ hGH.1 hS⟩

/-- **Non-vacuity** (kb/0011): `𝐌ⁿ` is GH and has a Cauchy surface, so `bprop_splitting_full`
applies to it. -/
theorem bprop_splitting_full_minkowskiSpace :
    ∃ S : Set (FlatSpacetime.minkowskiSpace d),
      (flatCausality d (FlatSpacetime.minkowskiSpace d)).IsCauchySurface S ∧
      ∃ Φ : S × ℝ ≃ₜ FlatSpacetime.minkowskiSpace d, ∀ t : ℝ,
        (flatCausality d (FlatSpacetime.minkowskiSpace d)).IsCauchySurface (Φ '' (univ ×ˢ {t})) := by
  obtain ⟨S, hS⟩ := barbotGH_minkowskiSpace (d := d)
  exact ⟨S, hS, (bprop_splitting_full _ gh_minkowskiSpace hS (0 : Minkowski d)).1⟩

end Flat

end Causal
