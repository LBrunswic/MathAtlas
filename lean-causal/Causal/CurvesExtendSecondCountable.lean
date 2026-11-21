import Causal.MaximalZorn
import Causal.OmegaOneConstant
import Causal.CBG.CausalConvex

/-!
# Curves extend in every T1, second countable space with a causality

Programme target `T-abs-curves-extend-second-countable` (`programme/roadmap.toml`; layer 1:
ETT-layer imports only, `Causal.MaximalZorn`, `Causal.OmegaOneConstant`, `Causal.CBG.CausalConvex`;
no model; no metric notion in a statement). There is no paper behind it, so **no label is
marked**. The statement, as the target words it:

> CurvesExtendOn W for every open W of every T1, second countable spacetime, with no other
> hypothesis (hence CurvesExtend): Zorn on towers
> (Causal.AbstractDev.exists_isMaximal_of_chainsInherit) over the causal curves of W with no
> constant end piece, a coherent chain bounded by its direct limit (countable cofinality) or by
> one of its members (uncountable cofinality, through T-abs-omega-one-constant); maximal is
> inextensible

The fact it discharges, as the library states it (`Causal/CauchyExtension.lean:79–81`):

> **A model fact, carried as a named hypothesis** (kb/0012): every future causal curve over a
> segment lies on an inextensible causal curve. In a Lorentzian manifold this is the existence of
> inextensible extensions (Zorn); the library does not prove it for topological spacetimes.

## What is proved

* **The theorem.** In every causality on a T1, second countable space, every future causal curve
  of an open `W` over an interval lies on an inextensible causal curve of `W`
  (`Causality.exists_inextensible_of_t1_secondCountable`). Hence
  `Causality.curvesExtendOn_of_t1_secondCountable` (`CurvesExtendOn W`, every open `W`) and
  `Causality.curvesExtend_of_t1_secondCountable` (`CurvesExtend`). ETT's topological spacetimes
  are Hausdorff and second countable (`def:category_topological_spacetimes`, `ETT.tex:255`), so
  curves extend in every one of them, on every open set. Two named hypotheses discharged, as
  examples: `Causality.IsCauchySurface.isAcausal_of_t1_secondCountable` and
  `Causality.IsCauchySurfaceOn.eq_of_le_of_t1_secondCountable`.
* **The Zorn class** (the target's (1)). `Causality.TailFreeCurve C W`: causal curves of `W`
  over an interval `I` that are `TailFree`, i.e. constant on no final or initial segment of `I`
  with two points. The carrier is the interval; the morphisms, `Causality.tailFreeMor`, are the
  `reparam` field of `Causality.StrictlyExtends`: `f` strictly monotone onto a sub-interval with
  `c' ∘ f = c`. They compose (`tailFreeMor_morphismsCompose`).
* **Chain inheritance** (the target's (2), `tailFreeMor_chainsInherit`), for every non-empty
  coherent chain.
  * (2a) A countable set of indices is cofinal. The chain is bounded by the direct limit of an
    increasing cofinal sequence (`exists_seq_limit`). Its parametrisations `ψ n` are built one at
    a time with bounded images (`exists_strictMonoOn_extend`, right and left), so each extension
    has room. They are continuous because strictly monotone with ordconnected image
    (`continuousOn_of_strictMonoOn_ordConnected`).
  * (2b) Otherwise, from some member on every morphism is onto, and that member is the bound.
    Right excesses cannot be cofinal (`false_of_rightExcess`), nor left ones
    (`false_of_leftExcess`, by `t ↦ -t`).
* **Maximal is inextensible** (the target's (3), `tailFreeMor_inextensible_of_isMaximal`). A
  strict extension is trimmed of its constant end pieces by a monotone retraction
  (`exists_tailFree_retraction`, T1). The retraction keeps the maximal curve a sub-arc, so
  maximality maps the trimmed extension back, and its image does not grow.
* **The start** (the target's (4)): the given curve, trimmed the same way.

## The proof of (2b), with the audit's corrections

The corrections are those of `lean-causal/campaign/T-abs-omega-one-constant/AUDIT-1.json`,
finding 2. Suppose right excesses are cofinal.

1. **Recursion.** By recursion on the ordinals, each `seq α` is two right-excess steps above an
   upper bound of the countably many `seq β`, `β < α` (every countable set of indices is
   bounded). One step may add a single point (a curve over `[0, 1)` closed by its limit); two
   steps leave the excess `E α` of `seq (α + 1)` over `seq α` with two points. `E α` is a final
   segment of the interval of `seq (α + 1)`.
2. **The maps.** For each rational `q`, `g q α` is the value of the curve of `seq (α + 1)` at
   `q`, if `q ∈ E α`, else at a fixed point of `E α`. At a limit `λ`, `g q λ` is the value at
   the supremum of the earlier parameters, all carried into the interval of `seq (λ + 1)`. These
   maps are continuous at limits (a squeeze), so all are constant on one tail `[γ₀, ω₁)`
   (`exists_lt_omega_one_forall_eq_family`).
3. **The contradiction.** Take a limit `λ ≥ γ₀` (`exists_isSuccLimit_ge_lt_omega_one`). Then
   `g q (λ + 1) = g q λ` for every `q`, and the right side does not depend on `q`. So the curve
   of `seq (λ + 2)` takes one value at the rationals of `E (λ + 1)`, hence on all of it (density,
   continuity, closed points). That final segment has two points, against tail-freeness.

The condition read is at `λ + 1` with `λ ≥ γ₀`: the audit's "α + 1 ≥ γ". The dense family is the
rationals of the excess.

## Hypothesis checklist

| the target's statement | here |
|---|---|
| `M` T1 | ✓ `[T1Space M]`. It closes the constancy sets in the trimming (`exists_tailFree_retraction`), and it is used in (2b) twice: by the `ω₁` lemma and in the density step (`eq_of_continuousOn_of_rat`) |
| `M` second countable | ✓ `[SecondCountableTopology M]`, used in (2b) only, through `exists_lt_omega_one_forall_eq_family` |
| "with no other hypothesis" | ✓ no T2, no causality (`IsCausal`), no time function, no causal arc-connectedness, no local compactness; any causality |
| `CurvesExtendOn W` for every open `W` | ✓ `curvesExtendOn_of_t1_secondCountable C W`; ⚠ weakened (stronger theorem): any interval, not only segments (`exists_inextensible_of_t1_secondCountable`) |
| hence `CurvesExtend` | ✓ `curvesExtend_of_t1_secondCountable`, through `curvesExtendOn_top` |
| the definitions | ✓ the library's: `Causality.CurvesExtendOn` (`Causal/CBG/CausalConvex.lean:153`), `Causality.CurvesExtend` (`Causal/CauchyExtension.lean:82`), `Causality.Inextensible` (`Causal/Inextensible.lean:184`, DEC-11, DEC-13) |

## SCOPE (disclosed)

* **Nothing marked**: no paper, no label.
* **Sharpness is not formalized.**
  * Second countability: the long ray is the conjectured counterexample (Hausdorff, not second
    countable; `Causal/CurvesExtend.lean:90–99`, not formalized).
  * T1: whether it can be weakened to T0 is not examined. In a finite space `CurvesExtend` holds
    trivially (a curve of maximal image is inextensible); argued, not formalized.
* **The inextensible curve comes from Zorn** (choice, through towers: no uniqueness of
  reparametrisations is needed, kb/0094). It is not unique, and its interval is not normalised.
* **Library prose that this module makes outdated** (not edited here, a frozen strict library):
  * the docstring of `Causality.CurvesExtend` ("the library does not prove it for topological
    spacetimes", `Causal/CauchyExtension.lean:81`);
  * the SCOPE of `Causal.CurvesExtend` ("whether `CurvesExtend` holds in every strongly causal
    spacetime is open here", `Causal/CurvesExtend.lean:97–98`).

  They are for the master to amend at graduation.
* `continuousOn_of_strictMonoOn_ordConnected` is the ETT-layer twin, with an ordconnected domain,
  of `Causal.Flat.continuousOn_of_strictMonoOn` (`Causal/Flat/Develop.lean:1614`, a model module
  this layer may not import). The name is distinct on purpose.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology Function TopologicalSpace

universe u

/-! ## 1. Strictly monotone maps between real intervals -/

section RealIntervals

theorem continuousOn_of_strictMonoOn_ordConnected {f : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hf : StrictMonoOn f s) (himg : (f '' s).OrdConnected) : ContinuousOn f s := by
  haveI := hs
  haveI := himg
  rw [continuousOn_iff_continuous_restrict]
  have h : s.restrict f = fun x => ((hf.orderIso f s x : f '' s) : ℝ) := by
    funext x; rfl
  rw [h]
  exact continuous_subtype_val.comp (hf.orderIso f s).continuous

theorem ordConnected_image_of_strictMonoOn {f : ℝ → ℝ} {s K : Set ℝ} (hf : StrictMonoOn f s)
    (himg : (f '' s).OrdConnected) (hK : K ⊆ s) (hKo : K.OrdConnected) :
    (f '' K).OrdConnected := by
  refine ⟨?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
  obtain ⟨c, hc, rfl⟩ := himg.out (mem_image_of_mem f (hK ha)) (mem_image_of_mem f (hK hb)) hz
  have h1 : a ≤ c := (hf.le_iff_le (hK ha) hc).1 hz.1
  have h2 : c ≤ b := (hf.le_iff_le hc (hK hb)).1 hz.2
  exact ⟨c, hKo.out ha hb ⟨h1, h2⟩, rfl⟩

/-- The inverse of a strictly monotone map, on its image, is strictly monotone. -/
theorem strictMonoOn_invFunOn {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s) :
    StrictMonoOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  rw [hf.injOn.leftInvOn_invFunOn ha, hf.injOn.leftInvOn_invFunOn hb]
  exact (hf.lt_iff_lt ha hb).1 hab

/-- The image of `t ↦ -F (-t)` on `-X` is ordconnected when that of `F` on `X` is. -/
theorem ordConnected_image_neg {F : ℝ → ℝ} {X : Set ℝ} (h : (F '' X).OrdConnected) :
    ((fun t => -F (-t)) '' (Neg.neg ⁻¹' X)).OrdConnected := by
  refine ⟨?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
  obtain ⟨c, hc, hcz⟩ := h.out (mem_image_of_mem F hb) (mem_image_of_mem F ha)
    (⟨by linarith [hz.2], by linarith [hz.1]⟩ : -z ∈ Icc (F (-b)) (F (-a)))
  refine ⟨-c, by simpa using hc, ?_⟩
  simp only [neg_neg, hcz]

theorem exists_strictMonoOn_extend_right {A B : Set ℝ} {h : ℝ → ℝ} {lo hi : ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hB : B.OrdConnected)
    (hlow : ∀ a ∈ A, ∀ t ∈ B, t ≤ a → t ∈ A) (hh : StrictMonoOn h A)
    (himg : (h '' A).OrdConnected) (hbd : h '' A ⊆ Icc lo hi) :
    ∃ h' : ℝ → ℝ, StrictMonoOn h' B ∧ (h' '' B).OrdConnected ∧ h' '' B ⊆ Icc lo (hi + 1) ∧
      EqOn h' h A := by
  classical
  by_cases hBA : B ⊆ A
  · have hEq : B = A := Subset.antisymm hBA hAB
    subst hEq
    exact ⟨h, hh, himg, hbd.trans (Icc_subset_Icc le_rfl (by linarith)), fun _ _ => rfl⟩
  obtain ⟨t₀, ht₀B, ht₀A⟩ := not_subset.1 hBA
  have hbddA : BddAbove A :=
    ⟨t₀, fun a ha => le_of_not_ge fun h' => ht₀A (hlow a ha t₀ ht₀B h')⟩
  have hne : (h '' A).Nonempty := hA.image h
  have hbddh : BddAbove (h '' A) := ⟨hi, fun y hy => (hbd hy).2⟩
  set β := sSup A with hβ
  set S := sSup (h '' A) with hS
  have hβge : ∀ t ∈ B, t ∉ A → β ≤ t := fun t ht htA =>
    csSup_le hA fun a ha => le_of_not_ge fun h' => htA (hlow a ha t ht h')
  have hle_β : ∀ a ∈ A, a ≤ β := fun a ha => le_csSup hbddA ha
  have hle_S : ∀ a ∈ A, h a ≤ S := fun a ha => le_csSup hbddh (mem_image_of_mem h ha)
  set g : ℝ → ℝ := fun x => x / (1 + x) with hg
  have hg0 : ∀ x, 0 ≤ x → 0 ≤ g x := fun x hx => div_nonneg hx (by linarith)
  have hg1 : ∀ x, 0 ≤ x → g x < 1 := fun x hx => by
    simp only [hg]; rw [div_lt_one (by linarith)]; linarith
  have hgz : g 0 = 0 := by simp [hg]
  have hgmono : ∀ x y, 0 ≤ x → x < y → g x < g y := fun x y hx hxy => by
    simp only [hg]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hgpos : ∀ x, 0 < x → 0 < g x := fun x hx => by
    have := hgmono 0 x le_rfl hx; rwa [hgz] at this
  have hginv : ∀ u, u < 1 → g (u / (1 - u)) = u := fun u hu => by
    simp only [hg]
    have h1 : (1 - u) ≠ 0 := by linarith
    field_simp
    ring
  set h' : ℝ → ℝ := fun t => if t ∈ A then h t else S + g (t - β) with hh'
  have hin : ∀ t ∈ A, h' t = h t := fun t ht => if_pos ht
  have hout : ∀ t, t ∉ A → h' t = S + g (t - β) := fun t ht => if_neg ht
  have hmono : StrictMonoOn h' B := by
    intro t ht t' ht' htt'
    by_cases h1 : t ∈ A <;> by_cases h2 : t' ∈ A
    · rw [hin t h1, hin t' h2]; exact hh h1 h2 htt'
    · rw [hin t h1, hout t' h2]
      rcases (hβge t' ht' h2).lt_or_eq with hlt' | heq
      · have := hgpos (t' - β) (by linarith); linarith [hle_S t h1]
      · have htβ : t < β := lt_of_lt_of_eq htt' heq.symm
        obtain ⟨a, ha, hta⟩ := exists_lt_of_lt_csSup hA htβ
        have h3 := hh h1 ha hta
        have h4 := hle_S a ha
        rw [← heq, sub_self, hgz]
        linarith
    · exact absurd (hlow t' h2 t ht htt'.le) h1
    · rw [hout t h1, hout t' h2]
      have := hgmono (t - β) (t' - β) (by linarith [hβge t ht h1]) (by linarith)
      linarith
  have hS_lo : lo ≤ S := by
    obtain ⟨a, ha⟩ := hA
    exact (hbd (mem_image_of_mem h ha)).1.trans (hle_S a ha)
  have hS_hi : S ≤ hi := csSup_le hne fun y hy => (hbd hy).2
  have hsub : h' '' B ⊆ Icc lo (hi + 1) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases h1 : t ∈ A
    · rw [hin t h1]
      have := hbd (mem_image_of_mem h h1)
      exact ⟨this.1, by linarith [this.2]⟩
    · rw [hout t h1]
      have h2 := hg0 (t - β) (by linarith [hβge t ht h1])
      have h3 := hg1 (t - β) (by linarith [hβge t ht h1])
      constructor <;> linarith
  have hocon : (h' '' B).OrdConnected := by
    refine ⟨?_⟩
    rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩ z ⟨hz1, hz2⟩
    by_cases hzS : z ≤ S
    · by_cases h1 : t₁ ∈ A
      · rw [hin t₁ h1] at hz1
        rcases hzS.lt_or_eq with hzS' | hzS'
        · obtain ⟨_, ⟨a, ha, rfl⟩, hza⟩ := exists_lt_of_lt_csSup hne hzS'
          obtain ⟨a', ha', hz⟩ := himg.out (mem_image_of_mem h h1) (mem_image_of_mem h ha)
            ⟨hz1, hza.le⟩
          exact ⟨a', hAB ha', by rw [hin a' ha']; exact hz⟩
        · by_cases hSmem : S ∈ h '' A
          · obtain ⟨a', ha', hz⟩ := hSmem
            exact ⟨a', hAB ha', by rw [hin a' ha', hz, hzS']⟩
          · have h2 : t₂ ∉ A := by
              intro h2
              rw [hin t₂ h2] at hz2
              exact hSmem ⟨t₂, h2, le_antisymm (hle_S t₂ h2) (hzS' ▸ hz2)⟩
            have hβA : β ∉ A := by
              intro hβA
              apply hSmem
              refine ⟨β, hβA, le_antisymm (hle_S β hβA) (csSup_le hne ?_)⟩
              rintro _ ⟨a, ha, rfl⟩
              exact hh.monotoneOn ha hβA (hle_β a ha)
            have hβB : β ∈ B := hB.out ht₁ ht₂ ⟨hle_β t₁ h1, hβge t₂ ht₂ h2⟩
            exact ⟨β, hβB, by rw [hout β hβA, sub_self, hgz, add_zero, hzS']⟩
      · rw [hout t₁ h1] at hz1
        have := hg0 (t₁ - β) (by linarith [hβge t₁ ht₁ h1])
        exact ⟨t₁, ht₁, by rw [hout t₁ h1]; linarith⟩
    · push Not at hzS
      have h2 : t₂ ∉ A := fun h2 => by
        rw [hin t₂ h2] at hz2
        linarith [hle_S t₂ h2]
      rw [hout t₂ h2] at hz2
      have hβt₂ := hβge t₂ ht₂ h2
      have hu0 : 0 < z - S := by linarith
      have hu1 : z - S < 1 := by have := hg1 (t₂ - β) (by linarith); linarith
      have hx0 : 0 < (z - S) / (1 - (z - S)) := div_pos hu0 (by linarith)
      have hgx := hginv (z - S) hu1
      have hxle : (z - S) / (1 - (z - S)) ≤ t₂ - β := by
        by_contra hcon
        push Not at hcon
        have := hgmono (t₂ - β) _ (by linarith) hcon
        linarith
      obtain ⟨a, ha⟩ := hA
      have htB : β + (z - S) / (1 - (z - S)) ∈ B :=
        hB.out (hAB ha) ht₂ ⟨by linarith [hle_β a ha], by linarith⟩
      have htA : β + (z - S) / (1 - (z - S)) ∉ A := fun hA' => by linarith [hle_β _ hA']
      refine ⟨_, htB, ?_⟩
      rw [hout _ htA, show β + (z - S) / (1 - (z - S)) - β = (z - S) / (1 - (z - S)) by ring, hgx]
      ring
  exact ⟨h', hmono, hocon, hsub, fun t ht => hin t ht⟩

theorem exists_strictMonoOn_extend_left {A B : Set ℝ} {h : ℝ → ℝ} {lo hi : ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hB : B.OrdConnected)
    (hup : ∀ a ∈ A, ∀ t ∈ B, a ≤ t → t ∈ A) (hh : StrictMonoOn h A)
    (himg : (h '' A).OrdConnected) (hbd : h '' A ⊆ Icc lo hi) :
    ∃ h' : ℝ → ℝ, StrictMonoOn h' B ∧ (h' '' B).OrdConnected ∧ h' '' B ⊆ Icc (lo - 1) hi ∧
      EqOn h' h A := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨h₁, hm, hoc, hsub, heq⟩ := exists_strictMonoOn_extend_right (A := Neg.neg ⁻¹' A)
    (B := Neg.neg ⁻¹' B) (h := fun t => -h (-t)) (lo := -hi) (hi := -lo)
    ⟨-a₀, by simpa using ha₀⟩ (fun t ht => hAB ht)
    ⟨fun x hx y hy z hz => hB.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
    (fun a ha t ht hta => hup (-a) ha (-t) ht (neg_le_neg hta))
    (fun s hs t ht hst => neg_lt_neg (hh ht hs (neg_lt_neg hst)))
    (ordConnected_image_neg himg)
    (by
      rintro _ ⟨t, ht, rfl⟩
      have := hbd (mem_image_of_mem h ht)
      exact ⟨neg_le_neg this.2, neg_le_neg this.1⟩)
  refine ⟨fun t => -h₁ (-t), fun s hs t ht hst => neg_lt_neg (hm
    (show -t ∈ Neg.neg ⁻¹' B by simpa using ht) (show -s ∈ Neg.neg ⁻¹' B by simpa using hs)
    (neg_lt_neg hst)), ?_, ?_, fun t ht => ?_⟩
  · have := ordConnected_image_neg hoc
    have e : Neg.neg ⁻¹' (Neg.neg ⁻¹' B) = B := by ext; simp
    rwa [e] at this
  · rintro _ ⟨t, ht, rfl⟩
    have := hsub (mem_image_of_mem h₁ (show -t ∈ Neg.neg ⁻¹' B by simpa using ht))
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · have := heq (show -t ∈ Neg.neg ⁻¹' A by simpa using ht)
    simp only [neg_neg] at this
    simp only [this, neg_neg]

theorem exists_strictMonoOn_extend {A B : Set ℝ} {h : ℝ → ℝ} {lo hi : ℝ}
    (hA : A.Nonempty) (hAo : A.OrdConnected) (hAB : A ⊆ B) (hB : B.OrdConnected)
    (hh : StrictMonoOn h A) (himg : (h '' A).OrdConnected) (hbd : h '' A ⊆ Icc lo hi) :
    ∃ h' : ℝ → ℝ, StrictMonoOn h' B ∧ (h' '' B).OrdConnected ∧
      h' '' B ⊆ Icc (lo - 1) (hi + 1) ∧ EqOn h' h A := by
  set B₁ := {t ∈ B | ∃ a ∈ A, a ≤ t} with hB₁
  have hAB₁ : A ⊆ B₁ := fun a ha => ⟨hAB ha, a, ha, le_rfl⟩
  have hB₁o : B₁.OrdConnected :=
    ⟨fun x hx y hy z hz => ⟨hB.out hx.1 hy.1 hz, let ⟨a, ha, hax⟩ := hx.2; ⟨a, ha, hax.trans hz.1⟩⟩⟩
  obtain ⟨h₁, hm₁, ho₁, hs₁, he₁⟩ := exists_strictMonoOn_extend_right hA hAB₁ hB₁o
    (fun a ha t ht hta => let ⟨a', ha', ha't⟩ := ht.2; hAo.out ha' ha ⟨ha't, hta⟩) hh himg hbd
  obtain ⟨h₂, hm₂, ho₂, hs₂, he₂⟩ := exists_strictMonoOn_extend_left (hA.mono hAB₁)
    (fun t ht => ht.1) hB
    (fun a ha t ht hat => ⟨ht, let ⟨a', ha', ha'a⟩ := ha.2; ⟨a', ha', ha'a.trans hat⟩⟩) hm₁ ho₁ hs₁
  exact ⟨h₂, hm₂, ho₂, hs₂, fun t ht => (he₂ (hAB₁ ht)).trans (he₁ ht)⟩

end RealIntervals

/-! ## 2. Tail-free curves -/

section TailFree

variable {M : Type u} [TopologicalSpace M]

def TailFree {α : Type*} (I : Set ℝ) (c : ℝ → α) : Prop :=
  (∀ t ∈ I, ∀ t' ∈ I, t < t' → ∃ s ∈ I, t ≤ s ∧ c s ≠ c t) ∧
    ∀ t ∈ I, ∀ t' ∈ I, t' < t → ∃ s ∈ I, s ≤ t ∧ c s ≠ c t

theorem eq_of_continuousOn_of_rat [T1Space M] {f : ℝ → M} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {y : M} (hq : ∀ q : ℚ, (q : ℝ) ∈ Ioo a b → f q = y) :
    ∀ x ∈ Icc a b, f x = y := by
  have hcl : IsClosed (Icc a b ∩ f ⁻¹' {y}) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : Ioo a b ∩ range ((↑) : ℚ → ℝ) ⊆ Icc a b ∩ f ⁻¹' {y} := by
    rintro x ⟨hx, q, rfl⟩
    exact ⟨Ioo_subset_Icc_self hx, hq q hx⟩
  have h1 : Ioo a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  have h2 : closure (Ioo a b) ⊆ Icc a b ∩ f ⁻¹' {y} :=
    closure_minimal (h1.trans (closure_minimal hsub hcl)) hcl
  rw [closure_Ioo hab.ne] at h2
  exact fun x hx => (h2 hx).2

/-- The image of a sub-interval under a monotone retraction onto a sub-interval is ordconnected. -/
theorem ordConnected_image_of_retraction {I I₀ J : Set ℝ} {ρ : ℝ → ℝ} (hI₀ : I₀ ⊆ I)
    (hI₀o : I₀.OrdConnected) (hρm : MapsTo ρ I I₀) (hρmono : MonotoneOn ρ I)
    (hρid : ∀ t ∈ I₀, ρ t = t) (hJ : J ⊆ I) (hJo : J.OrdConnected) : (ρ '' J).OrdConnected := by
  refine ⟨?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
  rcases le_or_gt a b with hab | hab
  · have hzI₀ : z ∈ I₀ := hI₀o.out (hρm (hJ ha)) (hρm (hJ hb)) hz
    have hzI : z ∈ I := hI₀ hzI₀
    rcases lt_or_ge z a with hza | haz
    · refine ⟨a, ha, le_antisymm hz.1 ?_⟩
      calc z = ρ z := (hρid z hzI₀).symm
        _ ≤ ρ a := hρmono hzI (hJ ha) hza.le
    rcases le_or_gt z b with hzb | hbz
    · exact ⟨z, hJo.out ha hb ⟨haz, hzb⟩, hρid z hzI₀⟩
    · refine ⟨b, hb, le_antisymm ?_ hz.2⟩
      calc ρ b ≤ ρ z := hρmono (hJ hb) hzI hbz.le
        _ = z := hρid z hzI₀
  · have := hρmono (hJ hb) (hJ ha) hab.le
    exact ⟨a, ha, le_antisymm hz.1 (hz.2.trans this)⟩

theorem exists_tailFree_retraction [T1Space M] {I : Set ℝ} {c : ℝ → M} (hI : I.Nonempty)
    (hIo : I.OrdConnected) (hc : ∀ a ∈ I, ∀ b ∈ I, ContinuousOn c (Icc a b)) :
    ∃ I₀ ⊆ I, ∃ ρ : ℝ → ℝ, I₀.Nonempty ∧ I₀.OrdConnected ∧ TailFree I₀ c ∧ MapsTo ρ I I₀ ∧
      MonotoneOn ρ I ∧ (∀ t ∈ I₀, ρ t = t) ∧ (∀ t ∈ I, c (ρ t) = c t) ∧
      ∀ t ∈ I, ∀ t' ∈ I, t < t' → ρ t = ρ t' →
        (∀ s ∈ I, t ≤ s → c s = c t) ∨ ∀ s ∈ I, s ≤ t' → c s = c t' := by
  classical
  by_cases hconst : ∀ s ∈ I, ∀ s' ∈ I, c s = c s'
  · obtain ⟨t₀, ht₀⟩ := hI
    refine ⟨{t₀}, singleton_subset_iff.2 ht₀, fun _ => t₀, singleton_nonempty _,
      ordConnected_singleton, ⟨?_, ?_⟩, fun _ _ => rfl, fun _ _ _ _ _ => le_rfl,
      fun t ht => ht.symm, fun t ht => hconst t₀ ht₀ t ht, ?_⟩
    · intro t ht t' ht' h
      rw [mem_singleton_iff] at ht ht'
      exact absurd (ht ▸ ht' ▸ h) (lt_irrefl _)
    · intro t ht t' ht' h
      rw [mem_singleton_iff] at ht ht'
      exact absurd (ht ▸ ht' ▸ h) (lt_irrefl _)
    · intro t ht _ _ _ _
      exact Or.inl fun s hs _ => hconst s hs t ht
  push Not at hconst
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hσ⟩ := hconst
  set R := {t ∈ I | ∀ s ∈ I, t ≤ s → c s = c t} with hR
  set L := {t ∈ I | ∀ s ∈ I, s ≤ t → c s = c t} with hL
  have hRup : ∀ t ∈ R, ∀ s ∈ I, t ≤ s → s ∈ R := fun t ht s hs hts =>
    ⟨hs, fun s' hs' hss' => (ht.2 s' hs' (hts.trans hss')).trans (ht.2 s hs hts).symm⟩
  have hLdown : ∀ t ∈ L, ∀ s ∈ I, s ≤ t → s ∈ L := fun t ht s hs hst =>
    ⟨hs, fun s' hs' hs's => (ht.2 s' hs' (hs's.trans hst)).trans (ht.2 s hs hst).symm⟩
  have hRval : ∀ t ∈ R, ∀ t' ∈ R, c t = c t' := fun t ht t' ht' => by
    rcases le_total t t' with h | h
    · exact (ht.2 t' ht'.1 h).symm
    · exact ht'.2 t ht.1 h
  have hLval : ∀ t ∈ L, ∀ t' ∈ L, c t = c t' := fun t ht t' ht' => by
    rcases le_total t t' with h | h
    · exact ht'.2 t ht.1 h
    · exact (ht.2 t' ht'.1 h).symm
  -- not every point is above a point of `R`, nor below a point of `L`
  have hRnot : ∃ s₀ ∈ I, ∀ r ∈ R, s₀ < r := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r₁, hr₁, h₁⟩ := hcon σ₁ hσ₁
    obtain ⟨r₂, hr₂, h₂⟩ := hcon σ₂ hσ₂
    exact hσ ((hRval _ (hRup r₁ hr₁ σ₁ hσ₁ h₁) _ (hRup r₂ hr₂ σ₂ hσ₂ h₂)))
  have hLnot : ∃ s₀ ∈ I, ∀ l ∈ L, l < s₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l₁, hl₁, h₁⟩ := hcon σ₁ hσ₁
    obtain ⟨l₂, hl₂, h₂⟩ := hcon σ₂ hσ₂
    exact hσ ((hLval _ (hLdown l₁ hl₁ σ₁ hσ₁ h₁) _ (hLdown l₂ hl₂ σ₂ hσ₂ h₂)))
  obtain ⟨sR, hsR, hsR'⟩ := hRnot
  obtain ⟨sL, hsL, hsL'⟩ := hLnot
  have hRbdd : BddBelow R := ⟨sR, fun r hr => (hsR' r hr).le⟩
  have hLbdd : BddAbove L := ⟨sL, fun l hl => (hsL' l hl).le⟩
  -- the least point of `R` and the greatest of `L`
  have hRmin : ∀ r ∈ R, sInf R ∈ R ∧ ∀ r' ∈ R, sInf R ≤ r' := by
    intro r₁ hr₁
    have hRne : R.Nonempty := ⟨r₁, hr₁⟩
    have hle : ∀ r' ∈ R, sInf R ≤ r' := fun r' hr' => csInf_le hRbdd hr'
    have hge : sR ≤ sInf R := le_csInf hRne fun r hr => (hsR' r hr).le
    have hmemI : sInf R ∈ I := hIo.out hsR hr₁.1 ⟨hge, hle r₁ hr₁⟩
    -- `c = c r₁` beyond `sInf R`
    have habove : ∀ s ∈ I, sInf R < s → c s = c r₁ := fun s hs hlt => by
      obtain ⟨r, hr, hrs⟩ := exists_lt_of_csInf_lt hRne hlt
      exact hRval _ (hRup r hr s hs hrs.le) _ hr₁
    have hat : c (sInf R) = c r₁ := by
      rcases (hle r₁ hr₁).lt_or_eq with hlt | heq
      · have hcw : ContinuousWithinAt c (Ioc (sInf R) r₁) (sInf R) :=
          ((hc _ hmemI _ hr₁.1) (sInf R) ⟨le_rfl, hlt.le⟩).mono Ioc_subset_Icc_self
        have hcl : sInf R ∈ closure (Ioc (sInf R) r₁) := by
          rw [closure_Ioc hlt.ne]; exact ⟨le_rfl, hlt.le⟩
        have hmem := hcw.mem_closure_image hcl
        have himg : c '' Ioc (sInf R) r₁ ⊆ {c r₁} := by
          rintro _ ⟨s, hs, rfl⟩
          exact habove s (hIo.out hmemI hr₁.1 (Ioc_subset_Icc_self hs)) hs.1
        have := closure_mono himg hmem
        rwa [closure_singleton] at this
      · rw [heq]
    refine ⟨⟨hmemI, fun s hs hle' => ?_⟩, hle⟩
    rcases hle'.lt_or_eq with hlt | heq
    · rw [habove s hs hlt, hat]
    · rw [heq]
  have hLmax : ∀ l ∈ L, sSup L ∈ L ∧ ∀ l' ∈ L, l' ≤ sSup L := by
    intro l₁ hl₁
    have hLne : L.Nonempty := ⟨l₁, hl₁⟩
    have hge : ∀ l' ∈ L, l' ≤ sSup L := fun l' hl' => le_csSup hLbdd hl'
    have hle : sSup L ≤ sL := csSup_le hLne fun l hl => (hsL' l hl).le
    have hmemI : sSup L ∈ I := hIo.out hl₁.1 hsL ⟨hge l₁ hl₁, hle⟩
    have hbelow : ∀ s ∈ I, s < sSup L → c s = c l₁ := fun s hs hlt => by
      obtain ⟨l, hl, hsl⟩ := exists_lt_of_lt_csSup hLne hlt
      exact hLval _ (hLdown l hl s hs hsl.le) _ hl₁
    have hat : c (sSup L) = c l₁ := by
      rcases (hge l₁ hl₁).lt_or_eq with hlt | heq
      · have hcw : ContinuousWithinAt c (Ico l₁ (sSup L)) (sSup L) :=
          ((hc _ hl₁.1 _ hmemI) (sSup L) ⟨hlt.le, le_rfl⟩).mono Ico_subset_Icc_self
        have hcl : sSup L ∈ closure (Ico l₁ (sSup L)) := by
          rw [closure_Ico hlt.ne]; exact ⟨hlt.le, le_rfl⟩
        have hmem := hcw.mem_closure_image hcl
        have himg : c '' Ico l₁ (sSup L) ⊆ {c l₁} := by
          rintro _ ⟨s, hs, rfl⟩
          exact hbelow s (hIo.out hl₁.1 hmemI (Ico_subset_Icc_self hs)) hs.2
        have := closure_mono himg hmem
        rwa [closure_singleton] at this
      · rw [← heq]
    refine ⟨⟨hmemI, fun s hs hle' => ?_⟩, hge⟩
    rcases hle'.lt_or_eq with hlt | heq
    · rw [hbelow s hs hlt, hat]
    · rw [heq]
  -- `L` lies strictly below `R`
  have hLR : ∀ l ∈ L, ∀ r ∈ R, l < r := by
    intro l hl r hr
    by_contra hcon
    push Not at hcon
    apply hσ
    have key : ∀ s ∈ I, c s = c r := fun s hs => by
      rcases le_total r s with h | h
      · exact hr.2 s hs h
      · exact (hl.2 s hs (h.trans hcon)).trans (hl.2 r hr.1 hcon).symm
    rw [key σ₁ hσ₁, key σ₂ hσ₂]
  set I₀ := {t ∈ I | (∀ r ∈ R, t ≤ r) ∧ ∀ l ∈ L, l ≤ t} with hI₀
  set ρ : ℝ → ℝ := fun t => if t ∈ R then sInf R else if t ∈ L then sSup L else t with hρ
  have hI₀I : I₀ ⊆ I := fun t ht => ht.1
  have hRI₀ : ∀ r ∈ R, sInf R ∈ I₀ := fun r hr =>
    ⟨(hRmin r hr).1.1, (hRmin r hr).2, fun l hl => (hLR l hl _ (hRmin r hr).1).le⟩
  have hLI₀ : ∀ l ∈ L, sSup L ∈ I₀ := fun l hl =>
    ⟨(hLmax l hl).1.1, fun r hr => (hLR _ (hLmax l hl).1 r hr).le, (hLmax l hl).2⟩
  have hmid : ∀ t ∈ I, t ∉ R → t ∉ L → t ∈ I₀ := fun t ht htR htL =>
    ⟨ht, fun r hr => le_of_not_gt fun h => htR (hRup r hr t ht h.le),
      fun l hl => le_of_not_gt fun h => htL (hLdown l hl t ht h.le)⟩
  have hρR : ∀ t ∈ R, ρ t = sInf R := fun t ht => if_pos ht
  have hρL : ∀ t, t ∉ R → t ∈ L → ρ t = sSup L := fun t h1 h2 => by
    simp only [hρ, if_neg h1, if_pos h2]
  have hρN : ∀ t, t ∉ R → t ∉ L → ρ t = t := fun t h1 h2 => by
    simp only [hρ, if_neg h1, if_neg h2]
  have hmaps : MapsTo ρ I I₀ := by
    intro t ht
    by_cases h1 : t ∈ R
    · rw [hρR t h1]; exact hRI₀ t h1
    by_cases h2 : t ∈ L
    · rw [hρL t h1 h2]; exact hLI₀ t h2
    · rw [hρN t h1 h2]; exact hmid t ht h1 h2
  have hval : ∀ t ∈ I, c (ρ t) = c t := by
    intro t ht
    by_cases h1 : t ∈ R
    · rw [hρR t h1]; exact hRval _ (hRmin t h1).1 _ h1
    by_cases h2 : t ∈ L
    · rw [hρL t h1 h2]; exact hLval _ (hLmax t h2).1 _ h2
    · rw [hρN t h1 h2]
  have hid : ∀ t ∈ I₀, ρ t = t := by
    intro t ht
    by_cases h1 : t ∈ R
    · rw [hρR t h1]; exact le_antisymm ((hRmin t h1).2 t h1) (ht.2.1 _ (hRmin t h1).1)
    by_cases h2 : t ∈ L
    · rw [hρL t h1 h2]; exact le_antisymm (ht.2.2 _ (hLmax t h2).1) ((hLmax t h2).2 t h2)
    · rw [hρN t h1 h2]
  have hmono : MonotoneOn ρ I := by
    intro s hs s' hs' hss'
    by_cases h1 : s' ∈ R
    · rw [hρR s' h1]; exact (hmaps hs).2.1 _ (hRmin s' h1).1
    have h1' : s ∉ R := fun h => h1 (hRup s h s' hs' hss')
    by_cases h2 : s ∈ L
    · rw [hρL s h1' h2]; exact (hmaps hs').2.2 _ (hLmax s h2).1
    have h2' : s' ∉ L := fun h => h2 (hLdown s' h s hs hss')
    rw [hρN s h1' h2, hρN s' h1 h2']
    exact hss'
  have hkp : ∀ t ∈ I, ∀ t' ∈ I, t < t' → ρ t = ρ t' →
      (∀ s ∈ I, t ≤ s → c s = c t) ∨ ∀ s ∈ I, s ≤ t' → c s = c t' := by
    intro t ht t' ht' htt' he
    by_cases h1 : t ∈ R
    · exact Or.inl h1.2
    by_cases h2 : t' ∈ L
    · exact Or.inr h2.2
    exfalso
    by_cases h3 : t' ∈ R
    · rw [hρR t' h3] at he
      by_cases h4 : t ∈ L
      · rw [hρL t h1 h4] at he
        exact (hLR _ (hLmax t h4).1 _ (hRmin t' h3).1).ne he
      · rw [hρN t h1 h4] at he
        exact h1 (he ▸ (hRmin t' h3).1)
    · rw [hρN t' h3 h2] at he
      by_cases h4 : t ∈ L
      · rw [hρL t h1 h4] at he
        exact h2 (he ▸ (hLmax t h4).1)
      · rw [hρN t h1 h4] at he
        exact htt'.ne he
  have hne₀ : I₀.Nonempty := ⟨ρ σ₁, hmaps hσ₁⟩
  have ho₀ : I₀.OrdConnected := ⟨fun x hx y hy z hz => ⟨hIo.out hx.1 hy.1 hz,
    fun r hr => hz.2.trans (hy.2.1 r hr), fun l hl => (hx.2.2 l hl).trans hz.1⟩⟩
  have htf₀ : TailFree I₀ c := by
    constructor
    · intro t ht t' ht' htt'
      have htR : t ∉ R := fun h => absurd (ht'.2.1 t h) (not_le.2 htt')
      have : ¬ ∀ s ∈ I, t ≤ s → c s = c t := fun h => htR ⟨ht.1, h⟩
      push Not at this
      obtain ⟨s, hs, hts, hcs⟩ := this
      refine ⟨ρ s, hmaps hs, ?_, by rw [hval s hs]; exact hcs⟩
      calc t = ρ t := (hid t ht).symm
        _ ≤ ρ s := hmono ht.1 hs hts
    · intro t ht t' ht' htt'
      have htL : t ∉ L := fun h => absurd (ht'.2.2 t h) (not_le.2 htt')
      have : ¬ ∀ s ∈ I, s ≤ t → c s = c t := fun h => htL ⟨ht.1, h⟩
      push Not at this
      obtain ⟨s, hs, hst, hcs⟩ := this
      refine ⟨ρ s, hmaps hs, ?_, by rw [hval s hs]; exact hcs⟩
      calc ρ s ≤ ρ t := hmono hs ht.1 hst
        _ = t := hid t ht
  exact ⟨I₀, hI₀I, ρ, hne₀, ho₀, htf₀, hmaps, hmono, hid, hval, hkp⟩

end TailFree

/-! ## 3. The direct limit of a sequence of extensions -/

section Sequence

variable {M : Type u} [TopologicalSpace M]

/-- **A sequence of tail-free curves, each a reparametrised sub-arc of the next, has a direct
limit**: a tail-free causal curve `γ` over an interval `J` with compatible strictly monotone
`ψ n : I n → J`, onto sub-intervals, `γ ∘ ψ n = c n`. The `ψ n` are built one at a time
(`exists_strictMonoOn_extend`), with bounded images, so that each extension has room. -/
theorem exists_seq_limit {C : Causality M} {W : Opens M} {I : ℕ → Set ℝ} {c : ℕ → ℝ → M}
    {φ : ℕ → ℝ → ℝ} (hc : ∀ n, C.CausalCurveIn W (I n) (c n)) (htf : ∀ n, TailFree (I n) (c n))
    (hφ : ∀ n, StrictMonoOn (φ n) (I n)) (hφm : ∀ n, MapsTo (φ n) (I n) (I (n + 1)))
    (hφo : ∀ n, (φ n '' I n).OrdConnected) (hφc : ∀ n, ∀ t ∈ I n, c (n + 1) (φ n t) = c n t) :
    ∃ (J : Set ℝ) (γ : ℝ → M) (ψ : ℕ → ℝ → ℝ), C.CausalCurveIn W J γ ∧ TailFree J γ ∧
      (∀ n, StrictMonoOn (ψ n) (I n)) ∧ (∀ n, MapsTo (ψ n) (I n) J) ∧
      (∀ n, (ψ n '' I n).OrdConnected) ∧ (∀ n, ∀ t ∈ I n, γ (ψ n t) = c n t) ∧
      ∀ n, ∀ t ∈ I n, ψ (n + 1) (φ n t) = ψ n t := by
  classical
  have hne : ∀ n, (I n).Nonempty := fun n => (hc n).nonempty
  have hIo : ∀ n, (I n).OrdConnected := fun n => (hc n).ordConnected
  -- the parametrisations, one at a time, with images in `[-n - 1, n + 1]`
  set P : ℕ → (ℝ → ℝ) → Prop := fun n f => StrictMonoOn f (I n) ∧ (f '' I n).OrdConnected ∧
    f '' I n ⊆ Icc (-(n : ℝ) - 1) (n + 1) with hP
  have hstep : ∀ n (f : ℝ → ℝ), ∃ f' : ℝ → ℝ,
      P n f → P (n + 1) f' ∧ ∀ t ∈ I n, f' (φ n t) = f t := by
    intro n f
    by_cases hf : P n f
    · obtain ⟨hfm, hfo, hfb⟩ := hf
      have hinv : ∀ t ∈ I n, invFunOn (φ n) (I n) (φ n t) = t := fun t ht =>
        (hφ n).injOn.leftInvOn_invFunOn ht
      have himg : (f ∘ invFunOn (φ n) (I n)) '' (φ n '' I n) = f '' I n := by
        rw [image_comp, (hφ n).injOn.invFunOn_image subset_rfl]
      have hhm : StrictMonoOn (f ∘ invFunOn (φ n) (I n)) (φ n '' I n) := by
        rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hlt
        simp only [comp_apply, hinv s hs, hinv s' hs']
        exact hfm hs hs' (((hφ n).lt_iff_lt hs hs').1 hlt)
      obtain ⟨f', hf'm, hf'o, hf'b, hf'eq⟩ := exists_strictMonoOn_extend ((hne n).image _)
        (hφo n) (hφm n).image_subset (hIo (n + 1)) hhm (himg ▸ hfo) (himg ▸ hfb)
      refine ⟨f', fun _ => ⟨⟨hf'm, hf'o, ?_⟩, fun t ht => ?_⟩⟩
      · intro y hy
        have := hf'b hy
        push_cast
        constructor <;> linarith [this.1, this.2]
      · rw [hf'eq (mem_image_of_mem _ ht)]
        simp only [comp_apply, hinv t ht]
    · exact ⟨f, fun h => absurd h hf⟩
  choose F hF using hstep
  obtain ⟨t₀, ht₀⟩ := hne 0
  obtain ⟨ψ₀, hψ₀m, hψ₀o, hψ₀b, -⟩ := exists_strictMonoOn_extend (A := {t₀}) (B := I 0)
    (h := fun _ => 0) (lo := 0) (hi := 0) (singleton_nonempty _) ordConnected_singleton
    (singleton_subset_iff.2 ht₀) (hIo 0) (strictMonoOn_singleton _)
    (by rw [image_singleton]; exact ordConnected_singleton)
    (by rw [image_singleton]; exact singleton_subset_iff.2 ⟨le_rfl, le_rfl⟩)
  set ψ : ℕ → ℝ → ℝ := fun n => Nat.rec (motive := fun _ => ℝ → ℝ) ψ₀ (fun k f => F k f) n
    with hψdef
  have hψs : ∀ n, ψ (n + 1) = F n (ψ n) := fun _ => rfl
  have hPn : ∀ n, P n (ψ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hψ₀m, hψ₀o, fun y hy => ?_⟩
      have := hψ₀b hy
      simp only [Nat.cast_zero, neg_zero, zero_sub, zero_add]
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    | succ n ih => rw [hψs]; exact (hF n (ψ n) ih).1
  have hcompat : ∀ n, ∀ t ∈ I n, ψ (n + 1) (φ n t) = ψ n t := fun n t ht => by
    rw [hψs]; exact (hF n (ψ n) (hPn n)).2 t ht
  -- the images are nested
  have hnest1 : ∀ n, ψ n '' I n ⊆ ψ (n + 1) '' I (n + 1) := by
    rintro n _ ⟨t, ht, rfl⟩
    exact ⟨φ n t, hφm n ht, hcompat n t ht⟩
  have hnest : ∀ m n, m ≤ n → ψ m '' I m ⊆ ψ n '' I n := fun m n h =>
    monotone_nat_of_le_succ (f := fun n => ψ n '' I n) hnest1 h
  have hseg : ∀ x ∈ ⋃ n, ψ n '' I n, ∀ y ∈ ⋃ n, ψ n '' I n,
      ∃ n, x ∈ ψ n '' I n ∧ y ∈ ψ n '' I n := by
    intro x hx y hy
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    exact ⟨max m k, hnest m _ (le_max_left _ _) hm, hnest k _ (le_max_right _ _) hk⟩
  -- composites of the `φ`, and the values they carry
  set Φ : ℕ → ℕ → ℝ → ℝ := fun m k =>
    Nat.rec (motive := fun _ => ℝ → ℝ) id (fun j f => φ (m + j) ∘ f) k with hΦdef
  have hΦ : ∀ m k, ∀ t ∈ I m, Φ m k t ∈ I (m + k) ∧ ψ (m + k) (Φ m k t) = ψ m t ∧
      c (m + k) (Φ m k t) = c m t := by
    intro m k
    induction k with
    | zero => intro t ht; exact ⟨ht, rfl, rfl⟩
    | succ k ih =>
      intro t ht
      obtain ⟨h1, h2, h3⟩ := ih t ht
      refine ⟨hφm _ h1, ?_, ?_⟩
      · show ψ (m + k + 1) (φ (m + k) (Φ m k t)) = ψ m t
        rw [hcompat _ _ h1, h2]
      · show c (m + k + 1) (φ (m + k) (Φ m k t)) = c m t
        rw [hφc _ _ h1, h3]
  have hwd : ∀ m n, ∀ t ∈ I m, ∀ t' ∈ I n, ψ m t = ψ n t' → c m t = c n t' := by
    have key : ∀ m k, ∀ t ∈ I m, ∀ t' ∈ I (m + k), ψ m t = ψ (m + k) t' →
        c m t = c (m + k) t' := by
      intro m k t ht t' ht' he
      obtain ⟨h1, h2, h3⟩ := hΦ m k t ht
      have : Φ m k t = t' := (hPn (m + k)).1.injOn h1 ht' (h2.trans he)
      rw [← h3, this]
    intro m n t ht t' ht' he
    rcases le_total m n with hmn | hnm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact key m k t ht t' ht' he
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact (key n k t' ht' t ht he.symm).symm
  -- the limit curve
  set J := ⋃ n, ψ n '' I n with hJ
  set γ : ℝ → M := fun x => if h : ∃ n, x ∈ ψ n '' I n then
    c h.choose (invFunOn (ψ h.choose) (I h.choose) x) else c 0 x with hγdef
  have hγ : ∀ n, ∀ t ∈ I n, γ (ψ n t) = c n t := by
    intro n t ht
    have h : ∃ k, ψ n t ∈ ψ k '' I k := ⟨n, mem_image_of_mem _ ht⟩
    simp only [hγdef, dif_pos h]
    exact hwd _ _ _ (invFunOn_mem h.choose_spec) _ ht (invFunOn_eq h.choose_spec)
  have hJo : J.OrdConnected := ⟨fun x hx y hy z hz => by
    obtain ⟨n, hxn, hyn⟩ := hseg x hx y hy
    exact mem_iUnion.2 ⟨n, (hPn n).2.1.out hxn hyn hz⟩⟩
  have hcurveK : ∀ n, C.CausalCurveIn W (ψ n '' I n) (c n ∘ invFunOn (ψ n) (I n)) := by
    intro n
    have hinvm := strictMonoOn_invFunOn (hPn n).1
    have hinvimg : invFunOn (ψ n) (I n) '' (ψ n '' I n) = I n :=
      (hPn n).1.injOn.invFunOn_image subset_rfl
    refine (hc n).comp ((hne n).image _) (hPn n).2.1 hinvm
      (continuousOn_of_strictMonoOn_ordConnected (hPn n).2.1 hinvm
        (by rw [hinvimg]; exact hIo n)) ?_
    intro x hx
    have := mem_image_of_mem (invFunOn (ψ n) (I n)) hx
    rwa [hinvimg] at this
  have hcurve : C.CausalCurveIn W J γ := by
    refine ⟨?_, hJo, fun a ha b hb => ?_⟩
    · exact ⟨ψ 0 t₀, mem_iUnion.2 ⟨0, mem_image_of_mem _ ht₀⟩⟩
    · obtain ⟨n, han, hbn⟩ := hseg a ha b hb
      rcases le_or_gt a b with hab | hab
      · refine CurveOn.congr ((hcurveK n).curve a han b hbn) ?_
        intro x hx
        obtain ⟨t, ht, rfl⟩ := (hPn n).2.1.out han hbn hx
        simp only [comp_apply]
        rw [hγ n t ht, (hPn n).1.injOn.leftInvOn_invFunOn ht]
      · exact CurveOn.of_lt hab
  have htfJ : TailFree J γ := by
    constructor
    · intro t ht t' ht' htt'
      obtain ⟨n, htn, ht'n⟩ := hseg t ht t' ht'
      obtain ⟨u, hu, rfl⟩ := htn
      obtain ⟨u', hu', rfl⟩ := ht'n
      have huu' : u < u' := ((hPn n).1.lt_iff_lt hu hu').1 htt'
      obtain ⟨s, hs, hus, hcs⟩ := (htf n).1 u hu u' hu' huu'
      refine ⟨ψ n s, mem_iUnion.2 ⟨n, mem_image_of_mem _ hs⟩,
        (hPn n).1.monotoneOn hu hs hus, ?_⟩
      rw [hγ n s hs, hγ n u hu]
      exact hcs
    · intro t ht t' ht' htt'
      obtain ⟨n, htn, ht'n⟩ := hseg t ht t' ht'
      obtain ⟨u, hu, rfl⟩ := htn
      obtain ⟨u', hu', rfl⟩ := ht'n
      have huu' : u' < u := ((hPn n).1.lt_iff_lt hu' hu).1 htt'
      obtain ⟨s, hs, hsu, hcs⟩ := (htf n).2 u hu u' hu' huu'
      refine ⟨ψ n s, mem_iUnion.2 ⟨n, mem_image_of_mem _ hs⟩,
        (hPn n).1.monotoneOn hs hu hsu, ?_⟩
      rw [hγ n s hs, hγ n u hu]
      exact hcs
  exact ⟨J, γ, ψ, hcurve, htfJ, fun n => (hPn n).1,
    fun n t ht => mem_iUnion.2 ⟨n, mem_image_of_mem _ ht⟩, fun n => (hPn n).2.1, hγ, hcompat⟩

end Sequence

/-! ## 4. A chain with no countable cofinal set does not grow at an end forever -/

section LongChains

variable {M : Type u} [TopologicalSpace M]

open Ordinal Order in
/-- **Long chains stop growing on the right.** A coherent family of continuous maps over
intervals, tail-free on the right, indexed by a transitive relation whose countable subsets are
bounded, cannot have right excesses cofinally. Otherwise take `ω₁` indices, each two
right-excess steps above a bound of the earlier ones (a single step may add one point only); a
dense countable family of points in each excess, and at each limit the supremum of the earlier
parameters, give countably many maps `ω₁ → M` continuous at limits. They are constant on one
tail (`exists_lt_omega_one_forall_eq_family`, T1, second countable), so after a limit `λ` of
that tail all the points of the excess of `λ + 2` over `λ + 1` have one value, and by density and
T1 the map of `λ + 2` is constant on that final segment, which has two points. -/
theorem false_of_rightExcess [T1Space M] [SecondCountableTopology M] {ι : Type*}
    {r : ι → ι → Prop} (htrans : ∀ ⦃i j k⦄, r i j → r j k → r i k)
    (hbound : ∀ S : Set ι, S.Countable → ∃ j, ∀ x ∈ S, r x j)
    {I : ι → Set ℝ} {c : ι → ℝ → M} {φ : ∀ i j, r i j → ℝ → ℝ}
    (hI : ∀ i, (I i).OrdConnected)
    (hcont : ∀ i, ∀ a ∈ I i, ∀ b ∈ I i, ContinuousOn (c i) (Icc a b))
    (htf : ∀ i, ∀ t ∈ I i, ∀ t' ∈ I i, t < t' → ∃ s ∈ I i, t ≤ s ∧ c i s ≠ c i t)
    (hφ : ∀ i j h, StrictMonoOn (φ i j h) (I i)) (hφm : ∀ i j h, MapsTo (φ i j h) (I i) (I j))
    (hφc : ∀ i j h, ∀ t ∈ I i, c j (φ i j h t) = c i t)
    (hcomp : ∀ i j k hij hjk hik, ∀ t ∈ I i, φ j k hjk (φ i j hij t) = φ i k hik t)
    (hexc : ∀ i, ∃ j, ∃ h : r i j, ∃ t ∈ I j, ∀ s ∈ I i, φ i j h s < t) : False := by
  classical
  -- two right-excess steps leave a non-degenerate excess
  have hexc2 : ∀ i, ∃ j, ∃ h : r i j, ∃ a ∈ I j, ∃ b ∈ I j, a < b ∧
      ∀ s ∈ I i, φ i j h s < a := by
    intro i
    obtain ⟨j, hij, tj, htj, hj⟩ := hexc i
    obtain ⟨k, hjk, tk, htk, hk⟩ := hexc j
    refine ⟨k, htrans hij hjk, φ j k hjk tj, hφm _ _ _ htj, tk, htk, hk tj htj, fun s hs => ?_⟩
    rw [← hcomp i j k hij hjk _ s hs]
    exact hφ _ _ _ (hφm _ _ _ hs) htj (hj s hs)
  choose nx hnx ea hea eb heb heab hnxe using hexc2
  have hbound' : ∀ S : Set ι, ∃ j, S.Countable → ∀ x ∈ S, r x j := fun S => by
    by_cases hS : S.Countable
    · obtain ⟨j, hj⟩ := hbound S hS
      exact ⟨j, fun _ => hj⟩
    · obtain ⟨j, -⟩ := hbound ∅ countable_empty
      exact ⟨j, fun h => absurd h hS⟩
  choose ub hub using hbound'
  -- the `ω₁`-sequence: each index two right-excess steps above a bound of the earlier ones
  obtain ⟨seq, hseq⟩ : ∃ seq : Ordinal.{0} → ι,
      ∀ α, seq α = nx (ub (range fun β : Iio α => seq β.1)) :=
    ⟨_, fun α => Ordinal.lt_wf.fix_eq (C := fun _ => ι)
      (fun α rec => nx (ub (range fun β : Iio α => rec β.1 β.2))) α⟩
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hsucc : ∀ α < (ω₁ : Ordinal.{0}), succ α < ω₁ := fun α hα => hω.succ_lt hα
  have hcount : ∀ α < (ω₁ : Ordinal.{0}), (range fun β : Iio α => seq β.1).Countable :=
    fun α hα => by
      haveI := (countable_Iio_of_lt_omega_one hα).to_subtype
      exact countable_range _
  have hrel : ∀ α < (ω₁ : Ordinal.{0}), ∀ β < α, r (seq β) (seq α) := by
    intro α hα β hβα
    rw [hseq α]
    exact htrans (hub _ (hcount α hα) _ ⟨⟨β, hβα⟩, rfl⟩) (hnx _)
  have hKne : ∀ α, (I (seq α)).Nonempty := fun α => by
    rw [hseq α]
    exact ⟨ea _, hea _⟩
  have hexcess : ∀ i k (hik : r i k), (∃ j, r i j ∧ k = nx j) →
      ∃ a ∈ I k, ∃ b ∈ I k, a < b ∧ ∀ s ∈ I i, φ i k hik s < a := by
    rintro i k hik ⟨j, hij, rfl⟩
    refine ⟨ea j, hea j, eb j, heb j, heab j, fun s hs => ?_⟩
    rw [← hcomp i j (nx j) hij (hnx j) hik s hs]
    exact hnxe j _ (hφm _ _ _ hs)
  -- transport along the sequence
  obtain ⟨T, hT⟩ : ∃ T : Ordinal.{0} → Ordinal.{0} → ℝ → ℝ,
      ∀ β α (h : r (seq β) (seq α)), T β α = φ _ _ h :=
    ⟨fun β α => if h : r (seq β) (seq α) then φ _ _ h else id, fun β α h => dif_pos h⟩
  have hTm : ∀ α < (ω₁ : Ordinal.{0}), ∀ β < α, MapsTo (T β α) (I (seq β)) (I (seq α)) :=
    fun α hα β hβ => by rw [hT β α (hrel α hα β hβ)]; exact hφm _ _ _
  have hTs : ∀ α < (ω₁ : Ordinal.{0}), ∀ β < α, StrictMonoOn (T β α) (I (seq β)) :=
    fun α hα β hβ => by rw [hT β α (hrel α hα β hβ)]; exact hφ _ _ _
  have hTc : ∀ α < (ω₁ : Ordinal.{0}), ∀ β < α, ∀ t ∈ I (seq β),
      c (seq α) (T β α t) = c (seq β) t :=
    fun α hα β hβ t ht => by rw [hT β α (hrel α hα β hβ)]; exact hφc _ _ _ t ht
  have hTT : ∀ γ < (ω₁ : Ordinal.{0}), ∀ α < γ, ∀ β < α, ∀ t ∈ I (seq β),
      T α γ (T β α t) = T β γ t := fun γ hγ α hαγ β hβα t ht => by
    rw [hT α γ (hrel γ hγ α hαγ), hT β α (hrel α (hαγ.trans hγ) β hβα),
      hT β γ (hrel γ hγ β (hβα.trans hαγ))]
    exact hcomp _ _ _ _ _ _ t ht
  -- the excess of `seq (succ α)` over `seq α`: a final segment with two points
  set E : Ordinal.{0} → Set ℝ :=
    fun α => {t ∈ I (seq (succ α)) | ∀ s ∈ I (seq α), T α (succ α) s < t} with hE
  have hEup : ∀ α, ∀ t ∈ E α, ∀ t' ∈ I (seq (succ α)), t ≤ t' → t' ∈ E α :=
    fun α t ht t' ht' h => ⟨ht', fun s hs => (ht.2 s hs).trans_le h⟩
  have hEo : ∀ α, (E α).OrdConnected := fun α =>
    ⟨fun x hx y hy z hz => hEup α x hx z ((hI _).out hx.1 hy.1 hz) hz.1⟩
  have hEnd : ∀ α < (ω₁ : Ordinal.{0}), ∃ a ∈ E α, ∃ b ∈ E α, a < b := by
    intro α hα
    have hr := hrel (succ α) (hsucc α hα) α (lt_succ α)
    obtain ⟨a, ha, b, hb, hab, hlt⟩ := hexcess _ _ hr
      ⟨ub (range fun β : Iio (succ α) => seq β.1),
        hub _ (hcount _ (hsucc α hα)) _ ⟨⟨α, lt_succ α⟩, rfl⟩, hseq (succ α)⟩
    refine ⟨a, ⟨ha, fun s hs => ?_⟩, b, ⟨hb, fun s hs => ?_⟩, hab⟩
    · rw [hT _ _ hr]; exact hlt s hs
    · rw [hT _ _ hr]; exact (hlt s hs).trans hab
  -- a dense countable family of points in each excess
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Ordinal.{0} → ℝ, ∀ α < (ω₁ : Ordinal.{0}), e₀ α ∈ E α :=
    ⟨fun α => Classical.epsilon (· ∈ E α), fun α hα =>
      Classical.epsilon_spec (let ⟨a, ha, _⟩ := hEnd α hα; ⟨a, ha⟩)⟩
  set e : Ordinal.{0} → ℚ → ℝ := fun α q => if (q : ℝ) ∈ E α then (q : ℝ) else e₀ α with he
  have heE : ∀ α < (ω₁ : Ordinal.{0}), ∀ q, e α q ∈ E α := fun α hα q => by
    simp only [he]
    split_ifs with h
    exacts [h, he₀ α hα]
  have heq : ∀ α (q : ℚ), (q : ℝ) ∈ E α → e α q = q := fun α q h => by simp only [he, if_pos h]
  -- at a limit, the supremum of the earlier parameters, read in `seq (succ λ)`
  set S : Ordinal.{0} → Set ℝ :=
    fun l => {p | ∃ β < l, ∃ t ∈ I (seq β), p = T β (succ l) t} with hS
  have hS_sub : ∀ l < (ω₁ : Ordinal.{0}), S l ⊆ I (seq (succ l)) := by
    rintro l hl _ ⟨β, hβ, t, ht, rfl⟩
    exact hTm (succ l) (hsucc l hl) β (hβ.trans (lt_succ l)) ht
  have hS_ne : ∀ l, IsSuccLimit l → (S l).Nonempty := fun l hlim =>
    let ⟨t, ht⟩ := hKne 0
    ⟨_, 0, hlim.pos, t, ht, rfl⟩
  have hS_lt : ∀ l < (ω₁ : Ordinal.{0}), ∀ p ∈ S l, p < e₀ l := by
    rintro l hl _ ⟨β, hβ, t, ht, rfl⟩
    rw [← hTT (succ l) (hsucc l hl) l (lt_succ l) β hβ t ht]
    exact (he₀ l hl).2 _ (hTm l hl β hβ ht)
  have hS_bdd : ∀ l < (ω₁ : Ordinal.{0}), BddAbove (S l) := fun l hl =>
    ⟨e₀ l, fun p hp => (hS_lt l hl p hp).le⟩
  set sl : Ordinal.{0} → ℝ := fun l => sSup (S l) with hsl
  have hle_sl : ∀ l < (ω₁ : Ordinal.{0}), ∀ p ∈ S l, p ≤ sl l := fun l hl p hp =>
    le_csSup (hS_bdd l hl) hp
  have hsl_mem : ∀ l < (ω₁ : Ordinal.{0}), IsSuccLimit l → sl l ∈ I (seq (succ l)) := by
    intro l hl hlim
    obtain ⟨p, hp⟩ := hS_ne l hlim
    exact (hI _).out (hS_sub l hl hp) (he₀ l hl).1
      ⟨hle_sl l hl p hp, csSup_le ⟨p, hp⟩ fun q hq => (hS_lt l hl q hq).le⟩
  -- the maps `ω₁ → M`, one per rational
  set u : ℚ → Ordinal.{0} → ℝ := fun q α => if IsSuccLimit α then sl α else e α q with hu
  set g : ℚ → Ordinal.{0} → M := fun q α => c (seq (succ α)) (u q α) with hg
  have hu_mem : ∀ q, ∀ α < (ω₁ : Ordinal.{0}), u q α ∈ I (seq (succ α)) := fun q α hα => by
    simp only [hu]
    split_ifs with h
    · exact hsl_mem α hα h
    · exact (heE α hα q).1
  -- the parameters of the earlier points, read in `seq (succ λ)`, increase to `sl λ`
  have hlow : ∀ q, ∀ l < (ω₁ : Ordinal.{0}), ∀ γ < l, ∀ β < γ, ∀ t ∈ I (seq β),
      T β (succ l) t ≤ T (succ γ) (succ l) (u q γ) := by
    intro q l hl γ hγl β hβγ t ht
    have hγ : γ < ω₁ := hγl.trans hl
    have hsγl : succ γ < succ l := succ_lt_succ hγl
    have hβsγ : β < succ γ := hβγ.trans (lt_succ γ)
    rw [← hTT (succ l) (hsucc l hl) (succ γ) hsγl β hβsγ t ht]
    have ht' : T β (succ γ) t ∈ I (seq (succ γ)) := hTm _ (hsucc γ hγ) β hβsγ ht
    by_cases hlim : IsSuccLimit γ
    · have hu' : u q γ = sl γ := by simp only [hu, if_pos hlim]
      rw [hu']
      exact (hTs _ (hsucc l hl) _ hsγl).monotoneOn ht' (hsl_mem γ hγ hlim)
        (hle_sl γ hγ _ ⟨β, hβγ, t, ht, rfl⟩)
    · have hu' : u q γ = e γ q := by simp only [hu, if_neg hlim]
      rw [hu']
      have h1 : T γ (succ γ) (T β γ t) < e γ q := (heE γ hγ q).2 _ (hTm γ hγ β hβγ ht)
      rw [hTT (succ γ) (hsucc γ hγ) γ (lt_succ γ) β hβγ t ht] at h1
      exact ((hTs _ (hsucc l hl) _ hsγl) ht' (heE γ hγ q).1 h1).le
  -- continuity at limits
  have hlimc : ∀ q, ∀ a < (ω₁ : Ordinal.{0}), IsSuccLimit a → ∀ U ∈ 𝓝 (g q a),
      ∃ b < a, ∀ γ, b < γ → γ < a → g q γ ∈ U := by
    intro q l hl hlim U hU
    have hgl : g q l = c (seq (succ l)) (sl l) := by simp only [hg, hu, if_pos hlim]
    rw [hgl] at hU
    obtain ⟨_, ⟨β₀, hβ₀, t₀, ht₀, rfl⟩⟩ := hS_ne l hlim
    have hp₀I := hS_sub l hl ⟨β₀, hβ₀, t₀, ht₀, rfl⟩
    have hp₀le := hle_sl l hl _ ⟨β₀, hβ₀, t₀, ht₀, rfl⟩
    have hcw := hcont _ _ hp₀I _ (hsl_mem l hl hlim) (sl l) ⟨hp₀le, le_rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hcw hU)
    obtain ⟨_, ⟨β₁, hβ₁, t₁, ht₁, rfl⟩, hlt₁⟩ :=
      exists_lt_of_lt_csSup (hS_ne l hlim) (show sl l - ε < sl l by linarith)
    refine ⟨max β₀ β₁, max_lt hβ₀ hβ₁, fun γ hγ hγl => ?_⟩
    have hγ' : γ < ω₁ := hγl.trans hl
    have hsγl : succ γ < l := hlim.succ_lt hγl
    have hval : g q γ = c (seq (succ l)) (T (succ γ) (succ l) (u q γ)) := by
      rw [hTc (succ l) (hsucc l hl) (succ γ) (succ_lt_succ hγl) _ (hu_mem q γ hγ')]
    rw [hval]
    apply hball
    have hmemS : T (succ γ) (succ l) (u q γ) ∈ S l := ⟨succ γ, hsγl, u q γ, hu_mem q γ hγ', rfl⟩
    have h0 := hlow q l hl γ hγl β₀ (lt_of_le_of_lt (le_max_left _ _) hγ) t₀ ht₀
    have h1 := hlow q l hl γ hγl β₁ (lt_of_le_of_lt (le_max_right _ _) hγ) t₁ ht₁
    have h2 := hle_sl l hl _ hmemS
    refine ⟨?_, h0, h2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- eventual constancy, and a constant final segment
  obtain ⟨γ₀, hγ₀, hconst⟩ := exists_lt_omega_one_forall_eq_family (ι := ℚ) (g := g) hlimc
  obtain ⟨l, hγ₀l, hl, hlim⟩ := exists_isSuccLimit_ge_lt_omega_one hγ₀
  have hsl' : succ l < ω₁ := hsucc l hl
  have hnl : ¬ IsSuccLimit (succ l) := not_isSuccLimit_succ l
  have hall : ∀ q, c (seq (succ (succ l))) (e (succ l) q) = c (seq (succ l)) (sl l) := by
    intro q
    have h1 := hconst q (succ l) (hγ₀l.trans (le_succ l)) hsl'
    have h2 := hconst q l hγ₀l hl
    have e1 : g q (succ l) = c (seq (succ (succ l))) (e (succ l) q) := by
      simp only [hg, hu, if_neg hnl]
    have e2 : g q l = c (seq (succ l)) (sl l) := by simp only [hg, hu, if_pos hlim]
    rw [← e1, ← e2, h1, h2]
  have hconstE : ∀ t ∈ E (succ l), c (seq (succ (succ l))) t = c (seq (succ l)) (sl l) := by
    intro t ht
    obtain ⟨a, ha, b, hb, hab⟩ := hEnd (succ l) hsl'
    obtain ⟨v, hv, hvt⟩ : ∃ v ∈ E (succ l), v ≠ t := by
      by_cases h : a = t
      · exact ⟨b, hb, fun h' => hab.ne (h.trans h'.symm)⟩
      · exact ⟨a, ha, h⟩
    obtain ⟨lo, hlo, hi, hhi, hlohi, htmem⟩ : ∃ lo ∈ E (succ l), ∃ hi ∈ E (succ l), lo < hi ∧
        t ∈ Icc lo hi := by
      rcases lt_or_gt_of_ne hvt with h | h
      · exact ⟨v, hv, t, ht, h, h.le, le_rfl⟩
      · exact ⟨t, ht, v, hv, h, le_rfl, h.le⟩
    have hsub : Icc lo hi ⊆ E (succ l) := (hEo _).out hlo hhi
    refine eq_of_continuousOn_of_rat hlohi (hcont _ _ hlo.1 _ hhi.1) (fun q hq => ?_) t htmem
    rw [← heq _ q (hsub (Ioo_subset_Icc_self hq))]
    exact hall q
  obtain ⟨a, ha, b, hb, hab⟩ := hEnd (succ l) hsl'
  obtain ⟨s, hs, has, hne⟩ := htf _ a ha.1 b hb.1 hab
  exact hne ((hconstE s (hEup _ a ha s hs has)).trans (hconstE a ha).symm)

/-- **Long chains stop growing on the left**: the mirror image of `false_of_rightExcess`, through
`t ↦ -t`. -/
theorem false_of_leftExcess [T1Space M] [SecondCountableTopology M] {ι : Type*}
    {r : ι → ι → Prop} (htrans : ∀ ⦃i j k⦄, r i j → r j k → r i k)
    (hbound : ∀ S : Set ι, S.Countable → ∃ j, ∀ x ∈ S, r x j)
    {I : ι → Set ℝ} {c : ι → ℝ → M} {φ : ∀ i j, r i j → ℝ → ℝ}
    (hI : ∀ i, (I i).OrdConnected)
    (hcont : ∀ i, ∀ a ∈ I i, ∀ b ∈ I i, ContinuousOn (c i) (Icc a b))
    (htf : ∀ i, ∀ t ∈ I i, ∀ t' ∈ I i, t' < t → ∃ s ∈ I i, s ≤ t ∧ c i s ≠ c i t)
    (hφ : ∀ i j h, StrictMonoOn (φ i j h) (I i)) (hφm : ∀ i j h, MapsTo (φ i j h) (I i) (I j))
    (hφc : ∀ i j h, ∀ t ∈ I i, c j (φ i j h t) = c i t)
    (hcomp : ∀ i j k hij hjk hik, ∀ t ∈ I i, φ j k hjk (φ i j hij t) = φ i k hik t)
    (hexc : ∀ i, ∃ j, ∃ h : r i j, ∃ t ∈ I j, ∀ s ∈ I i, t < φ i j h s) : False := by
  refine false_of_rightExcess (I := fun i => Neg.neg ⁻¹' I i) (c := fun i t => c i (-t))
    (φ := fun i j h t => -φ i j h (-t)) htrans hbound
    (fun i => ⟨fun x hx y hy z hz => (hI i).out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩)
    (fun i a ha b hb => (hcont i (-b) hb (-a) ha).comp continuousOn_neg
      fun t ht => ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩) ?_
    (fun i j h s hs t ht hst => neg_lt_neg (hφ i j h ht hs (neg_lt_neg hst)))
    (fun i j h t ht => show -(-φ i j h (-t)) ∈ I j by rw [neg_neg]; exact hφm i j h ht)
    (fun i j h t ht => by simp only [neg_neg]; exact hφc i j h (-t) ht)
    (fun i j k hij hjk hik t ht => by simp only [neg_neg]; rw [hcomp i j k hij hjk hik (-t) ht])
    ?_
  · intro i t ht t' ht' htt'
    obtain ⟨s, hs, hst, hcs⟩ := htf i (-t) ht (-t') ht' (neg_lt_neg htt')
    exact ⟨-s, show -(-s) ∈ I i by rw [neg_neg]; exact hs, by linarith,
      by simp only [neg_neg]; exact hcs⟩
  · intro i
    obtain ⟨j, h, t, ht, hlt⟩ := hexc i
    exact ⟨j, h, -t, show -(-t) ∈ I j by rw [neg_neg]; exact ht,
      fun s hs => neg_lt_neg (hlt (-s) hs)⟩

end LongChains

/-! ## 5. Zorn on towers of tail-free curves -/

section IntervalMap

variable {I I' : Set ℝ}

open Classical in
/-- A map between two intervals read as a map of `ℝ` (the identity off its domain). -/
noncomputable def intervalMap (f : I → I') : ℝ → ℝ :=
  fun t => if h : t ∈ I then (f ⟨t, h⟩ : ℝ) else t

theorem intervalMap_apply (f : I → I') {t : ℝ} (ht : t ∈ I) : intervalMap f t = f ⟨t, ht⟩ :=
  dif_pos ht

theorem intervalMap_coe (f : I → I') (t : I) : intervalMap f t = f t := dif_pos t.2

theorem mapsTo_intervalMap (f : I → I') : MapsTo (intervalMap f) I I' := fun t ht => by
  rw [intervalMap_apply f ht]
  exact (f _).2

theorem strictMonoOn_intervalMap {f : I → I'} (hf : StrictMono f) :
    StrictMonoOn (intervalMap f) I := fun s hs t ht hst => by
  rw [intervalMap_apply f hs, intervalMap_apply f ht]
  exact hf hst

theorem image_intervalMap (f : I → I') : intervalMap f '' I = range fun t => (f t : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, (intervalMap_apply f ht).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.2, intervalMap_coe f t⟩

end IntervalMap

namespace Causality

variable {M : Type u} [TopologicalSpace M]

variable (C : Causality M) (W : Opens M) in
/-- **The tail-free causal curves of `W`**, the developments of the Zorn argument: a causal curve
`p.2` of `W` over the interval `p.1`, tail-free. Its carrier is the interval. -/
def TailFreeCurve : Type u :=
  {p : Set ℝ × (ℝ → M) // C.CausalCurveIn W p.1 p.2 ∧ TailFree p.1 p.2}

variable (C : Causality M) (W : Opens M) in
/-- **The morphisms**: `f : I → I'` strictly monotone, onto a sub-interval, with `c' ∘ f = c`
(the `reparam` field of `Causality.StrictlyExtends`). -/
def tailFreeMor (X Y : C.TailFreeCurve W) (f : X.1.1 → Y.1.1) : Prop :=
  StrictMono f ∧ (range fun t => (f t : ℝ)).OrdConnected ∧ ∀ t, Y.1.2 (f t) = X.1.2 t

theorem tailFreeMor_morphismsCompose {C : Causality M} {W : Opens M} :
    AbstractDev.MorphismsCompose (carrier := fun X : C.TailFreeCurve W => X.1.1)
      (C.tailFreeMor W) := by
  refine ⟨fun X => ⟨strictMono_id, ?_, fun t => rfl⟩, ?_⟩
  · have : (range fun t : X.1.1 => ((id t : X.1.1) : ℝ)) = X.1.1 := Subtype.range_coe
    rw [this]
    exact X.2.1.ordConnected
  · rintro X Y Z f g ⟨hf, hfo, hfc⟩ ⟨hg, hgo, hgc⟩
    refine ⟨hg.comp hf, ?_, fun t => by simp only [comp_apply, hgc, hfc]⟩
    have e : (range fun t : X.1.1 => ((g ∘ f) t : ℝ)) =
        intervalMap g '' range fun t => (f t : ℝ) := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨f t, ⟨t, rfl⟩, intervalMap_coe g (f t)⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, (intervalMap_coe g (f t)).symm⟩
    rw [e]
    refine ordConnected_image_of_strictMonoOn (strictMonoOn_intervalMap hg) ?_ ?_ hfo
    · rw [image_intervalMap]
      exact hgo
    · rintro _ ⟨t, rfl⟩
      exact (f t).2

/-- **Chain inheritance**: every non-empty coherent chain of tail-free curves has a commuting
upper bound, its direct limit when a countable set of indices is cofinal
(`exists_seq_limit`), one of its members otherwise: then from some member on every morphism is
onto (`false_of_rightExcess`, `false_of_leftExcess`). -/
theorem tailFreeMor_chainsInherit [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : Opens M} :
    AbstractDev.ChainsInherit.{u} (carrier := fun X : C.TailFreeCurve W => X.1.1)
      (C.tailFreeMor W) := by
  classical
  intro ι _ _ r X φ hch
  -- the chain, read on `ℝ`
  set Φ : ∀ i j, r i j → ℝ → ℝ := fun i j h => intervalMap (φ h) with hΦdef
  have hΦm : ∀ i j h, MapsTo (Φ i j h) (X i).1.1 (X j).1.1 := fun i j h => mapsTo_intervalMap _
  have hΦ : ∀ i j h, StrictMonoOn (Φ i j h) (X i).1.1 := fun i j h =>
    strictMonoOn_intervalMap (hch.isMor h).1
  have hΦo : ∀ i j h, (Φ i j h '' (X i).1.1).OrdConnected := fun i j h => by
    simp only [hΦdef]
    rw [image_intervalMap]
    exact (hch.isMor h).2.1
  have hΦc : ∀ i j h, ∀ t ∈ (X i).1.1, (X j).1.2 (Φ i j h t) = (X i).1.2 t :=
    fun i j h t ht => by
      simp only [hΦdef]
      rw [intervalMap_apply _ ht]
      exact (hch.isMor h).2.2 _
  have hΦcomp : ∀ i j k hij hjk hik, ∀ t ∈ (X i).1.1, Φ j k hjk (Φ i j hij t) = Φ i k hik t := by
    intro i j k hij hjk hik t ht
    simp only [hΦdef]
    rw [intervalMap_apply _ ht, intervalMap_coe, intervalMap_apply _ ht]
    exact congrArg Subtype.val (congrFun (hch.map_comp hij hjk hik) _)
  have hΦid : ∀ i h, ∀ t ∈ (X i).1.1, Φ i i h t = t := fun i h t ht => by
    simp only [hΦdef]
    rw [intervalMap_apply _ ht, hch.map_refl i h]
    rfl
  by_cases hcof : ∃ s : ℕ → ι, ∀ i, ∃ n, r i (s n)
  · -- a countable cofinal set: the direct limit
    obtain ⟨s, hs⟩ := hcof
    set b : ℕ → ι := fun n => Nat.rec (motive := fun _ => ι) (s 0)
      (fun n bn => if r bn (s (n + 1)) then s (n + 1) else bn) n with hbdef
    have hbsucc : ∀ n, b (n + 1) = if r (b n) (s (n + 1)) then s (n + 1) else b n :=
      fun _ => rfl
    have hb0 : ∀ n, r (s n) (b n) := by
      intro n
      cases n with
      | zero => exact hch.refl _
      | succ n =>
        rw [hbsucc]
        split_ifs with h
        exacts [hch.refl _, (hch.total _ _).resolve_right h]
    have hbs : ∀ n, r (b n) (b (n + 1)) := by
      intro n
      rw [hbsucc]
      split_ifs with h
      exacts [h, hch.refl _]
    have hbmono : ∀ n k, r (b n) (b (n + k)) := by
      intro n k
      induction k with
      | zero => exact hch.refl _
      | succ k ih => exact hch.trans ih (hbs (n + k))
    have hbcof : ∀ i, ∃ n, r i (b n) := fun i =>
      let ⟨n, hn⟩ := hs i
      ⟨n, hch.trans hn (hb0 n)⟩
    obtain ⟨J, γ, ψ, hγc, hγtf, hψm, hψmaps, hψo, hψγ, hψcomp⟩ :=
      exists_seq_limit (C := C) (W := W) (I := fun n => (X (b n)).1.1)
        (c := fun n => (X (b n)).1.2) (φ := fun n => Φ _ _ (hbs n)) (fun n => (X (b n)).2.1)
        (fun n => (X (b n)).2.2) (fun n => hΦ _ _ _) (fun n => hΦm _ _ _) (fun n => hΦo _ _ _)
        (fun n => hΦc _ _ _)
    have hψk : ∀ n k, ∀ t ∈ (X (b n)).1.1, ψ (n + k) (Φ _ _ (hbmono n k) t) = ψ n t := by
      intro n k
      induction k with
      | zero =>
        intro t ht
        show ψ n (Φ (b n) (b n) (hbmono n 0) t) = ψ n t
        rw [hΦid _ _ t ht]
      | succ k ih =>
        intro t ht
        show ψ (n + k + 1) (Φ (b n) (b (n + k + 1)) (hbmono n (k + 1)) t) = ψ n t
        have h1 := hΦm _ _ (hbmono n k) ht
        rw [← hΦcomp _ _ _ (hbmono n k) (hbs (n + k)) (hbmono n (k + 1)) t ht]
        exact (hψcomp (n + k) _ h1).trans (ih t ht)
    have hind : ∀ i n m (hn : r i (b n)) (hm : r i (b m)), ∀ t ∈ (X i).1.1,
        ψ n (Φ _ _ hn t) = ψ m (Φ _ _ hm t) := by
      have key : ∀ i n k (hn : r i (b n)) (hm : r i (b (n + k))), ∀ t ∈ (X i).1.1,
          ψ n (Φ _ _ hn t) = ψ (n + k) (Φ _ _ hm t) := by
        intro i n k hn hm t ht
        rw [← hΦcomp _ _ _ hn (hbmono n k) hm t ht, hψk n k _ (hΦm _ _ hn ht)]
      intro i n m hn hm t ht
      rcases le_total n m with h | h
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        exact key i n k hn hm t ht
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        exact (key i m k hm hn t ht).symm
    choose nI hnI using hbcof
    let Z : C.TailFreeCurve W := ⟨(J, γ), hγc, hγtf⟩
    refine ⟨Z, fun i t => ⟨ψ (nI i) (Φ _ _ (hnI i) t), hψmaps _ (hΦm _ _ _ t.2)⟩,
      fun i => ⟨?_, ?_, ?_⟩, fun i j h => ?_⟩
    · intro s t hst
      exact (hψm _) (hΦm _ _ _ s.2) (hΦm _ _ _ t.2) (hΦ _ _ _ s.2 t.2 hst)
    · have e : (range fun t : (X i).1.1 => ψ (nI i) (Φ _ _ (hnI i) t)) =
          ψ (nI i) '' (Φ _ _ (hnI i) '' (X i).1.1) := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨_, ⟨t, t.2, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      show (range fun t : (X i).1.1 => ψ (nI i) (Φ _ _ (hnI i) t)).OrdConnected
      rw [e]
      exact ordConnected_image_of_strictMonoOn (hψm _) (hψo _) (hΦm _ _ _).image_subset
        (hΦo _ _ _)
    · intro t
      show γ (ψ (nI i) (Φ _ _ (hnI i) t)) = (X i).1.2 t
      rw [hψγ _ _ (hΦm _ _ _ t.2), hΦc _ _ _ _ t.2]
    · funext t
      apply Subtype.ext
      show ψ (nI j) (Φ _ _ (hnI j) (φ h t)) = ψ (nI i) (Φ _ _ (hnI i) t)
      have e1 : (φ h t : ℝ) = Φ i j h t := (intervalMap_coe _ t).symm
      rw [e1, hΦcomp _ _ _ h (hnI j) (hch.trans h (hnI j)) t t.2]
      exact (hind i _ _ _ _ t t.2).symm
  · -- no countable cofinal set: from some member on, every morphism is onto
    push Not at hcof
    have hbound : ∀ S : Set ι, S.Countable → ∃ j, ∀ x ∈ S, r x j := by
      intro S hS
      rcases S.eq_empty_or_nonempty with rfl | hne
      · obtain ⟨j⟩ := ‹Nonempty ι›
        exact ⟨j, fun x hx => absurd hx (notMem_empty x)⟩
      · obtain ⟨s, rfl⟩ := hS.exists_eq_range hne
        obtain ⟨j, hj⟩ := hcof s
        exact ⟨j, by rintro _ ⟨n, rfl⟩; exact (hch.total (s n) j).resolve_right (hj n)⟩
    have hcont : ∀ i, ∀ a ∈ (X i).1.1, ∀ b ∈ (X i).1.1, ContinuousOn (X i).1.2 (Icc a b) :=
      fun i a ha b hb => CurveOn.continuousOn C.isRelFamily_le ((X i).2.1.curve a ha b hb)
    have hR : ¬ ∀ i, ∃ j, ∃ h : r i j, ∃ t ∈ (X j).1.1, ∀ s ∈ (X i).1.1, Φ i j h s < t :=
      fun hexc => false_of_rightExcess (I := fun i => (X i).1.1) (c := fun i => (X i).1.2)
        (φ := Φ) hch.trans hbound (fun i => (X i).2.1.ordConnected) hcont
        (fun i => (X i).2.2.1) hΦ hΦm hΦc hΦcomp hexc
    have hL : ¬ ∀ i, ∃ j, ∃ h : r i j, ∃ t ∈ (X j).1.1, ∀ s ∈ (X i).1.1, t < Φ i j h s :=
      fun hexc => false_of_leftExcess (I := fun i => (X i).1.1) (c := fun i => (X i).1.2)
        (φ := Φ) hch.trans hbound (fun i => (X i).2.1.ordConnected) hcont
        (fun i => (X i).2.2.2) hΦ hΦm hΦc hΦcomp hexc
    push Not at hR hL
    obtain ⟨i₁, hi₁⟩ := hR
    obtain ⟨i₂, hi₂⟩ := hL
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, r i₁ k ∧ r i₂ k := by
      rcases hch.total i₁ i₂ with h | h
      · exact ⟨i₂, h, hch.refl _⟩
      · exact ⟨i₁, hch.refl _, h⟩
    have hsurj : ∀ j (h : r k j), Surjective (φ h) := by
      intro j h t
      by_contra hns
      push Not at hns
      have hne' : ∀ a, (φ h a : ℝ) ≠ t := fun a he => hns a (Subtype.ext he)
      have hoc := (hch.isMor h).2.1
      by_cases hex : ∃ a, (t : ℝ) < φ h a
      · obtain ⟨a₂, ha₂⟩ := hex
        have hall : ∀ a, (t : ℝ) < φ h a := by
          intro a
          by_contra hle
          push Not at hle
          rcases hle.lt_or_eq with hlt | heq'
          · obtain ⟨a', ha'⟩ := hoc.out ⟨a, rfl⟩ ⟨a₂, rfl⟩ ⟨hlt.le, ha₂.le⟩
            exact hne' a' ha'
          · exact hne' a heq'
        obtain ⟨s, hs, hst⟩ := hi₂ j (hch.trans hk₂ h) t t.2
        rw [← hΦcomp _ _ _ hk₂ h (hch.trans hk₂ h) s hs] at hst
        have h3 : (t : ℝ) < Φ k j h (Φ i₂ k hk₂ s) := by
          show (t : ℝ) < intervalMap (φ h) (Φ i₂ k hk₂ s)
          rw [intervalMap_apply _ (hΦm _ _ hk₂ hs)]
          exact hall _
        linarith
      · push Not at hex
        have hall : ∀ a, (φ h a : ℝ) < t := fun a => lt_of_le_of_ne (hex a) (hne' a)
        obtain ⟨s, hs, hts⟩ := hi₁ j (hch.trans hk₁ h) t t.2
        rw [← hΦcomp _ _ _ hk₁ h (hch.trans hk₁ h) s hs] at hts
        have h3 : Φ k j h (Φ i₁ k hk₁ s) < t := by
          show intervalMap (φ h) (Φ i₁ k hk₁ s) < t
          rw [intervalMap_apply _ (hΦm _ _ hk₁ hs)]
          exact hall _
        linarith
    have hbij : ∀ j (h : r k j), Bijective (φ h) := fun j h =>
      ⟨(hch.isMor h).1.injective, hsurj j h⟩
    have hkj : ∀ j, ¬ r j k → r k j := fun j h => (hch.total j k).resolve_left h
    set g : ∀ j, (X j).1.1 → (X k).1.1 := fun j => if h : r j k then φ h else
      (Equiv.ofBijective _ (hbij j (hkj j h))).symm with hgdef
    have hg1 : ∀ j (h : r j k), g j = φ h := fun j h => dif_pos h
    have hg2 : ∀ j (h : ¬ r j k), g j = (Equiv.ofBijective _ (hbij j (hkj j h))).symm :=
      fun j h => dif_neg h
    refine ⟨X k, g, fun j => ?_, fun i j hij => ?_⟩
    · by_cases h : r j k
      · rw [hg1 j h]
        exact hch.isMor h
      · rw [hg2 j h]
        set e := Equiv.ofBijective _ (hbij j (hkj j h)) with he_def
        have he : ∀ x, φ (hkj j h) (e.symm x) = x := fun x => e.apply_symm_apply x
        refine ⟨fun x y hxy => ?_, ?_, fun x => ?_⟩
        · rw [← (hch.isMor (hkj j h)).1.lt_iff_lt, he, he]
          exact hxy
        · have : (range fun x => (e.symm x : ℝ)) = (X k).1.1 := by
            ext z
            constructor
            · rintro ⟨x, rfl⟩
              exact (e.symm x).2
            · intro hz
              exact ⟨e ⟨z, hz⟩, by simp⟩
          rw [this]
          exact (X k).2.1.ordConnected
        · rw [← (hch.isMor (hkj j h)).2.2 (e.symm x), he]
    · funext t
      by_cases hj : r j k
      · by_cases hi : r i k
        · rw [hg1 j hj, hg1 i hi]
          exact congrFun (hch.map_comp hij hj hi) t
        · exact absurd (hch.trans hij hj) hi
      · by_cases hi : r i k
        · rw [hg2 j hj, hg1 i hi]
          set e := Equiv.ofBijective _ (hbij j (hkj j hj))
          show e.symm (φ hij t) = φ hi t
          apply e.injective
          rw [e.apply_symm_apply]
          exact (congrFun (hch.map_comp hi (hkj j hj) hij) t).symm
        · rw [hg2 j hj, hg2 i hi]
          set ej := Equiv.ofBijective _ (hbij j (hkj j hj))
          set ei := Equiv.ofBijective _ (hbij i (hkj i hi))
          show ej.symm (φ hij t) = ei.symm t
          apply ej.injective
          rw [ej.apply_symm_apply]
          show φ hij t = φ (hkj j hj) (ei.symm t)
          rw [← congrFun (hch.map_comp (hkj i hi) hij (hkj j hj)) (ei.symm t)]
          show φ hij t = φ hij (φ (hkj i hi) (ei.symm t))
          rw [show φ (hkj i hi) (ei.symm t) = t from ei.apply_symm_apply t]

/-- **A maximal tail-free curve is inextensible** (T1): a strict extension, trimmed of its
constant end pieces (`exists_tailFree_retraction`), would map back into it, so its image does
not grow. -/
theorem tailFreeMor_inextensible_of_isMaximal [T1Space M] {C : Causality M} {W : Opens M}
    {Z : C.TailFreeCurve W}
    (hZ : AbstractDev.IsMaximal (carrier := fun X : C.TailFreeCurve W => X.1.1)
      (C.tailFreeMor W) Z) :
    C.Inextensible W Z.1.1 Z.1.2 := by
  refine ⟨Z.2.1, ?_⟩
  rintro ⟨I'', c'', hcurve, ⟨φ, hφ, hφm, hφo, hφc⟩, ⟨t', ht', hnew⟩⟩
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc, hρkp⟩ :=
    exists_tailFree_retraction hcurve.nonempty hcurve.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hcurve.curve a ha b hb))
  let Y : C.TailFreeCurve W :=
    ⟨(I₀, c''), ⟨hne, ho, fun a ha b hb => hcurve.curve a (hI₀I ha) b (hI₀I hb)⟩, htf⟩
  let f : Z.1.1 → Y.1.1 := fun t => ⟨ρ (φ t), hρm (hφm t.2)⟩
  have hf : C.tailFreeMor W Z Y f := by
    refine ⟨fun s t hst => ?_, ?_, fun t => ?_⟩
    · have hst' : (s : ℝ) < t := hst
      have h1 : φ s < φ t := hφ s.2 t.2 hst'
      rcases (hρmono (hφm s.2) (hφm t.2) h1.le).lt_or_eq with h | h
      · exact h
      · exfalso
        rcases hρkp _ (hφm s.2) _ (hφm t.2) h1 h with hk | hk
        · obtain ⟨u, hu, hsu, hne'⟩ := Z.2.2.1 s s.2 t t.2 hst'
          apply hne'
          rw [← hφc u hu, ← hφc s s.2]
          exact hk _ (hφm hu) (hφ.monotoneOn s.2 hu hsu)
        · obtain ⟨u, hu, hut, hne'⟩ := Z.2.2.2 t t.2 s s.2 hst'
          apply hne'
          rw [← hφc u hu, ← hφc t t.2]
          exact hk _ (hφm hu) (hφ.monotoneOn hu t.2 hut)
    · have e : (range fun t : Z.1.1 => ((f t : Y.1.1) : ℝ)) = ρ '' (φ '' Z.1.1) := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨φ t, ⟨t, t.2, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      rw [e]
      exact ordConnected_image_of_retraction hI₀I ho hρm hρmono hρid hφm.image_subset hφo
    · show c'' (ρ (φ t)) = Z.1.2 t
      rw [hρc _ (hφm t.2), hφc t t.2]
  obtain ⟨g, hg⟩ := hZ Y f hf
  have h1 : c'' t' = Y.1.2 (⟨ρ t', hρm ht'⟩ : Y.1.1) := (hρc t' ht').symm
  exact hnew _ (g ⟨ρ t', hρm ht'⟩).2 (h1.trans (hg.2.2 _).symm)

/-! ## 6. Curves extend -/

/-- **Every causal curve of `W` over an interval lies on an inextensible causal curve of `W`**,
in a T1, second countable space with a causality, with no other hypothesis: trim the curve
(`exists_tailFree_retraction`), take a maximal tail-free curve above it
(`AbstractDev.exists_isMaximal_of_chainsInherit`), which is inextensible
(`tailFreeMor_inextensible_of_isMaximal`). -/
theorem exists_inextensible_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {C : Causality M} {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    ∃ (J : Set ℝ) (γ : ℝ → M), C.Inextensible W J γ ∧ c '' I ⊆ γ '' J := by
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, -, -, hρc, -⟩ :=
    exists_tailFree_retraction hc.nonempty hc.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hc.curve a ha b hb))
  let X : C.TailFreeCurve W :=
    ⟨(I₀, c), ⟨hne, ho, fun a ha b hb => hc.curve a (hI₀I ha) b (hI₀I hb)⟩, htf⟩
  obtain ⟨Z, f, hf, hZ⟩ := AbstractDev.exists_isMaximal_of_chainsInherit
    tailFreeMor_morphismsCompose tailFreeMor_chainsInherit X
  refine ⟨Z.1.1, Z.1.2, tailFreeMor_inextensible_of_isMaximal hZ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨f ⟨ρ t, hρm ht⟩, (f _).2, ?_⟩
  rw [hf.2.2]
  exact hρc t ht

/-- **The target**: `CurvesExtendOn W` for every open `W` of every T1, second countable space with
a causality. -/
theorem curvesExtendOn_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (C : Causality M) (W : Opens M) : C.CurvesExtendOn W :=
  fun _ _ _ hab hc => exists_inextensible_of_t1_secondCountable (hc.causalCurveIn_Icc hab)

/-- **`CurvesExtend`**, the named model fact of kb/0012 (`Causal/CauchyExtension.lean:82`), holds
in every T1, second countable space with a causality: the witness of the ladder's premise-free
fact `curves_extend` (standing T1, second countable). -/
theorem curvesExtend_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (C : Causality M) : C.CurvesExtend :=
  curvesExtendOn_top.1 (curvesExtendOn_of_t1_secondCountable C ⊤)

/-- **A Cauchy surface is acausal** in a causally arc-connected T1, second countable spacetime:
`IsCauchySurface.isAcausal` with its named hypothesis `CurvesExtend` discharged. -/
theorem IsCauchySurface.isAcausal_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {C : Causality M} {S : Set M} (hS : C.IsCauchySurface S) (hC : C.CausallyArcConnected) :
    C.IsAcausal S :=
  hS.isAcausal hC (curvesExtend_of_t1_secondCountable C)

/-- **A Cauchy surface of an open set `B` is acausal for `≤_B`** when `B` is causally
arc-connected, in a T1, second countable space: `IsCauchySurfaceOn.eq_of_le` with its named
hypothesis `CurvesExtendOn B` discharged. -/
theorem IsCauchySurfaceOn.eq_of_le_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {C : Causality M} {B : Opens M} {S : Set M} (hS : C.IsCauchySurfaceOn B S)
    (hC : C.CausallyArcConnectedOn B) {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxy : C.le B x y) :
    x = y :=
  hS.eq_of_le hC (curvesExtendOn_of_t1_secondCountable C B) hx hy hxy

end Causality

end Causal
