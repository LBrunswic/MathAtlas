import Causal.CurvesExtendSecondCountable
import Causal.NestedCausalities

/-!
# The sub-arc form of the curves theorem: a trimmed curve is a reparametrised sub-arc of an inextensible one

Programme target `T-abs-c-ext-connexe-cauchy`, step (a) (`programme/roadmap.toml`; layer 1: it
imports `Causal.CurvesExtendSecondCountable` and `Causal.NestedCausalities`, both ETT-layer; no
model; no metric notion in a statement). There is no paper statement behind this module, so **no
label is marked**; it serves `lem:C_ext_connexe` (`ETT.tex:1932`) through
`Causal.CExtConnexeCauchy.Basic`.

The target's step (a), as it words it:

> (a) Sub-arc form: a causal curve c of an open W over an interval I has I₀ ⊆ I with
> c '' I₀ = c '' I, c tail-free on I₀ (Causal.exists_tailFree_retraction, …), and an inextensible
> γ of W over J with φ : I₀ → J strictly monotone, ordconnected image, γ ∘ φ = c on I₀ (…)

and the pitfall it answers (kb/0212):

> `CurvesExtend` (and `exists_inextensible_of_t1_secondCountable`) give c(I) ⊆ γ(J), not an
> extension over J ⊇ I with γ = c on I.

## What is proved (no `sorry`)

1. **Pauses** (`Causality.CausalCurveIn.comp_monotoneOn`): a causal curve read through a
   continuous non-decreasing change of parameter is a causal curve (`≤_N` is reflexive). The
   ETT-layer twin of the model-layer `Causality.causalCurveIn_comp_monotoneOn`
   (`Causal/Remarks/SingularRowsCauchyExt.lean:191`), whose module this layer may not import; the
   name differs on purpose. `pauseTop a` is the continuous non-decreasing surjection of `ℝ` that
   stays at `a` over `[a, a + 1]`.
2. **The constant end pieces do not matter** (`Causality.Extensible.of_top_tail`,
   `Extensible.of_bottom_tail`, `Causality.Inextensible.of_retraction`): if `c` is constant off a
   sub-interval `I₀` of `I` (a monotone retraction `ρ : I → I₀` with `c ∘ ρ = c`, the output of
   `exists_tailFree_retraction`), an extension of `c` over `I₀` gives one over `I`, so `c`
   inextensible over `I` is inextensible over `I₀`. The lemmas are one-sided first (DEC-13). An
   extension at the past end takes a constant final piece with no pause
   (`Causality.PastExtensible.of_top_tail`: the old curve read through `v ↦ min v (φ t₁)`); one
   at the future end is paused at the image of the end (`Causality.FutureExtensible.of_top_tail`:
   `pauseTop`, for as long as the constant piece, compressed to length `< 1` by
   `exists_compress`); a constant initial piece is the time reversal
   (`PastExtensible.of_bottom_tail`, `Extensible.of_bottom_tail`). `Extensible.of_top_tail` is the
   corollary of the two one-sided lemmas through `extensible_iff`, so the pause is written once.
   Past-inextensibility passes to the trimmed curve too
   (`Causality.PastInextensible.of_retraction`). Also: `image_eq_of_retraction`
   (`c '' I₀ = c '' I`), `continuousOn_of_retraction` (the retraction is `1`-Lipschitz),
   `TailFree.neg` (time reversal of the parameter).
3. **The sub-arc form** (`Causality.exists_subArc_of_tailFree`,
   `Causality.exists_subArc_of_t1_secondCountable`): in a T1, second countable space, a tail-free
   causal curve `c` of `W` over `I` is `γ ∘ ψ` on `I` for an inextensible, tail-free causal curve
   `γ` of `W` over `J` and a strictly increasing, continuous `ψ : I → J` with ordconnected image;
   an arbitrary causal curve is so on the sub-interval `I₀` of `exists_tailFree_retraction`, and
   constant off it. It is the proof of `exists_inextensible_of_t1_secondCountable`
   (`Causal/CurvesExtendSecondCountable.lean:1376`) with the morphism of the maximal tail-free
   curve kept (`tailFreeMor`).
4. **Inextensible curves of a smaller open set** (`Causality.Inextensible.exists_subArc_of_le`):
   an inextensible curve of `W ≤ U`, trimmed, is tail-free, still inextensible in `W`, has the
   same image, and is a reparametrised sub-arc of an inextensible curve of `U`. And **the past
   extension of a sub-arc** (`Causality.pastExtensible_of_subArc`): if `c = γ ∘ ψ` on `I` and `γ`
   has a new value below `ψ '' I`, then `γ`, cut at the top of `ψ '' I`, strictly extends `c` at
   the past end.
5. **`inextensible_nested ⇒ curve_nested`** on T1, second countable spaces
   (`Causality.InextensibleNestedOn.curveNestedOn_of_t1_secondCountable`), the ladder's `[[open]]`
   entry (`programme/ladder.toml`, "True, argued, on a T1, second countable M"): the trimmed curve
   lies on an inextensible `C`-curve, which is a `C'`-curve, and the constant end pieces are read
   through the retraction, continuous (`continuousOn_of_retraction`).

## Hypothesis checklist

| the target's statement (step (a)) | here |
|---|---|
| `W` open, `c` a causal curve of `W` over an interval | ✓ carried (`CausalCurveIn W I c`) |
| the space T1, second countable | ✓ `[T1Space M] [SecondCountableTopology M]`, used by the curves theorem only; pauses, end pieces and retractions need nothing |
| `c '' I₀ = c '' I`, `c` tail-free on `I₀` | ✓ (`c ∘ ρ = c` on `I`, `ρ` a monotone retraction onto `I₀`: constant off `I₀`) |
| `γ` inextensible in `W`, `φ : I₀ → J` strictly monotone, ordconnected image, `γ ∘ φ = c` | ✓ carried (`ψ` for `φ`); the conclusion adds `ψ` continuous and `γ` tail-free |

## SCOPE (disclosed)

* **Nothing marked**: no label. The sub-arc form is the curves theorem's proof exposed; it is not
  in `ETT.tex`.
* The inextensible curve comes from Zorn and is not unique (`Causal.CurvesExtendSecondCountable`,
  SCOPE).
* `Extensible.of_bottom_tail` is `of_top_tail` read through time reversal
  (`Extensible.of_dual_reverse`), and `PastExtensible.of_bottom_tail` is
  `FutureExtensible.of_top_tail` read through it (`PastExtensible.of_dual_reverse`,
  `FutureExtensible.of_dual_reverse`).

## Moved here (T-abs-end-pieces-one-sided)

`PastExtensible.of_top_tail`, `FutureExtensible.of_top_tail`, `PastExtensible.of_bottom_tail`,
`PastInextensible.of_retraction` and `pastExtensible_of_subArc` were proved in
`Causal.PastInextensibleMeetsCauchy` (T-abs-past-inextensible-meets-cauchy). They were moved here,
with their full names, statements and proofs. `FutureExtensible.of_top_tail` repeated the pause
construction of `Extensible.of_top_tail` with one more property proved, and
`Causal.PastInextensibleMeetsCauchy` imports this module, so `Extensible.of_top_tail` could become
their corollary only once they sat here. They use only § 1, one another and `Causal.Inextensible`,
so the move added no import. The proof of `Extensible.of_top_tail` changed and its statement did
not. The docstrings of `PastExtensible.of_top_tail` and `FutureExtensible.of_top_tail` had the
sentences describing `Extensible.of_top_tail`'s former pause rewritten.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology Function TopologicalSpace

universe u

/-! ## 1. Pauses -/

section Pause

/-- **Pausing at `a`**: `u` below `a`, `a` on `[a, a + 1]`, `u - 1` above `a + 1`; a continuous,
non-decreasing surjection of `ℝ`. -/
noncomputable def pauseTop (a u : ℝ) : ℝ := u - min 1 (max 0 (u - a))

theorem pauseTop_of_le {a u : ℝ} (h : u ≤ a) : pauseTop a u = u := by
  simp [pauseTop, max_eq_left (sub_nonpos.2 h)]

theorem pauseTop_of_mem_Icc {a u : ℝ} (h : u ∈ Icc a (a + 1)) : pauseTop a u = a := by
  have h1 : max 0 (u - a) = u - a := max_eq_right (by linarith [h.1])
  have h2 : min 1 (u - a) = u - a := min_eq_right (by linarith [h.2])
  simp only [pauseTop, h1, h2]
  ring

theorem pauseTop_of_ge {a u : ℝ} (h : a + 1 ≤ u) : pauseTop a u = u - 1 := by
  have h1 : max 0 (u - a) = u - a := max_eq_right (by linarith)
  have h2 : min 1 (u - a) = 1 := min_eq_left (by linarith)
  simp only [pauseTop, h1, h2]

theorem monotone_pauseTop (a : ℝ) : Monotone (pauseTop a) := by
  intro u v huv
  simp only [pauseTop]
  rw [min_def, min_def, max_def, max_def]
  split_ifs <;> linarith

theorem continuous_pauseTop (a : ℝ) : Continuous (pauseTop a) := by
  unfold pauseTop
  fun_prop

/-- A compression of `]0, ∞[` onto `]0, 1[`, strictly increasing on `[0, ∞[`: `x ↦ x / (1 + x)`. -/
theorem exists_compress : ∃ g : ℝ → ℝ, (∀ x, 0 < x → 0 < g x) ∧ (∀ x, 0 ≤ x → g x < 1) ∧
    (∀ x y, 0 ≤ x → x < y → g x < g y) ∧ ∀ v, 0 < v → v < 1 → ∃ x, 0 < x ∧ g x = v := by
  refine ⟨fun x => x / (1 + x), fun x hx => div_pos hx (by linarith), fun x hx => by
    show x / (1 + x) < 1
    rw [div_lt_one (by linarith)]; linarith, fun x y hx hxy => by
    show x / (1 + x) < y / (1 + y)
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith,
    fun v hv0 hv1 => ⟨v / (1 - v), div_pos hv0 (by linarith), ?_⟩⟩
  show v / (1 - v) / (1 + v / (1 - v)) = v
  have h1 : (1 - v) ≠ 0 := by linarith
  field_simp
  ring

end Pause

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W : Opens M}

/-- **A causal curve read through a continuous non-decreasing change of parameter is a causal
curve** (constant pieces allowed: `≤_N` is reflexive). -/
theorem CausalCurveOn.comp_monotoneOn {γ : ℝ → M} {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
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

/-- The interval form of `CausalCurveOn.comp_monotoneOn`. -/
theorem CausalCurveIn.comp_monotoneOn {γ : ℝ → M} {h : ℝ → ℝ} {J I' : Set ℝ}
    (hγ : C.CausalCurveIn W J γ) (hne : I'.Nonempty) (hoc : I'.OrdConnected)
    (hh : MonotoneOn h I') (hhc : ContinuousOn h I') (hmaps : MapsTo h I' J) :
    C.CausalCurveIn W I' (γ ∘ h) := by
  refine ⟨hne, hoc, fun a ha b hb => ?_⟩
  rcases le_or_gt a b with hab | hab
  · have hsub : Icc a b ⊆ I' := hoc.out ha hb
    exact CausalCurveOn.comp_monotoneOn hab (hγ.curve _ (hmaps ha) _ (hmaps hb)) (hh.mono hsub)
      (hhc.mono hsub)
  · exact CurveOn.of_lt hab

/-! ## 2. Constant end pieces do not matter -/

/-! The one-sided lemmas come first, and the two-sided `Extensible.of_top_tail` is their
corollary, so that the pause construction is written once (`FutureExtensible.of_top_tail`). The
one-sided lemmas, `PastInextensible.of_retraction` and `pastExtensible_of_subArc` (§ 4) were moved
here from `Causal.PastInextensibleMeetsCauchy` by T-abs-end-pieces-one-sided. -/

/-- **An extension at the past end over `I₁` is one over `I`, `I` adding to `I₁` a constant final
piece**: `t₁` the last parameter of `I₁`, and `c = c t₁` on `I` after it. No pause is needed: the
new curve is the old one followed by its value at `φ t₁`, read through `v ↦ min v (φ t₁)`, over the
old interval and a translate of the final piece. (The pause of `FutureExtensible.of_top_tail` does
not keep an extension at the past end: it adds parameters above the image of the
reparametrisation.) -/
theorem PastExtensible.of_top_tail {I₁ I : Set ℝ} {c : ℝ → M} {t₁ : ℝ} (hI₁I : I₁ ⊆ I)
    (hIo : I.OrdConnected) (ht₁ : t₁ ∈ I₁) (hmax : ∀ t ∈ I₁, t ≤ t₁)
    (htail : ∀ t ∈ I, t ∉ I₁ → t₁ < t ∧ c t = c t₁) (hext : C.PastExtensible W I₁ c) :
    C.PastExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hmaps, -, heq, hfin⟩, ⟨t', ht', hgrow⟩⟩ := hext
  set a := φ t₁ with ha
  have hI₁ : ∀ t ∈ I, t ≤ t₁ → t ∈ I₁ := fun t ht hle => by
    by_contra h
    exact absurd hle (not_le.2 (htail t ht h).1)
  have hφa : ∀ t ∈ I₁, φ t ≤ a := fun t ht => hφ.monotoneOn ht ht₁ (hmax t ht)
  -- `I'` lies below `a`: the image of `φ` is a final segment of `I'` with greatest point `a`
  have hI'a : ∀ v ∈ I', v ≤ a := fun v hv => by
    by_contra h
    push Not at h
    obtain ⟨s, hs, rfl⟩ := hfin t₁ ht₁ v hv h.le
    exact absurd (hφa s hs) (not_le.2 h)
  -- the new interval: `I'`, then a translate of the constant final piece of `I`
  set I'' : Set ℝ := I' ∪ {v | a < v ∧ t₁ + (v - a) ∈ I} with hI''
  obtain ⟨φ'', hlow, hhigh⟩ : ∃ φ'' : ℝ → ℝ, (∀ t, t ≤ t₁ → φ'' t = φ t) ∧
      ∀ t, t₁ < t → φ'' t = a + (t - t₁) :=
    ⟨fun t => if t ≤ t₁ then φ t else a + (t - t₁), fun t h => if_pos h,
      fun t h => if_neg (not_le.2 h)⟩
  have hmin : MapsTo (fun v => min v a) I'' I' := by
    rintro v (hv | ⟨hv, -⟩)
    · show min v a ∈ I'
      rw [min_eq_left (hI'a v hv)]
      exact hv
    · show min v a ∈ I'
      rw [min_eq_right hv.le]
      exact hmaps ht₁
  have hI''o : I''.OrdConnected := by
    refine ⟨fun v₁ hv₁ v₂ hv₂ z hz => ?_⟩
    rcases le_or_gt z a with hza | hza
    · left
      have hv₁' : v₁ ∈ I' := by
        rcases hv₁ with h | ⟨h, -⟩
        · exact h
        · exact absurd (h.trans_le (hz.1.trans hza)) (lt_irrefl _)
      exact hcurve.ordConnected.out hv₁' (hmaps ht₁) ⟨hz.1, hza⟩
    · right
      refine ⟨hza, ?_⟩
      have hv₂' : a < v₂ ∧ t₁ + (v₂ - a) ∈ I := by
        rcases hv₂ with h | h
        · exact absurd (hza.trans_le (hz.2.trans (hI'a v₂ h))) (lt_irrefl _)
        · exact h
      exact hIo.out (hI₁I ht₁) hv₂'.2 ⟨by linarith, by linarith [hz.2]⟩
  have hcurve'' : C.CausalCurveIn W I'' (c' ∘ fun v => min v a) :=
    hcurve.comp_monotoneOn ⟨a, Or.inl (hmaps ht₁)⟩ hI''o
      (fun _ _ _ _ h => min_le_min_right a h) (continuous_id.min continuous_const).continuousOn
      hmin
  have hmapsI : ∀ t ∈ I, φ'' t ∈ I'' := by
    intro t ht
    rcases le_or_gt t t₁ with h | h
    · rw [hlow t h]
      exact Or.inl (hmaps (hI₁ t ht h))
    · rw [hhigh t h]
      refine Or.inr ⟨by linarith, ?_⟩
      rw [show t₁ + (a + (t - t₁) - a) = t by ring]
      exact ht
  have hfin'' : ∀ t ∈ I, ∀ v ∈ I'', φ'' t ≤ v → v ∈ φ'' '' I := by
    intro t ht v hv htv
    rcases le_or_gt v a with hva | hva
    · have hvI' : v ∈ I' := by
        rcases hv with h | ⟨h, -⟩
        · exact h
        · exact absurd h (not_lt.2 hva)
      have htt₁ : t ≤ t₁ := by
        by_contra h
        push Not at h
        rw [hhigh t h] at htv
        linarith
      rw [hlow t htt₁] at htv
      obtain ⟨s, hs, rfl⟩ := hfin t (hI₁ t ht htt₁) v hvI' htv
      exact ⟨s, hI₁I hs, hlow s (hmax s hs)⟩
    · have hv' : a < v ∧ t₁ + (v - a) ∈ I := by
        rcases hv with h | h
        · exact absurd (hI'a v h) (not_le.2 hva)
        · exact h
      refine ⟨t₁ + (v - a), hv'.2, ?_⟩
      rw [hhigh _ (by linarith)]
      ring
  refine ⟨I'', c' ∘ fun v => min v a, hcurve'', ⟨φ'', ?_, hmapsI, ?_, ?_, hfin''⟩,
    ⟨t', Or.inl ht', ?_⟩⟩
  · intro s hs s' hs' hss'
    rcases le_or_gt s' t₁ with h' | h'
    · rw [hlow s (hss'.le.trans h'), hlow s' h']
      exact hφ (hI₁ s hs (hss'.le.trans h')) (hI₁ s' hs' h') hss'
    · rw [hhigh s' h']
      rcases le_or_gt s t₁ with h | h
      · rw [hlow s h]
        linarith [hφa s (hI₁ s hs h)]
      · rw [hhigh s h]
        linarith
  · refine ⟨?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ z hz
    exact hfin'' s hs z (hI''o.out (hmapsI s hs) (hmapsI s' hs') hz) hz.1
  · intro t ht
    simp only [Function.comp]
    rcases le_or_gt t t₁ with h | h
    · rw [hlow t h, min_eq_left (hφa t (hI₁ t ht h))]
      exact heq t (hI₁ t ht h)
    · rw [hhigh t h, min_eq_right (by linarith), heq t₁ ht₁]
      have hnot : t ∉ I₁ := fun hm => absurd (hmax t hm) (not_le.2 h)
      exact (htail t ht hnot).2.symm
  · intro t ht
    simp only [Function.comp]
    rw [min_eq_left (hI'a t' ht')]
    by_cases hm : t ∈ I₁
    · exact hgrow t hm
    · rw [(htail t ht hm).2]
      exact hgrow t₁ ht₁

/-- **An extension at the future end over `I₁` is one over `I`, `I` adding to `I₁` a constant final
piece**: the old extension paused at `ψ₁ t₁` by `pauseTop` for the constant piece, compressed to
length `< 1` (`exists_compress`), and the image of the new reparametrisation is an initial segment
of the new interval. This is the library's one `pauseTop` construction: `Extensible.of_top_tail` is its
corollary, with `PastExtensible.of_top_tail`. -/
theorem FutureExtensible.of_top_tail {I₁ I : Set ℝ} {c : ℝ → M} {t₁ : ℝ} (hI₁I : I₁ ⊆ I)
    (hIo : I.OrdConnected) (ht₁ : t₁ ∈ I₁) (hmax : ∀ t ∈ I₁, t ≤ t₁)
    (htail : ∀ t ∈ I, t ∉ I₁ → t₁ < t ∧ c t = c t₁) (hext : C.FutureExtensible W I₁ c) :
    C.FutureExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨ψ₁, hψ, hmaps, hoc, heq, hinit⟩, ⟨t', ht', hgrow⟩⟩ := hext
  obtain ⟨g, hgpos, hg1, hgmono, hginv⟩ := exists_compress
  set a := ψ₁ t₁ with ha
  have hI₁ : ∀ t ∈ I, t ≤ t₁ → t ∈ I₁ := fun t ht hle => by
    by_contra h
    exact absurd hle (not_le.2 (htail t ht h).1)
  have hψa : ∀ t ∈ I₁, ψ₁ t ≤ a := fun t ht => hψ.monotoneOn ht ht₁ (hmax t ht)
  obtain ⟨ψ, hlow, hhigh⟩ : ∃ ψ : ℝ → ℝ, (∀ t, t ≤ t₁ → ψ t = ψ₁ t) ∧
      ∀ t, t₁ < t → ψ t = a + g (t - t₁) :=
    ⟨fun t => if t ≤ t₁ then ψ₁ t else a + g (t - t₁), fun t h => if_pos h,
      fun t h => if_neg (not_le.2 h)⟩
  have hπlow : ∀ t ∈ I, t ≤ t₁ → pauseTop a (ψ t) = ψ₁ t := fun t ht h => by
    rw [hlow t h]; exact pauseTop_of_le (hψa t (hI₁ t ht h))
  have hπhigh : ∀ t, t₁ < t → pauseTop a (ψ t) = a := fun t h => by
    rw [hhigh t h]
    have h0 := hgpos (t - t₁) (by linarith)
    have h1 := hg1 (t - t₁) (by linarith)
    exact pauseTop_of_mem_Icc ⟨by linarith, by linarith⟩
  have hπI : ∀ t ∈ I, pauseTop a (ψ t) ∈ I' := fun t ht => by
    rcases le_or_gt t t₁ with h | h
    · rw [hπlow t ht h]; exact hmaps (hI₁ t ht h)
    · rw [hπhigh t h]; exact hmaps ht₁
  have hval : ∀ t ∈ I, c' (pauseTop a (ψ t)) = c t := fun t ht => by
    rcases le_or_gt t t₁ with h | h
    · rw [hπlow t ht h]; exact heq t (hI₁ t ht h)
    · rw [hπhigh t h, heq t₁ ht₁]
      by_cases hmem : t ∈ I₁
      · exact absurd (hmax t hmem) (not_le.2 h)
      · exact (htail t ht hmem).2.symm
  refine ⟨pauseTop a ⁻¹' I', c' ∘ pauseTop a, ?_,
    ⟨ψ, ?_, fun t ht => hπI t ht, ?_, fun t ht => hval t ht, ?_⟩, ?_⟩
  · refine hcurve.comp_monotoneOn ⟨a, ?_⟩ (hcurve.ordConnected.preimage_mono (monotone_pauseTop a))
      ((monotone_pauseTop a).monotoneOn _) (continuous_pauseTop a).continuousOn (fun u hu => hu)
    show pauseTop a a ∈ I'
    rw [pauseTop_of_le le_rfl]
    exact hmaps ht₁
  · intro t ht t' ht' htt'
    rcases le_or_gt t' t₁ with h' | h'
    · rw [hlow t (htt'.le.trans h'), hlow t' h']
      exact hψ (hI₁ t ht (htt'.le.trans h')) (hI₁ t' ht' h') htt'
    · rw [hhigh t' h']
      rcases le_or_gt t t₁ with h | h
      · rw [hlow t h]
        have := hgpos (t' - t₁) (by linarith)
        linarith [hψa t (hI₁ t ht h)]
      · rw [hhigh t h]
        have := hgmono (t - t₁) (t' - t₁) (by linarith) (by linarith)
        linarith
  · refine ⟨?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z ⟨hz1, hz2⟩
    by_cases hza : z ≤ a
    · have hx' : x ≤ t₁ := by
        by_contra h
        push Not at h
        rw [hhigh x h] at hz1
        have := hgpos (x - t₁) (by linarith)
        linarith
      rw [hlow x hx'] at hz1
      obtain ⟨w, hw, hwz⟩ := hoc.out (mem_image_of_mem ψ₁ (hI₁ x hx hx'))
        (mem_image_of_mem ψ₁ ht₁) ⟨hz1, hza⟩
      exact ⟨w, hI₁I hw, by rw [hlow w (hmax w hw)]; exact hwz⟩
    · push Not at hza
      have hy' : t₁ < y := by
        by_contra h
        push Not at h
        rw [hlow y h] at hz2
        linarith [hψa y (hI₁ y hy h)]
      rw [hhigh y hy'] at hz2
      have hu1 : z - a < 1 := by have := hg1 (y - t₁) (by linarith); linarith
      obtain ⟨x₀, hx₀, hgx₀⟩ := hginv (z - a) (by linarith) hu1
      have hxle : x₀ ≤ y - t₁ := by
        by_contra hcon
        push Not at hcon
        have := hgmono (y - t₁) x₀ (by linarith) hcon
        linarith
      have hwI : t₁ + x₀ ∈ I := hIo.out (hI₁I ht₁) hy ⟨by linarith, by linarith⟩
      refine ⟨t₁ + x₀, hwI, ?_⟩
      rw [hhigh (t₁ + x₀) (by linarith), show t₁ + x₀ - t₁ = x₀ by ring, hgx₀]
      ring
  · -- the image of `ψ` is an initial segment of the new interval
    intro t ht v hv hvt
    rcases le_or_gt v a with hva | hva
    · have hvI' : v ∈ I' := by
        have h := hv
        rw [mem_preimage, pauseTop_of_le hva] at h
        exact h
      obtain ⟨s, hs, hsv⟩ := hinit t₁ ht₁ v hvI' hva
      exact ⟨s, hI₁I hs, by rw [hlow s (hmax s hs)]; exact hsv⟩
    · have ht₁t : t₁ < t := by
        by_contra h
        push Not at h
        rw [hlow t h] at hvt
        linarith [hψa t (hI₁ t ht h)]
      rw [hhigh t ht₁t] at hvt
      have hu1 : v - a < 1 := by have := hg1 (t - t₁) (by linarith); linarith
      obtain ⟨x₀, hx₀, hgx₀⟩ := hginv (v - a) (by linarith) hu1
      have hxle : x₀ ≤ t - t₁ := by
        by_contra hcon
        push Not at hcon
        have := hgmono (t - t₁) x₀ (by linarith) hcon
        linarith
      refine ⟨t₁ + x₀, hIo.out (hI₁I ht₁) ht ⟨by linarith, by linarith⟩, ?_⟩
      rw [hhigh (t₁ + x₀) (by linarith), show t₁ + x₀ - t₁ = x₀ by ring, hgx₀]
      ring
  · have hπt' : pauseTop a (if t' ≤ a then t' else t' + 1) = t' := by
      split_ifs with h
      · exact pauseTop_of_le h
      · push Not at h
        rw [pauseTop_of_ge (by linarith)]
        ring
    refine ⟨if t' ≤ a then t' else t' + 1, ?_, fun t ht => ?_⟩
    · show pauseTop a _ ∈ I'
      rw [hπt']
      exact ht'
    · show c' (pauseTop a _) ≠ c t
      rw [hπt']
      by_cases hmem : t ∈ I₁
      · exact hgrow t hmem
      · rw [(htail t ht hmem).2]
        exact hgrow t₁ ht₁

/-- **An extension at the past end over `I₁` is one over `I`, `I` adding to `I₁` a constant initial
piece**: `FutureExtensible.of_top_tail` read through time reversal. -/
theorem PastExtensible.of_bottom_tail {I₁ I : Set ℝ} {c : ℝ → M} {t₀ : ℝ} (hI₁I : I₁ ⊆ I)
    (hIo : I.OrdConnected) (ht₀ : t₀ ∈ I₁) (hmin : ∀ t ∈ I₁, t₀ ≤ t)
    (htail : ∀ t ∈ I, t ∉ I₁ → t < t₀ ∧ c t = c t₀) (hext : C.PastExtensible W I₁ c) :
    C.PastExtensible W I c := by
  refine PastExtensible.of_dual_reverse ?_
  have hext' : C.dual.FutureExtensible W (-I₁) (fun t => c (-t)) :=
    FutureExtensible.of_dual_reverse (C := C.dual) (by simpa using hext)
  refine FutureExtensible.of_top_tail (C := C.dual) (I₁ := -I₁) (I := -I) (t₁ := -t₀)
    (Set.neg_subset_neg.2 hI₁I) (hIo.preimage_anti fun _ _ h => neg_le_neg h) (by simpa using ht₀)
    (fun t ht => ?_) (fun t ht htI => ?_) hext'
  · have := hmin (-t) ht
    linarith
  · obtain ⟨h1, h2⟩ := htail (-t) ht htI
    exact ⟨by linarith, by simpa using h2⟩

/-- **An extension over `I₁` is one over `I`, `I` adding to `I₁` a constant final piece**: `t₁`
the last parameter of `I₁`, and `c = c t₁` on `I` after it. An extension is one at the past end or
one at the future end (`extensible_iff`; `I₁ ∋ t₁` is non-empty), and each is carried over `I` by
its one-sided lemma: `PastExtensible.of_top_tail` (no pause) or `FutureExtensible.of_top_tail`
(the pause). -/
theorem Extensible.of_top_tail {I₁ I : Set ℝ} {c : ℝ → M} {t₁ : ℝ} (hI₁I : I₁ ⊆ I)
    (hIo : I.OrdConnected) (ht₁ : t₁ ∈ I₁) (hmax : ∀ t ∈ I₁, t ≤ t₁)
    (htail : ∀ t ∈ I, t ∉ I₁ → t₁ < t ∧ c t = c t₁) (hext : C.Extensible W I₁ c) :
    C.Extensible W I c :=
  ((extensible_iff ⟨t₁, ht₁⟩).1 hext).elim
    (fun h => (PastExtensible.of_top_tail hI₁I hIo ht₁ hmax htail h).extensible)
    fun h => (FutureExtensible.of_top_tail hI₁I hIo ht₁ hmax htail h).extensible

/-- **An extension over `I₁` is one over `I`, `I` adding to `I₁` a constant initial piece**:
`Extensible.of_top_tail` through time reversal. -/
theorem Extensible.of_bottom_tail {I₁ I : Set ℝ} {c : ℝ → M} {t₀ : ℝ} (hI₁I : I₁ ⊆ I)
    (hIo : I.OrdConnected) (ht₀ : t₀ ∈ I₁) (hmin : ∀ t ∈ I₁, t₀ ≤ t)
    (htail : ∀ t ∈ I, t ∉ I₁ → t < t₀ ∧ c t = c t₀) (hext : C.Extensible W I₁ c) :
    C.Extensible W I c := by
  refine Extensible.of_dual_reverse ?_
  have hext' : C.dual.Extensible W (-I₁) (fun t => c (-t)) :=
    Extensible.of_dual_reverse (C := C.dual) (by simpa using hext)
  refine Extensible.of_top_tail (C := C.dual) (I₁ := -I₁) (I := -I) (t₁ := -t₀)
    (Set.neg_subset_neg.2 hI₁I) (hIo.preimage_anti fun _ _ h => neg_le_neg h) (by simpa using ht₀)
    (fun t ht => ?_) (fun t ht htI => ?_) hext'
  · have := hmin (-t) ht
    linarith
  · obtain ⟨h1, h2⟩ := htail (-t) ht htI
    exact ⟨by linarith, by simpa using h2⟩

/-- **Inextensibility passes to the trimmed curve**: if `c` is constant off the sub-interval `I₀`
(a monotone retraction `ρ : I → I₀` with `c ∘ ρ = c`, as `exists_tailFree_retraction` gives),
`c` inextensible over `I` is inextensible over `I₀`. -/
theorem Inextensible.of_retraction {I I₀ : Set ℝ} {c : ℝ → M} {ρ : ℝ → ℝ}
    (hc : C.Inextensible W I c) (hI₀I : I₀ ⊆ I) (hne : I₀.Nonempty) (ho : I₀.OrdConnected)
    (hρm : MapsTo ρ I I₀) (hρmono : MonotoneOn ρ I) (hρid : ∀ t ∈ I₀, ρ t = t)
    (hρc : ∀ t ∈ I, c (ρ t) = c t) : C.Inextensible W I₀ c := by
  have hbelow : ∀ t ∈ I, t ∉ I₀ → (∃ s ∈ I₀, t ≤ s) → ∀ s ∈ I₀, t < s := by
    intro t ht htI₀ ⟨s, hs, hts⟩ s' hs'
    by_contra h
    push Not at h
    exact htI₀ (ho.out hs' hs ⟨h, hts⟩)
  have habove : ∀ t ∈ I, t ∉ I₀ → (¬ ∃ s ∈ I₀, t ≤ s) → ∀ s ∈ I₀, s < t := by
    intro t _ _ h s hs
    by_contra h'
    exact h ⟨s, hs, not_lt.1 h'⟩
  -- below `I₀`, the retraction sends every point to the least point of `I₀`
  have hρlow : ∀ t ∈ I, (∀ s ∈ I₀, t < s) → ∀ s ∈ I₀, ρ t ≤ s := fun t ht h s hs => by
    rw [← hρid s hs]; exact hρmono ht (hI₀I hs) (h s hs).le
  have hρhigh : ∀ t ∈ I, (∀ s ∈ I₀, s < t) → ∀ s ∈ I₀, s ≤ ρ t := fun t ht h s hs => by
    rw [← hρid s hs]; exact hρmono (hI₀I hs) ht (h s hs).le
  set I₁ := {t ∈ I | ∃ s ∈ I₀, t ≤ s} with hI₁
  have hI₀I₁ : I₀ ⊆ I₁ := fun t ht => ⟨hI₀I ht, t, ht, le_rfl⟩
  have hI₁I : I₁ ⊆ I := fun t ht => ht.1
  refine ⟨⟨hne, ho, fun a ha b hb => hc.1.curve a (hI₀I ha) b (hI₀I hb)⟩, fun hext => hc.2 ?_⟩
  -- the constant initial piece
  have hext₁ : C.Extensible W I₁ c := by
    by_cases hall : I₁ ⊆ I₀
    · have he : I₁ = I₀ := Subset.antisymm hall hI₀I₁
      rw [he]; exact hext
    obtain ⟨t, ht, htI₀⟩ := not_subset.1 hall
    have htb := hbelow t ht.1 htI₀ ht.2
    have hI₁o : I₁.OrdConnected := ⟨fun x hx y hy z hz => ⟨hc.1.ordConnected.out hx.1 hy.1 hz,
      let ⟨s, hs, hys⟩ := hy.2; ⟨s, hs, hz.2.trans hys⟩⟩⟩
    refine Extensible.of_bottom_tail hI₀I₁ hI₁o (hρm ht.1) (hρlow t ht.1 htb)
      (fun t' ht' ht'I₀ => ?_) hext
    have ht'b := hbelow t' ht'.1 ht'I₀ ht'.2
    have he : ρ t' = ρ t := le_antisymm (hρlow t' ht'.1 ht'b _ (hρm ht.1))
      (hρlow t ht.1 htb _ (hρm ht'.1))
    exact ⟨ht'b _ (hρm ht.1), by rw [← hρc t' ht'.1, he]⟩
  -- the constant final piece
  by_cases hall : I ⊆ I₁
  · have he : I = I₁ := Subset.antisymm hall hI₁I
    rw [he]; exact hext₁
  obtain ⟨t, ht, htI₁⟩ := not_subset.1 hall
  have htI₀ : t ∉ I₀ := fun h => htI₁ (hI₀I₁ h)
  have hta := habove t ht htI₀ (fun h => htI₁ ⟨ht, h⟩)
  refine Extensible.of_top_tail hI₁I hc.1.ordConnected (hI₀I₁ (hρm ht)) (fun x hx => ?_)
    (fun t' ht' ht'I₁ => ?_) hext₁
  · obtain ⟨s, hs, hxs⟩ := hx.2
    exact hxs.trans (hρhigh t ht hta s hs)
  · have ht'I₀ : t' ∉ I₀ := fun h => ht'I₁ (hI₀I₁ h)
    have ht'a := habove t' ht' ht'I₀ (fun h => ht'I₁ ⟨ht', h⟩)
    have he : ρ t' = ρ t := le_antisymm (hρhigh t ht hta _ (hρm ht'))
      (hρhigh t' ht' ht'a _ (hρm ht))
    exact ⟨ht'a _ (hρm ht), by rw [← hρc t' ht', he]⟩

/-- **Past-inextensibility passes to the trimmed curve**: if `c` is constant off the sub-interval
`I₀` (a monotone retraction `ρ : I → I₀` with `c ∘ ρ = c`, as `exists_tailFree_retraction` gives),
`c` past-inextensible over `I` is past-inextensible over `I₀`. The one-sided twin of
`Inextensible.of_retraction`, through `PastExtensible.of_bottom_tail` and `of_top_tail`. -/
theorem PastInextensible.of_retraction {I I₀ : Set ℝ} {c : ℝ → M} {ρ : ℝ → ℝ}
    (hc : C.PastInextensible W I c) (hI₀I : I₀ ⊆ I) (hne : I₀.Nonempty) (ho : I₀.OrdConnected)
    (hρm : MapsTo ρ I I₀) (hρmono : MonotoneOn ρ I) (hρid : ∀ t ∈ I₀, ρ t = t)
    (hρc : ∀ t ∈ I, c (ρ t) = c t) : C.PastInextensible W I₀ c := by
  have hbelow : ∀ t ∈ I, t ∉ I₀ → (∃ s ∈ I₀, t ≤ s) → ∀ s ∈ I₀, t < s := by
    intro t ht htI₀ ⟨s, hs, hts⟩ s' hs'
    by_contra h
    push Not at h
    exact htI₀ (ho.out hs' hs ⟨h, hts⟩)
  have habove : ∀ t ∈ I, t ∉ I₀ → (¬ ∃ s ∈ I₀, t ≤ s) → ∀ s ∈ I₀, s < t := by
    intro t _ _ h s hs
    by_contra h'
    exact h ⟨s, hs, not_lt.1 h'⟩
  have hρlow : ∀ t ∈ I, (∀ s ∈ I₀, t < s) → ∀ s ∈ I₀, ρ t ≤ s := fun t ht h s hs => by
    rw [← hρid s hs]; exact hρmono ht (hI₀I hs) (h s hs).le
  have hρhigh : ∀ t ∈ I, (∀ s ∈ I₀, s < t) → ∀ s ∈ I₀, s ≤ ρ t := fun t ht h s hs => by
    rw [← hρid s hs]; exact hρmono (hI₀I hs) ht (h s hs).le
  set I₁ := {t ∈ I | ∃ s ∈ I₀, t ≤ s} with hI₁
  have hI₀I₁ : I₀ ⊆ I₁ := fun t ht => ⟨hI₀I ht, t, ht, le_rfl⟩
  have hI₁I : I₁ ⊆ I := fun t ht => ht.1
  refine ⟨⟨hne, ho, fun a ha b hb => hc.1.curve a (hI₀I ha) b (hI₀I hb)⟩, fun hext => hc.2 ?_⟩
  -- the constant initial piece
  have hext₁ : C.PastExtensible W I₁ c := by
    by_cases hall : I₁ ⊆ I₀
    · have he : I₁ = I₀ := Subset.antisymm hall hI₀I₁
      rw [he]; exact hext
    obtain ⟨t, ht, htI₀⟩ := not_subset.1 hall
    have htb := hbelow t ht.1 htI₀ ht.2
    have hI₁o : I₁.OrdConnected := ⟨fun x hx y hy z hz => ⟨hc.1.ordConnected.out hx.1 hy.1 hz,
      let ⟨s, hs, hys⟩ := hy.2; ⟨s, hs, hz.2.trans hys⟩⟩⟩
    refine PastExtensible.of_bottom_tail hI₀I₁ hI₁o (hρm ht.1) (hρlow t ht.1 htb)
      (fun t' ht' ht'I₀ => ?_) hext
    have ht'b := hbelow t' ht'.1 ht'I₀ ht'.2
    have he : ρ t' = ρ t := le_antisymm (hρlow t' ht'.1 ht'b _ (hρm ht.1))
      (hρlow t ht.1 htb _ (hρm ht'.1))
    exact ⟨ht'b _ (hρm ht.1), by rw [← hρc t' ht'.1, he]⟩
  -- the constant final piece
  by_cases hall : I ⊆ I₁
  · have he : I = I₁ := Subset.antisymm hall hI₁I
    rw [he]; exact hext₁
  obtain ⟨t, ht, htI₁⟩ := not_subset.1 hall
  have htI₀ : t ∉ I₀ := fun h => htI₁ (hI₀I₁ h)
  have hta := habove t ht htI₀ (fun h => htI₁ ⟨ht, h⟩)
  refine PastExtensible.of_top_tail hI₁I hc.1.ordConnected (hI₀I₁ (hρm ht)) (fun x hx => ?_)
    (fun t' ht' ht'I₁ => ?_) hext₁
  · obtain ⟨s, hs, hxs⟩ := hx.2
    exact hxs.trans (hρhigh t ht hta s hs)
  · have ht'I₀ : t' ∉ I₀ := fun h => ht'I₁ (hI₀I₁ h)
    have ht'a := habove t' ht' ht'I₀ (fun h => ht'I₁ ⟨ht', h⟩)
    have he : ρ t' = ρ t := le_antisymm (hρhigh t ht hta _ (hρm ht'))
      (hρhigh t' ht' ht'a _ (hρm ht))
    exact ⟨ht'a _ (hρm ht), by rw [← hρc t' ht', he]⟩

end Causality

/-! ## 3. Retractions onto a sub-interval -/

/-- A monotone retraction of `I` onto a sub-interval `I₀` is continuous on `I` (it is
`1`-Lipschitz there). -/
theorem continuousOn_of_retraction {I I₀ : Set ℝ} {ρ : ℝ → ℝ} (hI₀I : I₀ ⊆ I)
    (ho : I₀.OrdConnected) (hρm : MapsTo ρ I I₀) (hρmono : MonotoneOn ρ I)
    (hρid : ∀ t ∈ I₀, ρ t = t) : ContinuousOn ρ I := by
  -- a point moved up lies below `I₀`, a point moved down above it
  have hup : ∀ x ∈ I, x < ρ x → ∀ y ∈ I₀, ρ x ≤ y := fun x hx hlt y hy => by
    have hxy : x < y := by
      by_contra h
      push Not at h
      exact absurd (hρid x (ho.out hy (hρm hx) ⟨h, hlt.le⟩)) hlt.ne'
    rw [← hρid y hy]
    exact hρmono hx (hI₀I hy) hxy.le
  have hdown : ∀ x ∈ I, ρ x < x → ∀ y ∈ I₀, y ≤ ρ x := fun x hx hlt y hy => by
    have hxy : y < x := by
      by_contra h
      push Not at h
      exact absurd (hρid x (ho.out (hρm hx) hy ⟨hlt.le, h⟩)) hlt.ne
    rw [← hρid y hy]
    exact hρmono (hI₀I hy) hx hxy.le
  have hlip : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → ρ y - ρ x ≤ y - x := fun x hx y hy hxy => by
    by_cases h1 : y < ρ y
    · have := hup y hy h1 _ (hρm hx); linarith
    by_cases h2 : ρ x < x
    · have := hdown x hx h2 _ (hρm hy); linarith
    push Not at h1 h2
    linarith
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (by linarith [hρmono hx hy h]), abs_of_nonpos (by linarith)]
    linarith [hlip x hx y hy h]
  · rw [abs_of_nonneg (by linarith [hρmono hy hx h]), abs_of_nonneg (by linarith)]
    linarith [hlip y hy x hx h]

/-- A curve constant off `I₀` (a retraction `ρ : I → I₀` with `c ∘ ρ = c`) has the same image
over `I₀` as over `I`. -/
theorem image_eq_of_retraction {α : Type*} {I I₀ : Set ℝ} {c : ℝ → α} {ρ : ℝ → ℝ}
    (hI₀I : I₀ ⊆ I) (hρm : MapsTo ρ I I₀) (hρc : ∀ t ∈ I, c (ρ t) = c t) : c '' I₀ = c '' I := by
  refine Subset.antisymm (image_mono hI₀I) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨ρ t, hρm ht, hρc t ht⟩

/-- Tail-freeness is invariant under time reversal of the parameter. -/
theorem TailFree.neg {α : Type*} {I : Set ℝ} {c : ℝ → α} (h : TailFree I c) :
    TailFree (-I) (fun t => c (-t)) := by
  refine ⟨fun t ht t' ht' htt' => ?_, fun t ht t' ht' htt' => ?_⟩
  · obtain ⟨s, hs, hst, hne⟩ := h.2 (-t) ht (-t') ht' (neg_lt_neg htt')
    exact ⟨-s, by simpa using hs, by linarith, by simpa using hne⟩
  · obtain ⟨s, hs, hst, hne⟩ := h.1 (-t) ht (-t') ht' (neg_lt_neg htt')
    exact ⟨-s, by simpa using hs, by linarith, by simpa using hne⟩

/-! ## 4. The sub-arc form -/

namespace Causality

/-- **The sub-arc form, tail-free case**: in a T1, second countable space, a tail-free causal
curve `c` of `W` over `I` is `γ ∘ ψ` on `I`, with `γ` an inextensible, tail-free causal curve of
`W` over `J` and `ψ : I → J` strictly increasing, continuous, with ordconnected image. -/
theorem exists_subArc_of_tailFree [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) (htf : TailFree I c) :
    ∃ (J : Set ℝ) (γ : ℝ → M) (ψ : ℝ → ℝ), C.Inextensible W J γ ∧ TailFree J γ ∧
      StrictMonoOn ψ I ∧ ContinuousOn ψ I ∧ MapsTo ψ I J ∧ (ψ '' I).OrdConnected ∧
      ∀ t ∈ I, γ (ψ t) = c t := by
  let X : C.TailFreeCurve W := ⟨(I, c), hc, htf⟩
  obtain ⟨Z, f, hf, hZ⟩ := AbstractDev.exists_isMaximal_of_chainsInherit
    tailFreeMor_morphismsCompose tailFreeMor_chainsInherit X
  have hmono : StrictMonoOn (intervalMap f) I := strictMonoOn_intervalMap hf.1
  have hoc : (intervalMap f '' I).OrdConnected := by
    have : intervalMap f '' X.1.1 = range fun t => (f t : ℝ) := image_intervalMap f
    rw [show I = X.1.1 from rfl, this]
    exact hf.2.1
  refine ⟨Z.1.1, Z.1.2, intervalMap f, tailFreeMor_inextensible_of_isMaximal hZ, Z.2.2, hmono,
    continuousOn_of_strictMonoOn_ordConnected hc.ordConnected hmono hoc, mapsTo_intervalMap f,
    hoc, fun t ht => ?_⟩
  rw [intervalMap_apply f ht]
  exact hf.2.2 ⟨t, ht⟩

/-- **The sub-arc form of the curves theorem** (T1, second countable): every causal curve `c` of
`W` over `I` is constant off a sub-interval `I₀` (a monotone retraction `ρ : I → I₀` with
`c ∘ ρ = c`), tail-free on `I₀`, and on `I₀` it is `γ ∘ ψ` for an inextensible, tail-free causal
curve `γ` of `W` over `J` and a strictly increasing, continuous `ψ : I₀ → J` with ordconnected
image. -/
theorem exists_subArc_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {C : Causality M} {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    ∃ I₀ ⊆ I, ∃ ρ : ℝ → ℝ, I₀.Nonempty ∧ I₀.OrdConnected ∧ TailFree I₀ c ∧ MapsTo ρ I I₀ ∧
      MonotoneOn ρ I ∧ (∀ t ∈ I₀, ρ t = t) ∧ (∀ t ∈ I, c (ρ t) = c t) ∧
      ∃ (J : Set ℝ) (γ : ℝ → M) (ψ : ℝ → ℝ), C.Inextensible W J γ ∧ TailFree J γ ∧
        StrictMonoOn ψ I₀ ∧ ContinuousOn ψ I₀ ∧ MapsTo ψ I₀ J ∧ (ψ '' I₀).OrdConnected ∧
        ∀ t ∈ I₀, γ (ψ t) = c t := by
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc, -⟩ :=
    exists_tailFree_retraction hc.nonempty hc.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hc.curve a ha b hb))
  exact ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc,
    exists_subArc_of_tailFree ⟨hne, ho, fun a ha b hb => hc.curve a (hI₀I ha) b (hI₀I hb)⟩ htf⟩

/-- **An inextensible curve of a smaller open set, trimmed**: an inextensible causal curve `c` of
`W ≤ U` (T1, second countable) has a sub-interval `I₀` with `c '' I₀ = c '' I` on which it is
tail-free and still inextensible in `W`, and there `c = γ ∘ ψ` for an inextensible causal curve
`γ` of `U` and a strictly increasing, continuous `ψ` with ordconnected image. -/
theorem Inextensible.exists_subArc_of_le [T1Space M] [SecondCountableTopology M]
    {C : Causality M} {W U : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible W I c)
    (hWU : W ≤ U) :
    ∃ I₀ ⊆ I, C.Inextensible W I₀ c ∧ TailFree I₀ c ∧ c '' I₀ = c '' I ∧
      ∃ (J : Set ℝ) (γ : ℝ → M) (ψ : ℝ → ℝ), C.Inextensible U J γ ∧ TailFree J γ ∧
        StrictMonoOn ψ I₀ ∧ ContinuousOn ψ I₀ ∧ MapsTo ψ I₀ J ∧ (ψ '' I₀).OrdConnected ∧
        ∀ t ∈ I₀, γ (ψ t) = c t := by
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc, -⟩ :=
    exists_tailFree_retraction hc.1.nonempty hc.1.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hc.1.curve a ha b hb))
  exact ⟨I₀, hI₀I, hc.of_retraction hI₀I hne ho hρm hρmono hρid hρc, htf,
    image_eq_of_retraction hI₀I hρm hρc,
    exists_subArc_of_tailFree ⟨hne, ho, fun a ha b hb =>
      CurveOn.mono_opens C.isRelFamily_le (hc.1.curve a (hI₀I ha) b (hI₀I hb)) hWU⟩ htf⟩

section

variable {C : Causality M} {W : Opens M}

/-- **A sub-arc with room below is extensible at the past end**: if `c = γ ∘ ψ` on `I`, `ψ` strictly
increasing with ordconnected image, and `γ` has a parameter `u` below all of `ψ '' I` with a value
`γ u` that `c` does not take, then `γ`, cut at the top of `ψ '' I`, strictly extends `c` at the
past end. -/
theorem pastExtensible_of_subArc {I J : Set ℝ} {c γ : ℝ → M} {ψ : ℝ → ℝ} (hI : I.Nonempty)
    (hγ : C.CausalCurveIn W J γ) (hψ : StrictMonoOn ψ I) (hmaps : MapsTo ψ I J)
    (hoc : (ψ '' I).OrdConnected) (heq : ∀ t ∈ I, γ (ψ t) = c t) {u : ℝ} (hu : u ∈ J)
    (hbelow : ∀ t ∈ I, u < ψ t) (hnew : ∀ t ∈ I, γ u ≠ c t) : C.PastExtensible W I c := by
  obtain ⟨t₀, ht₀⟩ := hI
  refine ⟨J ∩ {v | ∃ t ∈ I, v ≤ ψ t}, γ, ⟨⟨u, hu, t₀, ht₀, (hbelow t₀ ht₀).le⟩,
    ⟨fun x hx y hy z hz => ?_⟩, fun a ha b hb => hγ.curve a ha.1 b hb.1⟩,
    ⟨ψ, hψ, fun t ht => ⟨hmaps ht, t, ht, le_rfl⟩, hoc, heq, ?_⟩,
    ⟨u, ⟨hu, t₀, ht₀, (hbelow t₀ ht₀).le⟩, hnew⟩⟩
  · obtain ⟨t, ht, hyt⟩ := hy.2
    exact ⟨hγ.ordConnected.out hx.1 hy.1 hz, t, ht, hz.2.trans hyt⟩
  · rintro t ht v ⟨-, t₂, ht₂, hvt₂⟩ htv
    exact hoc.out (mem_image_of_mem ψ ht) (mem_image_of_mem ψ ht₂) ⟨htv, hvt₂⟩

end

/-! ## 5. `inextensible_nested ⇒ curve_nested` -/

/-- **Inextensible nesting gives curve nesting on a T1, second countable space** (the ladder's
`[[open]]` entry `inextensible_nested → curve_nested`): a causal curve of `W` for `C` over a
segment is, trimmed, a reparametrised sub-arc of an inextensible `C`-curve of `W`, which is a
`C'`-curve by the nesting, and its constant end pieces are read through the retraction. -/
theorem InextensibleNestedOn.curveNestedOn_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {C C' : Causality M} {W : Opens M}
    (h : C.InextensibleNestedOn C' W) : C.CurveNestedOn C' W := by
  intro c a b hc
  rcases lt_or_ge b a with hba | hab
  · exact CurveOn.of_lt hba
  obtain ⟨I₀, hI₀I, ρ, hne, ho, -, hρm, hρmono, hρid, hρc, J, γ, ψ, hγ, -, hψ, hψc, hψm, -,
    heq⟩ := exists_subArc_of_t1_secondCountable (hc.causalCurveIn_Icc hab)
  have h1 : C'.CausalCurveIn W I₀ (γ ∘ ψ) := (h hγ).1.comp hne ho hψ hψc hψm
  have h2 : C'.CausalCurveIn W (Icc a b) ((γ ∘ ψ) ∘ ρ) :=
    h1.comp_monotoneOn (nonempty_Icc.2 hab) ordConnected_Icc hρmono
      (continuousOn_of_retraction hI₀I ho hρm hρmono hρid) hρm
  have h3 : C'.CausalCurveIn W (Icc a b) c := h2.congr fun t ht => by
    simp only [Function.comp_apply]
    rw [heq _ (hρm ht), hρc t ht]
  exact h3.curve a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩

end Causality

end Causal
