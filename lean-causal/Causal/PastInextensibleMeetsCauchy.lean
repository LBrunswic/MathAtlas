import Causal.CExtConnexeCauchy.SubArc
import Causal.CauchyDual

/-!
# A past-inextensible causal curve through J⁺(S) meets the Cauchy surface S

Programme target `T-abs-past-inextensible-meets-cauchy` (`programme/roadmap.toml`; layer 1: it
imports `Causal.CExtConnexeCauchy.SubArc` and `Causal.CauchyDual`, both ETT-layer; no model; no
metric, curve length or geodesic in a statement). There is no statement of `ETT.tex` behind it, so
**no label is marked**. It is Sbierski 2312.07443's (2.4), the last step of his Thm 1.5:

> Otherwise, if it were to cross the graph of f , it would give rise, via ι−1 , to a past directed
> past inextendible causal curve in M which starts in I + (Σ, M ) but does not intersect Σ – which
> contradicts Σ being a Cauchy hypersurface. (`references/sbierski/text/sbierski2023c.txt:356–358`)

> The curve σ := ι−1 ◦ σ̃ is now a future directed timelike curve in M which is past-inextendible
> […] To the future it contains a point in I + γ(s0 ), M ⊆ I + {t0 } × Sd , M by (4.1), but it does
> not intersect the Cauchy hypersurface {t0 } × Sd by (4.3). This is a contradiction
> (`sbierski2023c.txt:1139–1144`)

## What is proved (no `sorry`)

1. **The theorem** (`Causality.PastInextensible.exists_mem_of_mem_Jplus`): on a T1, second
   countable space, `S` a Cauchy surface of a causally arc-connected open `W` (DEC-14) on which
   `≤_W` is antisymmetric, every past-inextensible causal curve of `W` (DEC-13) with a point in
   `J⁺(S, W)` meets `S`. **No tail-freeness is assumed.** Its time reversal
   (`FutureInextensible.exists_mem_of_mem_Jminus`); Sbierski's `I⁺` forms
   (`exists_mem_of_mem_Iplus`, `exists_mem_of_mem_Iminus`); the ladder forms at `M`
   (`…_of_isCausal`: `is_causal`, `causally_arc_connected`).
2. **The tail-free case** (`exists_mem_of_mem_Jplus_of_tailFree`), the target's three cases. The
   extension form of the target's step (a) is the library's `Causality.exists_subArc_of_tailFree`
   (`Causal/CExtConnexeCauchy/SubArc.lean:422`): a tail-free curve is `Z ∘ ψ` for an inextensible
   `Z`, `ψ` strictly increasing with ordconnected image. It is imported, not restated.
3. **The trimming removes the hypothesis** (`PastInextensible.of_retraction`): past-inextensible
   over `I` is past-inextensible over the trimmed `I₀` of `exists_tailFree_retraction`, the
   one-sided twin of `Inextensible.of_retraction` (`SubArc.lean:305`). It needs two end-piece
   lemmas: `PastExtensible.of_top_tail` (append the constant final piece, no pause) and
   `PastExtensible.of_bottom_tail` (pause; the time reversal of `FutureExtensible.of_top_tail`,
   which is `Extensible.of_top_tail`'s construction with the initial-segment property kept).
4. **The past extension of a sub-arc** (`pastExtensible_of_subArc`): `γ` cut at the top of
   `ψ '' I` strictly extends `γ ∘ ψ` at the past end when it has a new value below `ψ '' I`.
5. **Witnesses** (kb/0011): the timelike line, `S = {0}`, `id` over `]-∞, 1]` (past) and over
   `[-1, ∞[` (future), with the theorem applied (`timelikeLine_pastInextensible_meets_zero`,
   `timelikeLine_futureInextensible_meets_zero`).

## Hypothesis checklist

| the target's statement / Sbierski (2.4) | here |
|---|---|
| T1, second countable | ✓ `[T1Space M] [SecondCountableTopology M]`: the curves theorem and the trimming |
| `S` a Cauchy surface of `W` ("Σ a Cauchy hypersurface") | ✓ `C.IsCauchySurfaceOn W S` (DEC-14); `W = ⊤` is `M` |
| `W` causally arc-connected | ✓ `C.CausallyArcConnectedOn W`: acausality of `S` (`eq_of_le_of_t1_secondCountable`) |
| `≤_W` antisymmetric | ✓ inline, the shape of `hcaus` in `Causal.Ers482Solution`; used once, `q ≤ x ≤ q` |
| σ past-inextensible causal ("past directed past inextendible causal") | ✓ `C.PastInextensible W I σ` (DEC-13), future-directed parameter |
| a point in `J⁺(S, W)` ("starts in I⁺(Σ, M)") | ⚠ weakened: any point of σ, in `J⁺ ⊇ I⁺`; the `I⁺` form is a corollary |
| σ tail-free (the target's allowance) | ⚠ weakened: not assumed (`PastInextensible.of_retraction`) |
| conclusion: σ meets `S` | ✓ `∃ t ∈ I, σ t ∈ S` |

## SCOPE (disclosed)

* **Nothing marked**: no label of `ETT.tex`. No binder exists for 2312.07443.
* **Sharpness is argued, not formalized.** Antisymmetry: a ray glued to a circle at `q`, curves
  up the ray and around the circle, `S = {y}` (`y ≠ q` on the circle) is Cauchy, the ray is
  past-inextensible, `q ∈ J⁺(S)` along the circle, and the ray misses `S`. Arc-connectedness: two
  timelike lines with a non-local `(s, 0) ≤_M (r, 1)` (`s ≤ 0 ≤ r + 1`) keep the curves and the
  Cauchy surface `{0} × {0, 1}` (kb/0038) and are antisymmetric, but `id` over `]-∞, -1]` on line
  `1` has the point `(-1, 1) ∈ J⁺(S)` and misses `S`. In a Lorentzian spacetime with a Cauchy
  hypersurface both hold automatically.
* `causal_ladder` is not used: no statement concludes a ladder property, and `≤_W` antisymmetric is
  inline (no ladder node at an open `W`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W : Opens M}

/-- **An extension at the past end over `I₁` is one over `I`, `I` adding to `I₁` a constant final
piece**: `t₁` the last parameter of `I₁`, and `c = c t₁` on `I` after it. No pause is needed: the
new curve is the old one followed by its value at `φ t₁`, read through `v ↦ min v (φ t₁)`, over the
old interval and a translate of the final piece. (`Extensible.of_top_tail` does not keep the
extension at the past end: its pause adds parameters above the image of the reparametrisation.) -/
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
piece**: the construction of `Extensible.of_top_tail` (the old extension paused at `ψ₁ t₁` by
`pauseTop`, the piece compressed to length `< 1`), with the initial-segment property kept. -/
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

/-- **The tail-free case.** A tail-free past-inextensible causal curve `σ` of `W` with a point in
`J⁺(S, W)` meets the Cauchy surface `S` of `W`. The curve is `γ ∘ ψ` for an inextensible `γ`
(`exists_subArc_of_tailFree`), and `γ` meets `S` at `γ u`. If `γ u` is on `σ`, done. If `u` lies
at or above `ψ tq` (`x ≤_W σ tq`, `x ∈ S`), then `x ≤_W σ tq ≤_W γ u`, so `x = γ u` by acausality,
and `σ tq = x` by antisymmetry. Otherwise `u` lies below `ψ '' I`, and `γ` strictly extends `σ`
at the past end (`pastExtensible_of_subArc`). -/
theorem PastInextensible.exists_mem_of_mem_Jplus_of_tailFree [T1Space M]
    [SecondCountableTopology M] {S : Set M} {I : Set ℝ} {σ : ℝ → M}
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hσ : C.PastInextensible W I σ)
    (htf : TailFree I σ) (hJ : ∃ t ∈ I, σ t ∈ C.Jplus W S) : ∃ t ∈ I, σ t ∈ S := by
  obtain ⟨tq, htq, x, hxS, hxq⟩ := hJ
  obtain ⟨J, γ, ψ, hγ, -, hψ, -, hmaps, hoc, heq⟩ := exists_subArc_of_tailFree hσ.1 htf
  obtain ⟨y, ⟨⟨u, hu, rfl⟩, hyS⟩, -⟩ := hS J γ hγ
  -- the point where `Z = γ` meets `S` is on `σ`: done
  by_cases hon : ∃ t ∈ I, σ t = γ u
  · obtain ⟨t, ht, he⟩ := hon
    exact ⟨t, ht, he ▸ hyS⟩
  push Not at hon
  rcases le_or_gt (ψ tq) u with hle | hlt
  · -- above `σ (tq)`: `x ≤ σ tq ≤ γ u`, both ends on `S`, so `x = γ u` and `σ tq = x`
    have h1 : C.le W (σ tq) (γ u) := by
      have := hγ.1.le_of_le (hmaps htq) hu hle
      rwa [heq tq htq] at this
    have hxy : x = γ u :=
      hS.eq_of_le_of_t1_secondCountable hC hxS hyS (C.le_trans hxq h1)
    refine ⟨tq, htq, ?_⟩
    rw [hcaus (hxy ▸ h1) hxq]
    exact hxS
  · -- below the whole of `σ`: `γ` strictly extends `σ` at the past end
    exfalso
    have hbelow : ∀ t ∈ I, u < ψ t := by
      intro t ht
      by_contra h
      push Not at h
      obtain ⟨s, hs, hsu⟩ := hoc.out (mem_image_of_mem ψ ht) (mem_image_of_mem ψ htq) ⟨h, hlt.le⟩
      exact hon s hs (by rw [← heq s hs, hsu])
    exact hσ.2 (pastExtensible_of_subArc hσ.1.nonempty hγ.1 hψ hmaps hoc heq hu hbelow
      (fun t ht h => hon t ht h.symm))

/-- **Sbierski 2312.07443 (2.4), in ETT.** On a T1, second countable space, let `S` be a Cauchy
surface of a causally arc-connected open `W` on which `≤_W` is antisymmetric. Then every
past-inextensible causal curve of `W` with a point in `J⁺(S, W)` meets `S`. No tail-freeness is
assumed: the curve is trimmed (`exists_tailFree_retraction`), stays past-inextensible
(`PastInextensible.of_retraction`), and the trimmed curve has the same values. -/
theorem PastInextensible.exists_mem_of_mem_Jplus [T1Space M] [SecondCountableTopology M]
    {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurfaceOn W S)
    (hC : C.CausallyArcConnectedOn W) (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hσ : C.PastInextensible W I σ) (hJ : ∃ t ∈ I, σ t ∈ C.Jplus W S) : ∃ t ∈ I, σ t ∈ S := by
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc, -⟩ :=
    exists_tailFree_retraction hσ.1.nonempty hσ.1.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hσ.1.curve a ha b hb))
  obtain ⟨tq, htq, hq⟩ := hJ
  obtain ⟨t, ht, htS⟩ :=
    (hσ.of_retraction hI₀I hne ho hρm hρmono hρid hρc).exists_mem_of_mem_Jplus_of_tailFree
      hS hC hcaus htf ⟨ρ tq, hρm htq, by rw [hρc tq htq]; exact hq⟩
  exact ⟨t, hI₀I ht, htS⟩

/-- **The time reversal**: every future-inextensible causal curve of `W` with a point in `J⁻(S, W)`
meets `S` (`PastInextensible.exists_mem_of_mem_Jplus` for `C.dual`, the curve run backwards). -/
theorem FutureInextensible.exists_mem_of_mem_Jminus [T1Space M] [SecondCountableTopology M]
    {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurfaceOn W S)
    (hC : C.CausallyArcConnectedOn W) (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hσ : C.FutureInextensible W I σ) (hJ : ∃ t ∈ I, σ t ∈ C.Jminus W S) : ∃ t ∈ I, σ t ∈ S := by
  obtain ⟨tq, htq, hq⟩ := hJ
  obtain ⟨t, ht, htS⟩ := PastInextensible.exists_mem_of_mem_Jplus (C := C.dual)
    (dual_isCauchySurfaceOn.2 hS) (dual_causallyArcConnectedOn.2 hC)
    (fun _ _ h1 h2 => hcaus h2 h1) (dual_pastInextensible_iff.2 hσ)
    ⟨-tq, by simpa using htq, by simpa using hq⟩
  exact ⟨-t, ht, htS⟩

/-- **(2.4) as Sbierski words it**, with a point in `I⁺(S, W)` (`Iplus_subset_Jplus`). -/
theorem PastInextensible.exists_mem_of_mem_Iplus [T1Space M] [SecondCountableTopology M]
    {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurfaceOn W S)
    (hC : C.CausallyArcConnectedOn W) (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hσ : C.PastInextensible W I σ) (hI : ∃ t ∈ I, σ t ∈ C.Iplus W S) : ∃ t ∈ I, σ t ∈ S :=
  let ⟨t, ht, h⟩ := hI
  hσ.exists_mem_of_mem_Jplus hS hC hcaus ⟨t, ht, Iplus_subset_Jplus h⟩

/-- The time reversal, with a point in `I⁻(S, W)`. -/
theorem FutureInextensible.exists_mem_of_mem_Iminus [T1Space M] [SecondCountableTopology M]
    {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurfaceOn W S)
    (hC : C.CausallyArcConnectedOn W) (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hσ : C.FutureInextensible W I σ) (hI : ∃ t ∈ I, σ t ∈ C.Iminus W S) : ∃ t ∈ I, σ t ∈ S :=
  let ⟨t, ht, h⟩ := hI
  hσ.exists_mem_of_mem_Jminus hS hC hcaus ⟨t, ht, Iminus_subset_Jminus h⟩

/-- **The ladder form at `M`**: `C` causal (`is_causal`) and causally arc-connected
(`causally_arc_connected`), `S` a Cauchy surface of `M`, on a T1, second countable space. -/
theorem PastInextensible.exists_mem_of_mem_Jplus_of_isCausal [T1Space M]
    [SecondCountableTopology M] {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurface S)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) (hσ : C.PastInextensible ⊤ I σ)
    (hJ : ∃ t ∈ I, σ t ∈ C.Jplus ⊤ S) : ∃ t ∈ I, σ t ∈ S := by
  exact hσ.exists_mem_of_mem_Jplus hS hC hcaus hJ

/-- The ladder form at `M`, time-reversed. -/
theorem FutureInextensible.exists_mem_of_mem_Jminus_of_isCausal [T1Space M]
    [SecondCountableTopology M] {S : Set M} {I : Set ℝ} {σ : ℝ → M} (hS : C.IsCauchySurface S)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) (hσ : C.FutureInextensible ⊤ I σ)
    (hJ : ∃ t ∈ I, σ t ∈ C.Jminus ⊤ S) : ∃ t ∈ I, σ t ∈ S := by
  exact hσ.exists_mem_of_mem_Jminus hS hC hcaus hJ

end Causality

/-- On the timelike line, `id` over `]-∞, 1]` is past-inextensible in `ℝ`: a new value before the
image would be `≤ 1`, hence a value of `id` on `]-∞, 1]`. -/
theorem timelikeLine_pastInextensible_Iic_one : timelikeLine.PastInextensible ⊤ (Iic 1) id := by
  refine ⟨timelikeLine_causalCurveIn_id nonempty_Iic ordConnected_Iic, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, -, hmaps, -, heq, hfin⟩, ⟨t', ht', hgrow⟩⟩
  have h1 : (1 : ℝ) ∈ Iic (1 : ℝ) := mem_Iic.2 le_rfl
  rcases le_or_gt (φ 1) t' with h | h
  · obtain ⟨s, hs, rfl⟩ := hfin 1 h1 t' ht' h
    exact hgrow s hs (heq s hs)
  · have hle := hcurve.le_of_le ht' (hmaps h1) h.le
    rw [heq 1 h1, timelikeLine_le] at hle
    exact hgrow (c' t') hle.1 rfl

/-- On the timelike line, `id` over `[-1, ∞[` is future-inextensible in `ℝ`. -/
theorem timelikeLine_futureInextensible_Ici_neg_one :
    timelikeLine.FutureInextensible ⊤ (Ici (-1)) id := by
  refine ⟨timelikeLine_causalCurveIn_id nonempty_Ici ordConnected_Ici, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, -, hmaps, -, heq, hinit⟩, ⟨t', ht', hgrow⟩⟩
  have h1 : (-1 : ℝ) ∈ Ici (-1 : ℝ) := mem_Ici.2 le_rfl
  rcases le_or_gt t' (φ (-1)) with h | h
  · obtain ⟨s, hs, rfl⟩ := hinit (-1) h1 t' ht' h
    exact hgrow s hs (heq s hs)
  · have hle := hcurve.le_of_le (hmaps h1) ht' h.le
    rw [heq (-1) h1, timelikeLine_le] at hle
    exact hgrow (c' t') hle.1 rfl

/-- **The witness** (kb/0011): on the timelike line, `S = {0}` is a Cauchy surface of `ℝ`, which
is causally arc-connected with `≤` antisymmetric; `id` over `]-∞, 1]` is past-inextensible, and its
point `1 ∈ J⁺({0})` is not on `S`; the theorem makes it meet `S` (at `0`). -/
theorem timelikeLine_pastInextensible_meets_zero :
    (timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) ∧ timelikeLine.CausallyArcConnectedOn ⊤ ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le ⊤ x y → timelikeLine.le ⊤ y x → x = y) ∧
      timelikeLine.PastInextensible ⊤ (Iic 1) id ∧
      (1 : ℝ) ∈ Iic (1 : ℝ) ∧ id (1 : ℝ) ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∧
      id (1 : ℝ) ∉ ({0} : Set ℝ)) ∧
    ∃ t ∈ Iic (1 : ℝ), id t ∈ ({0} : Set ℝ) := by
  have hS : timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) := timelikeLine_isCauchySurface_zero
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le ⊤ x y → timelikeLine.le ⊤ y x → x = y :=
    timelikeLine_isCausal
  have hJ : id (1 : ℝ) ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) :=
    ⟨0, rfl, timelikeLine_le.2 ⟨zero_le_one, fun _ _ => trivial⟩⟩
  refine ⟨⟨hS, timelikeLine_causallyArcConnected, hcaus, timelikeLine_pastInextensible_Iic_one,
    mem_Iic.2 le_rfl, hJ, by norm_num⟩, ?_⟩
  exact timelikeLine_pastInextensible_Iic_one.exists_mem_of_mem_Jplus hS
    timelikeLine_causallyArcConnected hcaus ⟨1, mem_Iic.2 le_rfl, hJ⟩

/-- The time-reversed witness: `id` over `[-1, ∞[`, its point `-1 ∈ J⁻({0})`, meets `S = {0}`. -/
theorem timelikeLine_futureInextensible_meets_zero :
    (timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) ∧ timelikeLine.CausallyArcConnectedOn ⊤ ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le ⊤ x y → timelikeLine.le ⊤ y x → x = y) ∧
      timelikeLine.FutureInextensible ⊤ (Ici (-1)) id ∧
      (-1 : ℝ) ∈ Ici (-1 : ℝ) ∧ id (-1 : ℝ) ∈ timelikeLine.Jminus ⊤ ({0} : Set ℝ) ∧
      id (-1 : ℝ) ∉ ({0} : Set ℝ)) ∧
    ∃ t ∈ Ici (-1 : ℝ), id t ∈ ({0} : Set ℝ) := by
  have hS : timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) := timelikeLine_isCauchySurface_zero
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le ⊤ x y → timelikeLine.le ⊤ y x → x = y :=
    timelikeLine_isCausal
  have hJ : id (-1 : ℝ) ∈ timelikeLine.Jminus ⊤ ({0} : Set ℝ) :=
    ⟨0, rfl, timelikeLine_le.2 ⟨by norm_num, fun _ _ => trivial⟩⟩
  refine ⟨⟨hS, timelikeLine_causallyArcConnected, hcaus,
    timelikeLine_futureInextensible_Ici_neg_one, mem_Ici.2 le_rfl, hJ, by norm_num⟩, ?_⟩
  exact timelikeLine_futureInextensible_Ici_neg_one.exists_mem_of_mem_Jminus hS
    timelikeLine_causallyArcConnected hcaus ⟨-1, mem_Ici.2 le_rfl, hJ⟩

end Causal
