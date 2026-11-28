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
   (`Causal/CExtConnexeCauchy/SubArc.lean:684`): a tail-free curve is `Z ∘ ψ` for an inextensible
   `Z`, `ψ` strictly increasing with ordconnected image. It is imported, not restated.
3. **Witnesses** (kb/0011): the timelike line, `S = {0}`, `id` over `]-∞, 1]` (past) and over
   `[-1, ∞[` (future), with the theorem applied (`timelikeLine_pastInextensible_meets_zero`,
   `timelikeLine_futureInextensible_meets_zero`).

## What it uses from `Causal.CExtConnexeCauchy.SubArc` (moved there, T-abs-end-pieces-one-sided)

* **The trimming removes the hypothesis** (`PastInextensible.of_retraction`, `SubArc.lean:568`):
  past-inextensible over `I` is past-inextensible over the trimmed `I₀` of
  `exists_tailFree_retraction`, the one-sided twin of `Inextensible.of_retraction`
  (`SubArc.lean:510`). It needs two end-piece lemmas: `PastExtensible.of_top_tail` (append the
  constant final piece, no pause; `SubArc.lean:218`) and `PastExtensible.of_bottom_tail` (pause;
  `SubArc.lean:462`, the time reversal of `FutureExtensible.of_top_tail`, `SubArc.lean:335`).
* **The past extension of a sub-arc** (`pastExtensible_of_subArc`, `SubArc.lean:748`): `γ` cut at
  the top of `ψ '' I` strictly extends `γ ∘ ψ` at the past end when it has a new value below
  `ψ '' I`.

These five lemmas were proved in this module (T-abs-past-inextensible-meets-cauchy).
T-abs-end-pieces-one-sided moved them to `Causal.CExtConnexeCauchy.SubArc`, with their full names,
statements and proofs. The reason: `FutureExtensible.of_top_tail` repeated the pause construction of
SubArc's `Extensible.of_top_tail` with one more property proved, and SubArc is upstream of this
module, so `Extensible.of_top_tail` could become their corollary (through `extensible_iff`) only
once they sat there. They are pure curve topology, with no Cauchy surface. What stays here is (2.4)
itself, its tail-free case, its other forms and its witnesses.

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
* The trimming's and the sub-arc's lemmas (`PastInextensible.of_retraction`, the three end-piece
  lemmas, `pastExtensible_of_subArc`) are not in this module since T-abs-end-pieces-one-sided: they
  are in `Causal.CExtConnexeCauchy.SubArc` (above), with the same full names.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W : Opens M}

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
