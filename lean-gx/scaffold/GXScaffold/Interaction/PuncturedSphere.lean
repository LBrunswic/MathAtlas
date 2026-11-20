import GX.Branched.Paths

/-!
# The punctured disc and the annulus: the `π₁` relations behind Theorem M

Research target `T-3p1-theorem-m` (`roadmap/roadmap.toml`; `papers/bbs/NOTES-3+1.md`, N4,
l.316–360). There is no ledger label: the target reports under the pseudo-labels `N4:M1`,
`N4:M2`, `N4:M3`, `N4:theorem-M`, and **nothing is marked** (the master records research
results). This file is the topological half of (M1)–(M3), in `π₁` of a model;
`GXScaffold.Interaction.TheoremM` pushes it to holonomies. Every proof here is complete.

> Choose a base point on C₋, with arcs to the p_i in the cyclic order the orientation induces
> (BBS l.621–623). (NOTES-3+1.md l.335–336)
>
> Proof: π₁(D₋ ∖ {p_i}) is free on loops γ_i around the p_i, and a loop parallel to C₋ inside D₋
> is homotopic to γ₁⋯γ_a. (l.339–340)
>
> At the level of holonomy, this is topology: a loop parallel to C₋ is homotopic across the
> regular annulus A to a loop parallel to C₊. (l.345–346)
>
> Write P(x) ∈ PSL(2,ℝ) ≅ SO₀(1,2) for the holonomy of a small positive loop around x. (l.329)

## Main declarations

* `GX.punctDisc a` — the model of a closed disc with `a` punctures: the rectangle
  `[-1,1] × [0,a]` minus the points `(0, j + 1/2)`, `j < a`. `GX.PunctDisc.base a = (-1,0)`, on
  the boundary; `GX.PunctDisc.boundary a`, the boundary loop, counterclockwise;
  `GX.PunctDisc.lasso a k` (`k : Fin a`): up the left side (the arc), once counterclockwise
  around the square `[-1,1] × [j,j+1]`, `j = a - k - 1`, back down; `GX.PunctDisc.puncture a k`.
* `GX.PunctDisc.cls_boundary` — **the disc relation**: `[∂] = [γ₀] * [γ₁] * ⋯ * [γ_{a-1}]` in
  `π₁(punctDisc a, base)`. By telescoping (`GX.PunctDisc.lassoProd_eq`): groupoid algebra on the
  edges, no homotopy to build.
* `GX.PunctDisc.cls_lasso_eq_small`, `GX.PunctDisc.dist_smallSq_le` — the lassos are **small
  positive loops**: for every `0 < r < 1/2`, `[γₖ] = [τ · sᵣ · τ⁻¹]`, `sᵣ` the counterclockwise
  square of half-side `r` around the `k`-th puncture (four straight-line homotopies in boxes
  avoiding the punctures, `GX.PunctDisc.mk_sq_eq_small`).
* `GX.mk_eq_conj_of_annulus` — **the annulus lemma**: for `Φ : [0,1]² → X` with
  `Φ(s,0) = Φ(s,1) = τ(s)`, `Φ(0,·) ≃ τ · Φ(1,·) · τ⁻¹` rel endpoints.
* Tools: `GX.homotopic_of_convex_subset` (straight-line homotopy in a convex part of a subspace),
  `GX.segIn`, `GX.quot_symm_trans_distrib`.

## Hypothesis checklist

| notes | here |
|---|---|
| `D₋` a disc carrying `p₁ … p_a` | ✓ carried: the model, a closed disc with `a` punctures |
| arcs to the `pᵢ` in the cyclic order the orientation induces | ⚠ read: the model's arcs (SCOPE (a)) |
| `γᵢ` a small positive loop around `pᵢ` | ✓ `cls_lasso_eq_small` |
| `π₁(D₋ ∖ {pᵢ})` free on the `γᵢ` | not proved, not used: (M1) needs only the relation (SCOPE (b)) |
| `A` a regular annulus | ✓ any map of the square periodic in the second variable |

## SCOPE (disclosed)

* **(a)** "Arcs in the cyclic order" is read as: the arcs are the images of the model's tethers
  under a parametrisation of the closed disc. The model's tethers are not disjoint: they all run
  up the side `x = -1`, and `tL k` is an initial segment of `tL (k+1)`. An arbitrarily small
  perturbation separates them, in the order of SCOPE (c). What is true, and what the relations
  use, holds after a homeomorphism of the closed disc taking the punctures to the model's, and
  up to homotopy rel endpoints in the punctured disc. Then every system of disjoint arcs from a
  boundary point to the punctures, in the cyclic order, is homotopic to the model's tethers
  (Schoenflies; classical, not formalized). The lasso classes depend only on the homotopy classes
  of the tethers. The relations hold for every continuous map of the model, embedded or not.
* **(b)** The freeness of `π₁(D₋ ∖ {pᵢ})`, which the notes' proof mentions, is not formalized:
  the statement of (M1) needs only `[∂] = ∏ [γᵢ]`, which is proved.
* **(c)** Products are mathlib's: `π₁` is `End` in the fundamental groupoid, `[γ] * [δ] = [δ · γ]`
  (`δ` run first). So `cls_boundary` says `∂ ≃ γ_{a-1} ⋯ γ₁ γ₀` as a concatenation. At the base
  point, counterclockwise from the direction in which `∂` leaves it, the arcs reach the punctures
  of `γ_{a-1}, …, γ₀` in that order.
* **(d)** "Positive" is the counterclockwise orientation of the model `ℝ²`; on a surface it is
  whatever orientation the parametrisation carries (see `GXScaffold.Interaction.TheoremM`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Branched.Paths` (`pathToSub`, `cWinding`).
-/

noncomputable section

open Set Function unitInterval

namespace GX

set_option linter.unusedSectionVars false

/-! ### Straight-line homotopies inside a convex part of a subspace -/

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {S : Set E}

/-- Two paths of a subspace `S` with the same ends, both with values in a convex `K ⊆ S`, are
homotopic in `S` (straight-line homotopy). -/
theorem homotopic_of_convex_subset {K : Set E} (hK : Convex ℝ K) (hKS : K ⊆ S) {x y : S}
    {p q : Path x y} (hp : ∀ t, (p t : E) ∈ K) (hq : ∀ t, (q t : E) ∈ K) : p.Homotopic q :=
  ⟨{ toFun := fun w => ⟨AffineMap.lineMap (p w.2 : E) (q w.2 : E) (w.1 : ℝ),
        hKS (hK.lineMap_mem (hp _) (hq _) w.1.2)⟩
     continuous_toFun := by
       refine Continuous.subtype_mk ?_ _
       simp only [AffineMap.lineMap_apply_module]
       fun_prop
     map_zero_left := fun t => Subtype.ext (by simp)
     map_one_left := fun t => Subtype.ext (by simp)
     prop' := fun s t ht => by
       rcases ht with rfl | rfl
       · exact Subtype.ext (by simp)
       · exact Subtype.ext (by simp) }⟩

/-- The straight segment between two points of a convex `K ⊆ S`, as a path of `S`. -/
def segIn {K : Set E} (hK : Convex ℝ K) (hKS : K ⊆ S) {p q : E} (hp : p ∈ K) (hq : q ∈ K) :
    Path (⟨p, hKS hp⟩ : S) ⟨q, hKS hq⟩ :=
  pathToSub (Path.segment p q) fun t => hKS (by
    rw [Path.segment_apply]; exact hK.lineMap_mem hp hq t.2)

theorem segIn_apply {K : Set E} (hK : Convex ℝ K) (hKS : K ⊆ S) {p q : E} (hp : p ∈ K)
    (hq : q ∈ K) (t : I) : (segIn hK hKS hp hq t : E) = AffineMap.lineMap p q (t : ℝ) := rfl

/-- The values of a segment lie in every convex set containing its ends. -/
theorem segIn_mem {K : Set E} (hK : Convex ℝ K) (hKS : K ⊆ S) {p q : E} (hp : p ∈ K) (hq : q ∈ K)
    {K' : Set E} (hK' : Convex ℝ K') (hp' : p ∈ K') (hq' : q ∈ K') (t : I) :
    (segIn hK hKS hp hq t : E) ∈ K' := by
  rw [segIn_apply]; exact hK'.lineMap_mem hp' hq' t.2

theorem trans_val_mem {x y z : S} {p : Path x y} {q : Path y z} {K : Set E}
    (hp : ∀ t, (p t : E) ∈ K) (hq : ∀ t, (q t : E) ∈ K) (t : I) :
    ((p.trans q) t : E) ∈ K := by
  rw [Path.trans_apply]; split_ifs
  · exact hp _
  · exact hq _

theorem symm_val_mem {x y : S} {p : Path x y} {K : Set E} (hp : ∀ t, (p t : E) ∈ K) (t : I) :
    (p.symm t : E) ∈ K := hp _

end Convex

/-! ### Cancellation in the fundamental groupoid -/

section Cancel

variable {X : Type*} [TopologicalSpace X]

theorem quot_symm_trans_cancel {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) :
    (p.symm.trans (p.trans q)) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem quot_trans_symm_cancel {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x z) :
    (p.trans (p.symm.trans q)) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

theorem quot_symm_trans_distrib {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_trans, Path.trans_symm]

end Cancel

/-! ### The model: a closed disc with `a` punctures -/

/-- **The model punctured disc**: the closed rectangle `[-1,1] × [0,a]` (a closed disc) with the
`a` points `(0, j + 1/2)`, `j < a`, removed. -/
def punctDisc (a : ℕ) : Set (ℝ × ℝ) :=
  {z | z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) a ∧ ∀ j : ℕ, j < a → z ≠ ((0 : ℝ), (j : ℝ) + 1 / 2)}

namespace PunctDisc

variable {a : ℕ}

theorem ne_half_of_le_of_lt {y : ℝ} {k : ℕ} (h1 : (k : ℝ) ≤ y) (h2 : y < k + 1 / 2) (j : ℕ) :
    y ≠ j + 1 / 2 := by
  intro h
  rw [h] at h1 h2
  have hkj : k < j + 1 := by exact_mod_cast (by linarith : (k : ℝ) < j + 1)
  have : (k : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.mp hkj
  linarith

theorem ne_half_of_lt_of_le {y : ℝ} {k : ℕ} (h1 : (k : ℝ) + 1 / 2 < y) (h2 : y ≤ k + 1) (j : ℕ) :
    y ≠ j + 1 / 2 := by
  intro h
  rw [h] at h1 h2
  have hkj : k < j := by exact_mod_cast (by linarith : (k : ℝ) < j)
  have hjk : j < k + 1 := by exact_mod_cast (by linarith : (j : ℝ) < k + 1)
  omega

theorem natCast_ne_half (n j : ℕ) : (n : ℝ) ≠ j + 1 / 2 := by
  intro h
  have h2 : ((2 * n : ℕ) : ℝ) = ((2 * j + 1 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective h2
  omega

/-- A point of the closed rectangle off the vertical line `x = 0`, or off the half-integer
heights, is a point of the model. -/
theorem mem_of {z : ℝ × ℝ} (h1 : -1 ≤ z.1) (h2 : z.1 ≤ 1) (h3 : 0 ≤ z.2) (h4 : z.2 ≤ a)
    (h : z.1 ≠ 0 ∨ ∀ j : ℕ, z.2 ≠ j + 1 / 2) : z ∈ punctDisc a := by
  refine ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, fun j _ hz => ?_⟩
  rcases h with h | h
  · exact h (by rw [hz])
  · exact h j (by rw [hz])

/-- A box `[x₁,x₂] × [y₁,y₂]` of the rectangle avoiding the punctures lies in the model. -/
theorem box_subset {x₁ x₂ y₁ y₂ : ℝ} (h1 : -1 ≤ x₁) (h2 : x₂ ≤ 1) (h3 : 0 ≤ y₁) (h4 : y₂ ≤ a)
    (h : ∀ z ∈ Icc x₁ x₂ ×ˢ Icc y₁ y₂, z.1 ≠ 0 ∨ ∀ j : ℕ, z.2 ≠ j + 1 / 2) :
    Icc x₁ x₂ ×ˢ Icc y₁ y₂ ⊆ punctDisc a := fun z hz =>
  mem_of (h1.trans hz.1.1) (hz.1.2.trans h2) (h3.trans hz.2.1) (hz.2.2.trans h4) (h z hz)

theorem convex_box (x₁ x₂ y₁ y₂ : ℝ) : Convex ℝ (Icc x₁ x₂ ×ˢ Icc y₁ y₂) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

/-- The clamped height `min k a` of the `k`-th vertex. -/
def ht (a k : ℕ) : ℝ := ((min k a : ℕ) : ℝ)

theorem ht_nonneg (a k : ℕ) : 0 ≤ ht a k := Nat.cast_nonneg _

theorem ht_le (a k : ℕ) : ht a k ≤ a := by
  unfold ht; exact_mod_cast min_le_right _ _

theorem ht_le_succ (a k : ℕ) : ht a k ≤ ht a (k + 1) := by
  unfold ht; exact_mod_cast min_le_min_right _ (Nat.le_succ k)

theorem ht_of_le {a k : ℕ} (h : k ≤ a) : ht a k = k := by
  unfold ht; rw [min_eq_left h]

/-- The vertical line `x = -1` of the rectangle. -/
theorem leftLine_subset : Icc (-1 : ℝ) (-1) ×ˢ Icc (0 : ℝ) a ⊆ punctDisc a :=
  box_subset le_rfl (by norm_num) le_rfl le_rfl fun z hz => Or.inl (by
    have : z.1 = -1 := le_antisymm hz.1.2 hz.1.1
    rw [this]; norm_num)

/-- The vertical line `x = 1` of the rectangle. -/
theorem rightLine_subset : Icc (1 : ℝ) 1 ×ˢ Icc (0 : ℝ) a ⊆ punctDisc a :=
  box_subset (by norm_num) le_rfl le_rfl le_rfl fun z hz => Or.inl (by
    have : z.1 = 1 := le_antisymm hz.1.2 hz.1.1
    rw [this]; norm_num)

/-- The horizontal line at the vertex height `ht a k`. -/
theorem hLine_subset (k : ℕ) :
    Icc (-1 : ℝ) 1 ×ˢ Icc (ht a k) (ht a k) ⊆ punctDisc a :=
  box_subset le_rfl le_rfl (ht_nonneg a k) (ht_le a k) fun z hz => Or.inr fun j => by
    have : z.2 = ht a k := le_antisymm hz.2.2 hz.2.1
    rw [this]; exact natCast_ne_half _ j

theorem leftVtx_mem (k : ℕ) : ((-1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) (-1) ×ˢ Icc (0 : ℝ) a :=
  ⟨⟨le_rfl, le_rfl⟩, ⟨ht_nonneg a k, ht_le a k⟩⟩

theorem rightVtx_mem (k : ℕ) : ((1 : ℝ), ht a k) ∈ Icc (1 : ℝ) 1 ×ˢ Icc (0 : ℝ) a :=
  ⟨⟨le_rfl, le_rfl⟩, ⟨ht_nonneg a k, ht_le a k⟩⟩

theorem leftVtx_mem_h (k : ℕ) :
    ((-1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (ht a k) (ht a k) :=
  ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, le_rfl⟩⟩

theorem rightVtx_mem_h (k : ℕ) :
    ((1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (ht a k) (ht a k) :=
  ⟨⟨by norm_num, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩

variable (a)

/-- The left vertex `(-1, min k a)`. -/
def vL (k : ℕ) : punctDisc a := ⟨((-1 : ℝ), ht a k), leftLine_subset (leftVtx_mem k)⟩

/-- The right vertex `(1, min k a)`. -/
def vR (k : ℕ) : punctDisc a := ⟨((1 : ℝ), ht a k), rightLine_subset (rightVtx_mem k)⟩

/-- **The base point** `(-1, 0)`, a corner of the rectangle, on its boundary. -/
abbrev base : punctDisc a := vL a 0

/-- The horizontal edge at height `min k a`, from left to right. -/
def hE (k : ℕ) : Path (vL a k) (vR a k) :=
  segIn ((convex_Icc _ _).prod (convex_Icc _ _)) (hLine_subset k) (leftVtx_mem_h k)
    (rightVtx_mem_h k)

/-- The left vertical edge from height `min k a` to `min (k+1) a`, upwards. -/
def lE (k : ℕ) : Path (vL a k) (vL a (k + 1)) :=
  segIn ((convex_Icc _ _).prod (convex_Icc _ _)) leftLine_subset (leftVtx_mem k)
    (leftVtx_mem (k + 1))

/-- The right vertical edge from height `min k a` to `min (k+1) a`, upwards. -/
def rE (k : ℕ) : Path (vR a k) (vR a (k + 1)) :=
  segIn ((convex_Icc _ _).prod (convex_Icc _ _)) rightLine_subset (rightVtx_mem k)
    (rightVtx_mem (k + 1))

/-- The left side from the base point up to height `min k a`: the tether of the `k`-th
square. -/
def tL : (k : ℕ) → Path (base a) (vL a k)
  | 0 => Path.refl _
  | k + 1 => (tL k).trans (lE a k)

/-- The right side from `(1, 0)` up to height `min k a`. -/
def tR : (k : ℕ) → Path (vR a 0) (vR a k)
  | 0 => Path.refl _
  | k + 1 => (tR k).trans (rE a k)

/-- The `k`-th square `[-1,1] × [k,k+1]` (for `k < a`), positively oriented from its lower left
corner: bottom, right, top (backwards), left (downwards). -/
def sq (k : ℕ) : Path (vL a k) (vL a k) :=
  (((hE a k).trans (rE a k)).trans (hE a (k + 1)).symm).trans (lE a k).symm

/-- The `k`-th lasso in the geometric numbering: up the left side, once around the `k`-th
square, back down. -/
def lassoG (k : ℕ) : Path (base a) (base a) :=
  ((tL a k).trans (sq a k)).trans (tL a k).symm

/-- The positively oriented boundary of `[-1,1] × [0, min m a]`, from the base point. -/
def bdryG (m : ℕ) : Path (base a) (base a) :=
  (((hE a 0).trans (tR a m)).trans (hE a m).symm).trans (tL a m).symm

/-- **The boundary loop** `∂`: the boundary of the rectangle, positively (counterclockwise)
oriented, from the base point `(-1,0)`: along the bottom, up the right side, back along the top,
down the left side. -/
def boundary : Path (base a) (base a) := bdryG a a

/-- **The `k`-th lasso** `γₖ`, `k : Fin a`: the lasso around the puncture `(0, a - k - 1/2)`, the
`k`-th from the top. -/
def lasso (k : Fin a) : Path (base a) (base a) := lassoG a (a - (k + 1))

/-- **The `k`-th puncture**, `(0, a - k - 1/2)`, encircled by `lasso a k`. -/
def puncture (k : Fin a) : ℝ × ℝ := ((0 : ℝ), ((a - (k + 1) : ℕ) : ℝ) + 1 / 2)

/-! ### The boundary relation -/

/-- The ordered concatenation of the first `m` lassos (geometric numbering), in the fundamental
groupoid. -/
def lassoProd : ℕ → Path.Homotopic.Quotient (base a) (base a)
  | 0 => Path.Homotopic.Quotient.refl _
  | m + 1 => (lassoProd m).trans (Path.Homotopic.Quotient.mk (lassoG a m))

/-- **The telescoping identity**: the concatenation `γ₀ ⋯ γ_{m-1}` of the first `m` lassos is
homotopic to the boundary of `[-1,1] × [0, min m a]`. Pure groupoid algebra on the edges. -/
theorem lassoProd_eq (m : ℕ) : lassoProd a m = Path.Homotopic.Quotient.mk (bdryG a m) := by
  induction m with
  | zero =>
    show Path.Homotopic.Quotient.refl _ = _
    simp [bdryG, tR, tL, Path.refl_symm]
  | succ m ih =>
    show (lassoProd a m).trans _ = _
    rw [ih]
    simp only [bdryG, lassoG, sq, tR, tL, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm,
      quot_symm_trans_distrib, Path.Homotopic.Quotient.trans_assoc, quot_symm_trans_cancel]

/-- The class in `π₁(punctDisc a, base)` of a loop at the base point. -/
abbrev cls (γ : Path (base a) (base a)) : FundamentalGroup (punctDisc a) (base a) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)

/-- The concatenation of the first `m` lassos, as a product in `π₁` (mathlib's product is the
composition `x * y = y ≫ x`: the right factor is run first). -/
theorem fromPath_lassoProd (m : ℕ) :
    FundamentalGroup.fromPath (lassoProd a m) =
      (List.ofFn fun k : Fin m => cls a (lassoG a (m - (k + 1)))).prod := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have e : (List.ofFn fun k : Fin m => cls a (lassoG a (m + 1 - ((k.succ : ℕ) + 1)))) =
        List.ofFn fun k : Fin m => cls a (lassoG a (m - (k + 1))) := by
      congr 1; funext k
      rw [show m + 1 - ((k.succ : ℕ) + 1) = m - (k + 1) by rw [Fin.val_succ]; omega]
    have e0 : m + 1 - (((0 : Fin (m + 1)) : ℕ) + 1) = m := by simp
    rw [e, ← ih, e0]
    rfl

/-- **The boundary relation (M1, topological core).** In `π₁(punctDisc a, base)`, the class of the
positively oriented boundary loop is the ordered product of the classes of the lassos:
`[∂] = [γ₀] * [γ₁] * ⋯ * [γ_{a-1}]` (mathlib's group law on `π₁`: `[γ] * [δ]` runs `δ` first; as
a concatenation of paths, `∂ ≃ γ_{a-1} ⋯ γ₁ γ₀`, the lasso of the lowest puncture first). -/
theorem cls_boundary :
    cls a (boundary a) = (List.ofFn fun k : Fin a => cls a (lasso a k)).prod := by
  show cls a (bdryG a a) = (List.ofFn fun k : Fin a => cls a (lassoG a (a - (k + 1)))).prod
  rw [← fromPath_lassoProd, lassoProd_eq]

/-! ### The lassos are small positive loops around the punctures

The square `[-1,1] × [k,k+1]` and the small square of half-side `r` around its puncture
`(0, k + 1/2)` bound a frame made of four trapezoids, each inside a box of the model avoiding the
puncture; the straight-line homotopies in the four boxes move one square onto the other. -/

section Small

variable {a} {k : ℕ} {r : ℝ}

theorem boxB_subset (hk : k < a) (hr0 : 0 < r) :
    Icc (-1 : ℝ) 1 ×ˢ Icc (k : ℝ) (k + 1 / 2 - r) ⊆ punctDisc a := by
  have hka : (k : ℝ) + 1 ≤ a := by exact_mod_cast hk
  refine box_subset le_rfl le_rfl (Nat.cast_nonneg _) (by linarith) fun z hz => Or.inr fun j => ?_
  exact ne_half_of_le_of_lt hz.2.1 (by linarith [hz.2.2]) j

theorem boxT_subset (hk : k < a) (hr0 : 0 < r) :
    Icc (-1 : ℝ) 1 ×ˢ Icc ((k : ℝ) + 1 / 2 + r) (k + 1) ⊆ punctDisc a := by
  have hka : (k : ℝ) + 1 ≤ a := by exact_mod_cast hk
  refine box_subset le_rfl le_rfl (by positivity) hka fun z hz => Or.inr fun j => ?_
  exact ne_half_of_lt_of_le (by linarith [hz.2.1]) hz.2.2 j

theorem boxR_subset (hk : k < a) (hr0 : 0 < r) :
    Icc r 1 ×ˢ Icc (k : ℝ) (k + 1) ⊆ punctDisc a := by
  have hka : (k : ℝ) + 1 ≤ a := by exact_mod_cast hk
  refine box_subset (by linarith) le_rfl (Nat.cast_nonneg _) hka fun z hz => Or.inl ?_
  linarith [hz.1.1]

theorem boxL_subset (hk : k < a) (hr0 : 0 < r) :
    Icc (-1 : ℝ) (-r) ×ˢ Icc (k : ℝ) (k + 1) ⊆ punctDisc a := by
  have hka : (k : ℝ) + 1 ≤ a := by exact_mod_cast hk
  refine box_subset le_rfl (by linarith) (Nat.cast_nonneg _) hka fun z hz => Or.inl ?_
  linarith [hz.1.2]

theorem ht_succ_of_lt (hk : k < a) : ht a (k + 1) = (k : ℝ) + 1 := by
  rw [ht_of_le hk]; push_cast; ring

/-- The lower left corner `(-r, k + 1/2 - r)` of the small square. -/
def cBL (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : punctDisc a :=
  ⟨(-r, (k : ℝ) + 1 / 2 - r), boxB_subset hk hr0
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩⟩⟩

/-- The lower right corner `(r, k + 1/2 - r)`. -/
def cBR (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : punctDisc a :=
  ⟨(r, (k : ℝ) + 1 / 2 - r), boxB_subset hk hr0
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩⟩⟩

/-- The upper right corner `(r, k + 1/2 + r)`. -/
def cTR (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : punctDisc a :=
  ⟨(r, (k : ℝ) + 1 / 2 + r), boxT_subset hk hr0
    ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, by linarith⟩⟩⟩

/-- The upper left corner `(-r, k + 1/2 + r)`. -/
def cTL (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : punctDisc a :=
  ⟨(-r, (k : ℝ) + 1 / 2 + r), boxT_subset hk hr0
    ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, by linarith⟩⟩⟩

section Pts

variable (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2)
include hk hr0 hr

theorem vLk_memB : ((-1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (k : ℝ) (k + 1 / 2 - r) := by
  rw [ht_of_le hk.le]; exact ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by linarith⟩⟩

theorem vRk_memB : ((1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (k : ℝ) (k + 1 / 2 - r) := by
  rw [ht_of_le hk.le]; exact ⟨⟨by norm_num, le_rfl⟩, ⟨le_rfl, by linarith⟩⟩

theorem vRk_memR : ((1 : ℝ), ht a k) ∈ Icc r 1 ×ˢ Icc (k : ℝ) (k + 1) := by
  rw [ht_of_le hk.le]; exact ⟨⟨by linarith, le_rfl⟩, ⟨le_rfl, by linarith⟩⟩

theorem vRk1_memR : ((1 : ℝ), ht a (k + 1)) ∈ Icc r 1 ×ˢ Icc (k : ℝ) (k + 1) := by
  rw [ht_succ_of_lt hk]; exact ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, le_rfl⟩⟩

theorem vRk1_memT :
    ((1 : ℝ), ht a (k + 1)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc ((k : ℝ) + 1 / 2 + r) (k + 1) := by
  rw [ht_succ_of_lt hk]; exact ⟨⟨by norm_num, le_rfl⟩, ⟨by linarith, le_rfl⟩⟩

theorem vLk1_memT :
    ((-1 : ℝ), ht a (k + 1)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc ((k : ℝ) + 1 / 2 + r) (k + 1) := by
  rw [ht_succ_of_lt hk]; exact ⟨⟨le_rfl, by norm_num⟩, ⟨by linarith, le_rfl⟩⟩

theorem vLk1_memL : ((-1 : ℝ), ht a (k + 1)) ∈ Icc (-1 : ℝ) (-r) ×ˢ Icc (k : ℝ) (k + 1) := by
  rw [ht_succ_of_lt hk]; exact ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩

theorem vLk_memL : ((-1 : ℝ), ht a k) ∈ Icc (-1 : ℝ) (-r) ×ˢ Icc (k : ℝ) (k + 1) := by
  rw [ht_of_le hk.le]; exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩

theorem cBL_memB : (-r, (k : ℝ) + 1 / 2 - r) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (k : ℝ) (k + 1 / 2 - r) :=
  ⟨⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩⟩

theorem cBR_memB : (r, (k : ℝ) + 1 / 2 - r) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (k : ℝ) (k + 1 / 2 - r) :=
  ⟨⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩⟩

theorem cBR_memR : (r, (k : ℝ) + 1 / 2 - r) ∈ Icc r 1 ×ˢ Icc (k : ℝ) (k + 1) :=
  ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem cTR_memR : (r, (k : ℝ) + 1 / 2 + r) ∈ Icc r 1 ×ˢ Icc (k : ℝ) (k + 1) :=
  ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem cTR_memT : (r, (k : ℝ) + 1 / 2 + r) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc ((k : ℝ) + 1 / 2 + r) (k + 1) :=
  ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, by linarith⟩⟩

theorem cTL_memT :
    (-r, (k : ℝ) + 1 / 2 + r) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc ((k : ℝ) + 1 / 2 + r) (k + 1) :=
  ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, by linarith⟩⟩

theorem cTL_memL : (-r, (k : ℝ) + 1 / 2 + r) ∈ Icc (-1 : ℝ) (-r) ×ˢ Icc (k : ℝ) (k + 1) :=
  ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩⟩

theorem cBL_memL : (-r, (k : ℝ) + 1 / 2 - r) ∈ Icc (-1 : ℝ) (-r) ×ˢ Icc (k : ℝ) (k + 1) :=
  ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩⟩

end Pts

theorem hE_mem (a k : ℕ) {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hp : ((-1 : ℝ), ht a k) ∈ K)
    (hq : ((1 : ℝ), ht a k) ∈ K) (t : I) : (hE a k t : ℝ × ℝ) ∈ K :=
  segIn_mem _ _ _ _ hK hp hq t

theorem lE_mem (a k : ℕ) {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hp : ((-1 : ℝ), ht a k) ∈ K)
    (hq : ((-1 : ℝ), ht a (k + 1)) ∈ K) (t : I) : (lE a k t : ℝ × ℝ) ∈ K :=
  segIn_mem _ _ _ _ hK hp hq t

theorem rE_mem (a k : ℕ) {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hp : ((1 : ℝ), ht a k) ∈ K)
    (hq : ((1 : ℝ), ht a (k + 1)) ∈ K) (t : I) : (rE a k t : ℝ × ℝ) ∈ K :=
  segIn_mem _ _ _ _ hK hp hq t

/-- The diagonal from the lower left corner of the `k`-th square to that of the small square. -/
def dBL (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (vL a k) (cBL hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxB_subset hk hr0) (vLk_memB hk hr0 hr) (cBL_memB hk hr0 hr)

/-- The diagonal from the lower right corner of the `k`-th square to that of the small square. -/
def dBR (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (vR a k) (cBR hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxB_subset hk hr0) (vRk_memB hk hr0 hr) (cBR_memB hk hr0 hr)

/-- The diagonal from the upper right corner of the `k`-th square to that of the small square. -/
def dTR (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (vR a (k + 1)) (cTR hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxR_subset hk hr0) (vRk1_memR hk hr0 hr) (cTR_memR hk hr0 hr)

/-- The diagonal from the upper left corner of the `k`-th square to that of the small square. -/
def dTL (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (vL a (k + 1)) (cTL hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxT_subset hk hr0) (vLk1_memT hk hr0 hr) (cTL_memT hk hr0 hr)

/-- The bottom side of the small square. -/
def sB (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (cBL hk hr0 hr) (cBR hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxB_subset hk hr0) (cBL_memB hk hr0 hr) (cBR_memB hk hr0 hr)

/-- The right side of the small square. -/
def sR (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (cBR hk hr0 hr) (cTR hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxR_subset hk hr0) (cBR_memR hk hr0 hr) (cTR_memR hk hr0 hr)

/-- The top side of the small square, backwards. -/
def sT (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (cTR hk hr0 hr) (cTL hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxT_subset hk hr0) (cTR_memT hk hr0 hr) (cTL_memT hk hr0 hr)

/-- The left side of the small square, downwards. -/
def sL (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (cTL hk hr0 hr) (cBL hk hr0 hr) :=
  segIn (convex_box _ _ _ _) (boxL_subset hk hr0) (cTL_memL hk hr0 hr) (cBL_memL hk hr0 hr)

section SegMem

variable (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
include hK

theorem dBL_mem (hp : ((-1 : ℝ), ht a k) ∈ K) (hq : (-r, (k : ℝ) + 1 / 2 - r) ∈ K) (t : I) :
    (dBL hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem dBR_mem (hp : ((1 : ℝ), ht a k) ∈ K) (hq : (r, (k : ℝ) + 1 / 2 - r) ∈ K) (t : I) :
    (dBR hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem dTR_mem (hp : ((1 : ℝ), ht a (k + 1)) ∈ K) (hq : (r, (k : ℝ) + 1 / 2 + r) ∈ K) (t : I) :
    (dTR hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem dTL_mem (hp : ((-1 : ℝ), ht a (k + 1)) ∈ K) (hq : (-r, (k : ℝ) + 1 / 2 + r) ∈ K)
    (t : I) : (dTL hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem sB_mem (hp : (-r, (k : ℝ) + 1 / 2 - r) ∈ K) (hq : (r, (k : ℝ) + 1 / 2 - r) ∈ K) (t : I) :
    (sB hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem sR_mem (hp : (r, (k : ℝ) + 1 / 2 - r) ∈ K) (hq : (r, (k : ℝ) + 1 / 2 + r) ∈ K) (t : I) :
    (sR hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem sT_mem (hp : (r, (k : ℝ) + 1 / 2 + r) ∈ K) (hq : (-r, (k : ℝ) + 1 / 2 + r) ∈ K) (t : I) :
    (sT hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

theorem sL_mem (hp : (-r, (k : ℝ) + 1 / 2 + r) ∈ K) (hq : (-r, (k : ℝ) + 1 / 2 - r) ∈ K) (t : I) :
    (sL hk hr0 hr t : ℝ × ℝ) ∈ K := segIn_mem _ _ _ _ hK hp hq t

end SegMem

/-- **The small square** of half-side `r` around the puncture `(0, k + 1/2)`, positively
(counterclockwise) oriented from its lower left corner. -/
def smallSq (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (cBL hk hr0 hr) (cBL hk hr0 hr) :=
  (((sB hk hr0 hr).trans (sR hk hr0 hr)).trans (sT hk hr0 hr)).trans (sL hk hr0 hr)

/-- **The tether** of the small square: up the left side to height `k`, then the diagonal to the
lower left corner of the small square. -/
def smallTether (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) : Path (base a) (cBL hk hr0 hr) :=
  (tL a k).trans (dBL hk hr0 hr)

/-- The small square stays in the closed box of half-side `r` around the puncture. -/
theorem smallSq_mem (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) (t : I) :
    (smallSq hk hr0 hr t : ℝ × ℝ) ∈ Icc (-r) r ×ˢ Icc ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r) := by
  have hK := convex_box (-r) r ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r)
  have pBL : (-r, (k : ℝ) + 1 / 2 - r) ∈ Icc (-r) r ×ˢ Icc ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r) :=
    ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
  have pBR : (r, (k : ℝ) + 1 / 2 - r) ∈ Icc (-r) r ×ˢ Icc ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r) :=
    ⟨⟨by linarith, le_rfl⟩, ⟨le_rfl, by linarith⟩⟩
  have pTR : (r, (k : ℝ) + 1 / 2 + r) ∈ Icc (-r) r ×ˢ Icc ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r) :=
    ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, le_rfl⟩⟩
  have pTL : (-r, (k : ℝ) + 1 / 2 + r) ∈ Icc (-r) r ×ˢ Icc ((k : ℝ) + 1 / 2 - r) (k + 1 / 2 + r) :=
    ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩
  exact trans_val_mem (trans_val_mem (trans_val_mem (sB_mem hk hr0 hr hK pBL pBR)
    (sR_mem hk hr0 hr hK pBR pTR)) (sT_mem hk hr0 hr hK pTR pTL)) (sL_mem hk hr0 hr hK pTL pBL) t

/-- **The `k`-th square is homotopic to the small square around its puncture**, conjugated by
the diagonal: `□ₖ ≃ d · s_r · d⁻¹` in the punctured model, for every `0 < r < 1/2`. -/
theorem mk_sq_eq_small (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) :
    Path.Homotopic.Quotient.mk (sq a k) =
      Path.Homotopic.Quotient.mk ((dBL hk hr0 hr).trans
        ((smallSq hk hr0 hr).trans (dBL hk hr0 hr).symm)) := by
  have cB := convex_box (-1 : ℝ) 1 (k : ℝ) (k + 1 / 2 - r)
  have cR := convex_box r 1 (k : ℝ) (k + 1)
  have cT := convex_box (-1 : ℝ) 1 ((k : ℝ) + 1 / 2 + r) (k + 1)
  have cL := convex_box (-1 : ℝ) (-r) (k : ℝ) (k + 1)
  have h1 : Path.Homotopic.Quotient.mk (hE a k) = Path.Homotopic.Quotient.mk
      ((dBL hk hr0 hr).trans ((sB hk hr0 hr).trans (dBR hk hr0 hr).symm)) :=
    Path.Homotopic.Quotient.eq.2 (homotopic_of_convex_subset cB (boxB_subset hk hr0)
      (hE_mem a k cB (vLk_memB hk hr0 hr) (vRk_memB hk hr0 hr))
      (trans_val_mem (dBL_mem hk hr0 hr cB (vLk_memB hk hr0 hr) (cBL_memB hk hr0 hr))
        (trans_val_mem (sB_mem hk hr0 hr cB (cBL_memB hk hr0 hr) (cBR_memB hk hr0 hr))
          (symm_val_mem (dBR_mem hk hr0 hr cB (vRk_memB hk hr0 hr) (cBR_memB hk hr0 hr))))))
  have h2 : Path.Homotopic.Quotient.mk (rE a k) = Path.Homotopic.Quotient.mk
      ((dBR hk hr0 hr).trans ((sR hk hr0 hr).trans (dTR hk hr0 hr).symm)) :=
    Path.Homotopic.Quotient.eq.2 (homotopic_of_convex_subset cR (boxR_subset hk hr0)
      (rE_mem a k cR (vRk_memR hk hr0 hr) (vRk1_memR hk hr0 hr))
      (trans_val_mem (dBR_mem hk hr0 hr cR (vRk_memR hk hr0 hr) (cBR_memR hk hr0 hr))
        (trans_val_mem (sR_mem hk hr0 hr cR (cBR_memR hk hr0 hr) (cTR_memR hk hr0 hr))
          (symm_val_mem (dTR_mem hk hr0 hr cR (vRk1_memR hk hr0 hr) (cTR_memR hk hr0 hr))))))
  have h3 : Path.Homotopic.Quotient.mk (hE a (k + 1)).symm = Path.Homotopic.Quotient.mk
      ((dTR hk hr0 hr).trans ((sT hk hr0 hr).trans (dTL hk hr0 hr).symm)) :=
    Path.Homotopic.Quotient.eq.2 (homotopic_of_convex_subset cT (boxT_subset hk hr0)
      (symm_val_mem (hE_mem a (k + 1) cT (vLk1_memT hk hr0 hr) (vRk1_memT hk hr0 hr)))
      (trans_val_mem (dTR_mem hk hr0 hr cT (vRk1_memT hk hr0 hr) (cTR_memT hk hr0 hr))
        (trans_val_mem (sT_mem hk hr0 hr cT (cTR_memT hk hr0 hr) (cTL_memT hk hr0 hr))
          (symm_val_mem (dTL_mem hk hr0 hr cT (vLk1_memT hk hr0 hr) (cTL_memT hk hr0 hr))))))
  have h4 : Path.Homotopic.Quotient.mk (lE a k).symm = Path.Homotopic.Quotient.mk
      ((dTL hk hr0 hr).trans ((sL hk hr0 hr).trans (dBL hk hr0 hr).symm)) :=
    Path.Homotopic.Quotient.eq.2 (homotopic_of_convex_subset cL (boxL_subset hk hr0)
      (symm_val_mem (lE_mem a k cL (vLk_memL hk hr0 hr) (vLk1_memL hk hr0 hr)))
      (trans_val_mem (dTL_mem hk hr0 hr cL (vLk1_memL hk hr0 hr) (cTL_memL hk hr0 hr))
        (trans_val_mem (sL_mem hk hr0 hr cL (cTL_memL hk hr0 hr) (cBL_memL hk hr0 hr))
          (symm_val_mem (dBL_mem hk hr0 hr cL (vLk_memL hk hr0 hr) (cBL_memL hk hr0 hr))))))
  have e : sq a k = (((hE a k).trans (rE a k)).trans (hE a (k + 1)).symm).trans (lE a k).symm :=
    rfl
  rw [e, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, h1, h2, h3, h4]
  simp only [smallSq, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, quot_symm_trans_cancel]

/-- **The lasso is a small positive loop around its puncture.** For every `0 < r < 1/2`, the
`k`-th lasso (geometric numbering, `k < a`) is homotopic in the punctured model to the small
square of half-side `r` around `(0, k + 1/2)`, conjugated by its tether. -/
theorem mk_lassoG_eq_small (hk : k < a) (hr0 : 0 < r) (hr : r < 1 / 2) :
    Path.Homotopic.Quotient.mk (lassoG a k) =
      Path.Homotopic.Quotient.mk ((smallTether hk hr0 hr).trans
        ((smallSq hk hr0 hr).trans (smallTether hk hr0 hr).symm)) := by
  have e : lassoG a k = ((tL a k).trans (sq a k)).trans (tL a k).symm := rfl
  rw [e, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    mk_sq_eq_small hk hr0 hr]
  simp only [smallTether, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    quot_symm_trans_distrib, Path.Homotopic.Quotient.trans_assoc]

/-- `a - (k + 1) < a`: the geometric index of the `k`-th lasso. -/
theorem geom_lt (k : Fin a) : a - ((k : ℕ) + 1) < a := by omega

/-- **The `k`-th lasso is a small positive loop around the `k`-th puncture** (`k : Fin a`): for
every `0 < r < 1/2`, `[γₖ] = [τ · sᵣ · τ⁻¹]` in `π₁(punctDisc a, base)`, where `sᵣ` is the
counterclockwise square of half-side `r` around `puncture a k` and `τ` its tether. -/
theorem cls_lasso_eq_small (k : Fin a) (hr0 : 0 < r) (hr : r < 1 / 2) :
    cls a (lasso a k) = cls a ((smallTether (geom_lt k) hr0 hr).trans
      ((smallSq (geom_lt k) hr0 hr).trans (smallTether (geom_lt k) hr0 hr).symm)) :=
  congrArg FundamentalGroup.fromPath (mk_lassoG_eq_small (geom_lt k) hr0 hr)

/-- The small square of `cls_lasso_eq_small` lies in the closed ball of radius `r` around the
puncture (`ℝ × ℝ` carries the sup distance). -/
theorem dist_smallSq_le (k : Fin a) (hr0 : 0 < r) (hr : r < 1 / 2) (t : I) :
    dist (smallSq (geom_lt k) hr0 hr t : ℝ × ℝ) (puncture a k) ≤ r := by
  have h := smallSq_mem (geom_lt k) hr0 hr t
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  simp only [puncture]
  exact ⟨abs_le.2 ⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
    abs_le.2 ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩

end Small

end PunctDisc

/-! ### Freely homotopic loops are conjugate (the annulus) -/

section Annulus

variable {X : Type*} [TopologicalSpace X]

/-- The unit interval is contractible (a convex set). -/
theorem contractibleSpace_unitInterval : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, ⟨le_rfl, zero_le_one⟩⟩

/-- The left side `t ↦ (0,t)` of the square. -/
def sqLeft : Path ((0, 0) : I × I) (0, 1) where
  toFun t := (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The bottom side `s ↦ (s,0)` of the square. -/
def sqBottom : Path ((0, 0) : I × I) (1, 0) where
  toFun s := (s, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right side `t ↦ (1,t)` of the square. -/
def sqRight : Path ((1, 0) : I × I) (1, 1) where
  toFun t := (1, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top side `s ↦ (s,1)` of the square. -/
def sqTop : Path ((0, 1) : I × I) (1, 1) where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- **The annulus lemma.** Let `Φ : [0,1]² → X` be an annulus: `Φ(s,0) = Φ(s,1) = τ(s)`, with
inner loop `α = Φ(0,·)` and outer loop `β = Φ(1,·)`. Then `α ≃ τ · β · τ⁻¹` rel endpoints: freely
homotopic loops are conjugate by the track of the base point. -/
theorem mk_eq_conj_of_annulus (Φ : C(I × I, X)) {x y : X} (α : Path x x) (β : Path y y)
    (τ : Path x y) (hα : ∀ t, Φ (0, t) = α t) (hβ : ∀ t, Φ (1, t) = β t)
    (hτ₀ : ∀ s, Φ (s, 0) = τ s) (hτ₁ : ∀ s, Φ (s, 1) = τ s) :
    Path.Homotopic.Quotient.mk α = Path.Homotopic.Quotient.mk (τ.trans (β.trans τ.symm)) := by
  haveI := contractibleSpace_unitInterval
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic sqLeft
    (sqBottom.trans (sqRight.trans sqTop.symm))
  refine Path.Homotopic.Quotient.eq.2 ⟨
    { toFun := fun w => Φ (F w)
      continuous_toFun := by fun_prop
      map_zero_left := fun t => by
        show Φ (F (0, t)) = α t
        rw [F.apply_zero]; exact hα t
      map_one_left := fun t => by
        show Φ (F (1, t)) = (τ.trans (β.trans τ.symm)) t
        have e : F (1, t) = (sqBottom.trans (sqRight.trans sqTop.symm)) t := F.apply_one t
        rw [e, Path.trans_apply, Path.trans_apply]
        split_ifs with h1
        · exact hτ₀ _
        · rw [Path.trans_apply, Path.trans_apply]
          split_ifs with h2
          · exact hβ _
          · exact hτ₁ _
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · show Φ (F (s, 0)) = α 0
          rw [F.source, Path.source]; exact (hα 0).trans α.source
        · show Φ (F (s, 1)) = α 1
          rw [F.target, Path.target]; exact (hα 1).trans α.target }⟩

end Annulus

end GX
