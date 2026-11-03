import Causal.Flat.Bieberbach

/-!
# `Causal.Flat.BieberbachMinSet` — a commutative group of Euclidean isometries acts by translations on its common minimal set

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.1,
the prose item **[5.B]** of `docs/BARBOT.md` (l.1720–1735). Package WP-Bieb-3 (DEC-110). **No
ledger label is certified here**: this is step (2a) of the proof of Bieberbach I through virtual
abelianity — Barbot's "affine subspace on which Γ acts by translations" (l.1729–1735), for an
abelian group.

> If `L(Γ)` is not discrete, we consider the unique maximal unipotent affine subspace associated
> to `Γ_nd` […] The proof is completed by the observation that unipotent elements of `Isom(U)`
> are translations. (l.1729–1735)

The argument (no discreteness).
* `minSet g` — the **minimal set** of `g`: the `x` with `L(g) (g x − x) = g x − x` (`g x − x`
  has no component in `range (L(g) − 1) = Fix(L(g))^⊥`; it is where the displacement is
  minimal). An affine subspace, the preimage of `ker (L(g) − 1)` by the affine map `x ↦ g x − x`.
* `eq_zero_of_map_eq_of_eq_map_sub` — for an isometry `A`, `Fix(A) ∩ range(A − 1) = 0` (the
  inner-product computation `⟪v, v⟫ = ⟪A u, A v⟫ − ⟪u, v⟫`).
* `exists_sub_map_sub_fixed` — on an `A`-invariant subspace `D`, every `w ∈ D` is a fixed vector
  plus some `A u − u`, `u ∈ D` (rank–nullity for `(A − 1)|_D`).
* `vsub_eq_of_mem_minSet` — `g` moves every point of `minSet g` by the same vector
  (`(g x − x) − (g y − y) = (L(g) − 1)(x − y)` lies in `Fix(L(g)) ∩ range(L(g) − 1) = 0`).
* `apply_mem_minSet_of_commute` — an `h` commuting with `g` preserves `minSet g`.
* `exists_mem_minSet_of_invariant` — a nonempty `g`-invariant affine subspace `S` meets
  `minSet g` (on `D = S.direction`, `L(g)`-invariant, `ker (L − 1) ⊕ range (L − 1) = D`).
* `exists_subset_minSet_of_commute` — for a commutative `A`, a nonempty `A`-invariant `U` of
  **minimal dimension** (well-founded on `finrank U.direction`) lies in every `minSet γ`: else
  `U ⊓ minSet γ` is nonempty, `A`-invariant and of the same dimension, hence `U`.
* `exists_actsByTranslationsOn_of_commute` — such a `U` is one on which `A` acts by translations.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| Γ discrete (l.1723) | ⚠ weakened: not used in this step |
| `Γ_nd`, unipotent subspace (l.1729–1733, bthm:unip) | ⚠ replaced: `A` commutative (from `Flat/BieberbachAbelian`), the common minimal set instead of the unipotent subspace |
| `E = ℝⁿ` | ⚠ weakened: any finite-dimensional real inner product space |

## SCOPE (disclosed)
* Step (2a) only; effectiveness is `Flat/BieberbachEffective`, the assembly `Flat/BieberbachProof`.
* The `U` produced is not claimed maximal (`Flat/Bieberbach`'s `BieberbachMaxConclusion` gives
  maximality from any `BieberbachConclusion`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-110.
-/

namespace Causal.Flat

open Set Function Module

section MinSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The minimal set** of a Euclidean isometry `g`: the points `x` whose displacement `g x − x`
is fixed by the linear part `L(g)`. -/
def minSet (g : E ≃ᵃⁱ[ℝ] E) : AffineSubspace ℝ E where
  carrier := {x | g.linearIsometryEquiv (g x -ᵥ x) = g x -ᵥ x}
  smul_vsub_vadd_mem := by
    intro c p1 p2 p3 h1 h2 h3
    simp only [Set.mem_setOf_eq] at h1 h2 h3 ⊢
    have key : g (c • (p1 -ᵥ p2) +ᵥ p3) -ᵥ (c • (p1 -ᵥ p2) +ᵥ p3) =
        c • ((g p1 -ᵥ p1) - (g p2 -ᵥ p2)) + (g p3 -ᵥ p3) := by
      rw [AffineIsometryEquiv.map_vadd, map_smul, AffineIsometryEquiv.map_vsub]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
      abel
    rw [key, map_add, map_smul, map_sub, h1, h2, h3]

theorem mem_minSet {g : E ≃ᵃⁱ[ℝ] E} {x : E} :
    x ∈ minSet g ↔ g.linearIsometryEquiv (g x -ᵥ x) = g x -ᵥ x := Iff.rfl

/-- **A fixed vector in the range of `A − 1` is zero** (`A` an isometry): if `A v = v` and
`v = A u − u`, then `⟪v, v⟫ = ⟪A u, A v⟫ − ⟪u, v⟫ = 0`. -/
theorem eq_zero_of_map_eq_of_eq_map_sub (A : E ≃ₗᵢ[ℝ] E) {u v : E} (hv : A v = v)
    (hu : v = A u - u) : v = 0 := by
  have h : inner ℝ v v = 0 := by
    calc inner ℝ v v = inner ℝ (A u - u) v := by rw [← hu]
      _ = inner ℝ (A u) v - inner ℝ u v := inner_sub_left _ _ _
      _ = inner ℝ (A u) (A v) - inner ℝ u v := by rw [hv]
      _ = 0 := by rw [LinearIsometryEquiv.inner_map_map, sub_self]
  exact inner_self_eq_zero.1 h

/-- **Fitting decomposition for an isometry on an invariant subspace**: on an `A`-invariant
`D`, every `w ∈ D` is `w₀ + (A u − u)` with `u ∈ D` and `A w₀ = w₀`
(`ker (A − 1)|_D ⊕ range (A − 1)|_D = D`, by rank–nullity and
`eq_zero_of_map_eq_of_eq_map_sub`). -/
theorem exists_sub_map_sub_fixed [FiniteDimensional ℝ E] (A : E ≃ₗᵢ[ℝ] E)
    {D : Submodule ℝ E} (hD : ∀ v ∈ D, A v ∈ D) {w : E} (hw : w ∈ D) :
    ∃ u ∈ D, A (w - (A u - u)) = w - (A u - u) := by
  let f : E →ₗ[ℝ] E := A.toLinearEquiv.toLinearMap - LinearMap.id
  have hf : ∀ v ∈ D, f v ∈ D := fun v hv => D.sub_mem (hD v hv) hv
  let T : D →ₗ[ℝ] D := f.restrict hf
  have hTv : ∀ v : D, ((T v : D) : E) = A v - v := fun v => rfl
  have hdisj : LinearMap.ker T ⊓ LinearMap.range T = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    obtain ⟨hk, ⟨u, rfl⟩⟩ := hv
    have hk' : A (T u : E) - (T u : E) = 0 := by
      rw [← hTv]; exact congrArg Subtype.val (LinearMap.mem_ker.1 hk)
    exact Subtype.ext (eq_zero_of_map_eq_of_eq_map_sub A (sub_eq_zero.1 hk') (hTv u))
  have hsup : LinearMap.ker T ⊔ LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker T) (LinearMap.range T)
    have h2 := LinearMap.finrank_range_add_finrank_ker T
    rw [hdisj, finrank_bot] at h1
    omega
  have hmem : (⟨w, hw⟩ : D) ∈ LinearMap.ker T ⊔ LinearMap.range T := hsup ▸ Submodule.mem_top
  obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hmem
  refine ⟨u, u.2, ?_⟩
  have hw' : w - (A u - u) = (y : E) := by
    have hwyz : w = (y : E) + (T u : E) := (congrArg Subtype.val hyz).symm
    rw [← hTv, hwyz, add_sub_cancel_right]
  have hy' : A (y : E) - (y : E) = 0 := by
    rw [← hTv]; exact congrArg Subtype.val (LinearMap.mem_ker.1 hy)
  rw [hw']
  exact sub_eq_zero.1 hy'

/-- **`g` translates its minimal set**: all points of `minSet g` are moved by the same vector. -/
theorem vsub_eq_of_mem_minSet {g : E ≃ᵃⁱ[ℝ] E} {x y : E} (hx : x ∈ minSet g)
    (hy : y ∈ minSet g) : g x -ᵥ x = g y -ᵥ y := by
  have hd : g.linearIsometryEquiv ((g x -ᵥ x) - (g y -ᵥ y)) = (g x -ᵥ x) - (g y -ᵥ y) := by
    rw [map_sub, (mem_minSet).1 hx, (mem_minSet).1 hy]
  have hu : (g x -ᵥ x) - (g y -ᵥ y) = g.linearIsometryEquiv (x - y) - (x - y) := by
    rw [← vsub_eq_sub x y, AffineIsometryEquiv.map_vsub]
    simp only [vsub_eq_sub]
    abel
  exact sub_eq_zero.1 (eq_zero_of_map_eq_of_eq_map_sub g.linearIsometryEquiv hd hu)

/-- **A commuting isometry preserves the minimal set.** -/
theorem apply_mem_minSet_of_commute {g h : E ≃ᵃⁱ[ℝ] E} (hgh : Commute g h) {x : E}
    (hx : x ∈ minSet g) : h x ∈ minSet g := by
  have hc : g (h x) = h (g x) := congrFun (congrArg (⇑) hgh.eq) x
  have hL : ∀ w : E, g.linearIsometryEquiv (h.linearIsometryEquiv w) =
      h.linearIsometryEquiv (g.linearIsometryEquiv w) := fun w =>
    congrArg (fun k : E ≃ᵃⁱ[ℝ] E => k.linearIsometryEquiv w) hgh.eq
  have hdisp : g (h x) -ᵥ h x = h.linearIsometryEquiv (g x -ᵥ x) := by
    rw [hc, AffineIsometryEquiv.map_vsub]
  rw [mem_minSet, hdisp, hL, (mem_minSet).1 hx]

/-- **A nonempty invariant affine subspace meets the minimal set.** -/
theorem exists_mem_minSet_of_invariant [FiniteDimensional ℝ E] (g : E ≃ᵃⁱ[ℝ] E)
    {S : AffineSubspace ℝ E} (hS : (S : Set E).Nonempty) (hinv : ∀ x ∈ S, g x ∈ S) :
    ∃ x ∈ S, x ∈ minSet g := by
  obtain ⟨x₀, hx₀⟩ := hS
  have hD : ∀ v ∈ S.direction, g.linearIsometryEquiv v ∈ S.direction := by
    intro v hv
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := (AffineSubspace.mem_direction_iff_eq_vsub ⟨x₀, hx₀⟩ v).1 hv
    rw [AffineIsometryEquiv.map_vsub]
    exact AffineSubspace.vsub_mem_direction (hinv p₁ hp₁) (hinv p₂ hp₂)
  obtain ⟨u, hu, hfix⟩ := exists_sub_map_sub_fixed g.linearIsometryEquiv hD
    (AffineSubspace.vsub_mem_direction (hinv x₀ hx₀) hx₀)
  refine ⟨(-u) +ᵥ x₀, AffineSubspace.vadd_mem_of_mem_direction (S.direction.neg_mem hu) hx₀, ?_⟩
  have hdisp : g ((-u) +ᵥ x₀) -ᵥ ((-u) +ᵥ x₀) =
      (g x₀ -ᵥ x₀) - (g.linearIsometryEquiv u - u) := by
    rw [AffineIsometryEquiv.map_vadd, map_neg]
    simp only [vsub_eq_sub, vadd_eq_add]
    abel
  rw [mem_minSet, hdisp, hfix]

/-- **A commutative group has a nonempty invariant affine subspace inside all minimal sets.** -/
theorem exists_subset_minSet_of_commute [FiniteDimensional ℝ E] {A : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h) :
    ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ (∀ γ ∈ A, ∀ x ∈ U, γ x ∈ U) ∧
      ∀ γ ∈ A, ∀ x ∈ U, x ∈ minSet γ := by
  classical
  let P : ℕ → Prop := fun n => ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧
    (∀ γ ∈ A, ∀ x ∈ U, γ x ∈ U) ∧ finrank ℝ U.direction = n
  have hP : ∃ n, P n := ⟨_, ⊤, ⟨0, AffineSubspace.mem_top ℝ E 0⟩,
    fun _ _ _ _ => AffineSubspace.mem_top ℝ E _, rfl⟩
  obtain ⟨U, hUne, hUinv, hUn⟩ := Nat.find_spec hP
  refine ⟨U, hUne, hUinv, fun γ hγ x hx => ?_⟩
  obtain ⟨y, hyU, hyM⟩ := exists_mem_minSet_of_invariant γ hUne (hUinv γ hγ)
  set V := U ⊓ minSet γ with hV
  have hVne : (V : Set E).Nonempty := ⟨y, (AffineSubspace.mem_inf_iff _ _ _).2 ⟨hyU, hyM⟩⟩
  have hVinv : ∀ δ ∈ A, ∀ z ∈ V, δ z ∈ V := by
    intro δ hδ z hz
    obtain ⟨hzU, hzM⟩ := (AffineSubspace.mem_inf_iff _ _ _).1 hz
    exact (AffineSubspace.mem_inf_iff _ _ _).2
      ⟨hUinv δ hδ z hzU, apply_mem_minSet_of_commute (hA γ hγ δ hδ) hzM⟩
  have hle : V.direction ≤ U.direction := AffineSubspace.direction_le inf_le_left
  have hmin : Nat.find hP ≤ finrank ℝ V.direction := Nat.find_min' hP ⟨V, hVne, hVinv, rfl⟩
  have hdir : V.direction = U.direction :=
    Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) (hUn ▸ hmin))
  have hVU : V = U := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir hVne inf_le_left
  have hxV : x ∈ V := hVU ▸ hx
  exact ((AffineSubspace.mem_inf_iff _ _ _).1 hxV).2

/-- **Step (2a)**: a commutative group of isometries of a finite-dimensional Euclidean space acts
by translations on some nonempty affine subspace. -/
theorem exists_actsByTranslationsOn_of_commute [FiniteDimensional ℝ E]
    {A : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h) :
    ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ ActsByTranslationsOn A U := by
  obtain ⟨U, ⟨x₀, hx₀⟩, hUinv, hUmin⟩ := exists_subset_minSet_of_commute hA
  refine ⟨U, ⟨x₀, hx₀⟩, fun γ hγ => ⟨γ x₀ -ᵥ x₀,
    AffineSubspace.vsub_mem_direction (hUinv γ hγ x₀ hx₀) hx₀, fun x hx => ?_⟩⟩
  rw [vsub_eq_of_mem_minSet (hUmin γ hγ x₀ hx₀) (hUmin γ hγ x hx), vsub_vadd]

end MinSet

end Causal.Flat
