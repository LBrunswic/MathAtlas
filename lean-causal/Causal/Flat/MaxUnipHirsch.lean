import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `Causal.Flat.MaxUnipHirsch` — `H¹(G; W) = 0` for nilpotent `G` and `W^G = 0` (Hirsch)

Step module of Prop 5.2 (`bthm:unip`, DEC-121, route P1 of `docs/CARRIERE-DALBO-SURVEY.md`
§2.1). **No label is marked**: this is the one piece of content of the Fried–Goldman–Hirsch
Fitting-submodule proof, stated for an arbitrary group and field, with bare cocycle predicates
(no `groupCohomology`). Consumer: `Flat/MaxUnipProof` (glue, master), through
`exists_coboundary_of_isNilpotent`, instantiated at `G = ↥N`, `W = 𝐌ⁿ ⧸ V₁`
(`Flat/MaxUnipCocycle`).

* `H1Vanishes ρ` — if `W^G = 0` then every 1-cocycle `u (g h) = u g + ρ g (u h)` is a coboundary
  `u g = ρ g w − w`; `HirschH1 K G` — that for every finite-dimensional `W` (universe `v`).
* `hirschQuotRep`, `hirschSubRep` — the representations on `W ⧸ W'` (`mapQ`) and on `W'`
  (`restrict`) for a `G`-invariant `W'`.
* `h1Vanishes_of_central_ne_one` — a central `z` with `ρ z ≠ 1` reduces to smaller dimension.
* `h1Vanishes_of_center_trivial` — if the centre acts trivially, reduce to `G ⧸ center G`.
* `hirschH1` — nilpotent `G`: `HirschH1 K G`; `exists_coboundary_of_isNilpotent`, unbundled.

> Lemma 1.1 (Hirsch [1977]). Let $G$ be a nilpotent group and $E$ a $G$-module such that
> $H^0(G;E) = 0$. Then $H^i(G;E) = 0$ for all $i$. (Fried–Goldman–Hirsch 1981, §1; read for the
> survey, only $i = 1$ is used here)

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (`GHFspace.tex` l.1712–1717, the statement this serves)

**Proof plan (survey §2.1 P1, simplified: no Fitting decomposition is needed).** Outer
induction `Group.nilpotent_center_quotient_ind` (motive `HirschH1 K`), inner strong induction on
`finrank K W`. Key identity, for `z` central: `u (z g) = u (g z)` gives
`ρ z (u g) − u g = ρ g (u z) − u z`.
* Some central `z` with `ρ z ≠ 1`; `W' := ker (ρ z − 1)`, `G`-invariant (`z` central).
  `W' = ⊥`: `ρ z − 1` is bijective, `u = δ((ρ z − 1)⁻¹ (u z))` by the identity.
  `W' ≠ ⊥`: `W' ≠ ⊤`, and `(W ⧸ W')^G = 0` — if `(ρ g − 1) w ∈ W'` for all `g` then
  `(ρ g − 1)(ρ z − 1) w = 0`, so `(ρ z − 1) w ∈ W^G = 0`. Inner IH on `W ⧸ W'`, lift `w`; then
  `u − δw` is a cocycle in `W'`, `W'^G = 0`, inner IH again.
* The centre acts trivially: the identity gives `u z ∈ W^G = 0`, so `u (z g) = u g`; `u`, `ρ`
  factor through `G ⧸ center G` (`QuotientGroup.lift`), whose invariants are `W^G = 0`; outer IH.
* **Pitfall (survey §4.4)**: never use the generalized eigenspaces of a non-central element —
  for non-connected nilpotent groups they are not `G`-invariant (`D₈` on `ℝ²`, `Q₈`).
* No finite generation of `G` is used anywhere (the centre may be infinite).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| FGH 1.1: `G` nilpotent, `H⁰(G; E) = 0` | ✓ carried; `E` finite-dimensional over a field (⚠ strengthened: FGH allow any module; the consumer is finite-dimensional) |
| FGH 1.1: all `i` | only `i = 1` (SCOPE) |

## SCOPE (disclosed)
* Only `H¹`; only finite-dimensional modules over a field.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-121.
-/

namespace Causal.Flat

open Module

universe u v w

section Hirsch

variable {K : Type u} [Field K]

/-- **`H¹(G; W) = 0` when `W^G = 0`**, for one representation, with bare cocycle predicates. -/
def H1Vanishes {G : Type w} [Group G] {W : Type v} [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) : Prop :=
  (∀ x : W, (∀ g, ρ g x = x) → x = 0) →
    ∀ c : G → W, (∀ g h, c (g * h) = c g + ρ g (c h)) → ∃ x : W, ∀ g, c g = ρ g x - x

variable (K) in
/-- `H1Vanishes` for every finite-dimensional `K`-representation of `G` in universe `v`. -/
def HirschH1 (G : Type w) [Group G] : Prop :=
  ∀ (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G W), H1Vanishes ρ

variable {G : Type w} [Group G] {W : Type v} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- **The trivial group.** -/
theorem hirschH1_of_subsingleton [Subsingleton G] : HirschH1.{u, v} K G := by
  intro W _ _ _ ρ _ c hc
  have h1 : c 1 = 0 := by
    have h := hc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    simpa using h
  exact ⟨0, fun g => by rw [Subsingleton.elim g 1, h1]; simp⟩

omit [FiniteDimensional K W] in
/-- The representation of `G` on `W ⧸ W'` induced by `ρ`, for a `G`-invariant `W'`. -/
def hirschQuotRep (ρ : Representation K G W) (W' : Submodule K W)
    (hW' : ∀ g, W' ≤ W'.comap (ρ g)) : Representation K G (W ⧸ W') where
  toFun g := W'.mapQ W' (ρ g) (hW' g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

omit [FiniteDimensional K W] in
/-- The representation of `G` on a `G`-invariant `W'` obtained by restricting `ρ`. -/
def hirschSubRep (ρ : Representation K G W) (W' : Submodule K W)
    (hW' : ∀ g, W' ≤ W'.comap (ρ g)) : Representation K G W' where
  toFun g := (ρ g).restrict (hW' g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

/-- **Dimension reduction by a central element acting nontrivially.** -/
theorem h1Vanishes_of_central_ne_one (ρ : Representation K G W) {z : G}
    (hz : z ∈ Subgroup.center G) (hρz : ρ z ≠ 1)
    (ih : ∀ (W' : Type v) [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
      (ρ' : Representation K G W'), finrank K W' < finrank K W → H1Vanishes ρ') :
    H1Vanishes ρ := by
  intro h0 c hc
  set T : Module.End K W := ρ z - 1 with hT
  have hTapply : ∀ w, T w = ρ z w - w := fun w => rfl
  have hcomm : ∀ g w, T (ρ g w) = ρ g (T w) := by
    intro g w
    have hgz : ρ z (ρ g w) = ρ g (ρ z w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.mp hz g, map_mul,
        Module.End.mul_apply]
    rw [hTapply, hTapply, map_sub, hgz]
  -- the key identity
  have hkey : ∀ g, T (c g) = ρ g (c z) - c z := by
    intro g
    have h1 := hc g z
    have h2 := hc z g
    rw [Subgroup.mem_center_iff.mp hz g, h2] at h1
    rw [hTapply]
    -- h1 : c z + ρ z (c g) = c g + ρ g (c z)
    have := congrArg (fun t => t - c z - c g) h1
    rw [show ρ z (c g) - c g = c z + ρ z (c g) - c z - c g by abel, this]
    abel
  set W' : Submodule K W := LinearMap.ker T with hW'
  have hW'inv : ∀ g, W' ≤ W'.comap (ρ g) := by
    intro g w hw
    simp only [Submodule.mem_comap, hW', LinearMap.mem_ker] at hw ⊢
    rw [hcomm, hw, map_zero]
  by_cases hbot : W' = ⊥
  · have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) (c z)
    refine ⟨x, fun g => hinj ?_⟩
    rw [hkey, map_sub, hcomm, hx]
  · have htop : W' ≠ ⊤ := by
      intro h
      apply hρz
      have : T = 0 := LinearMap.ker_eq_top.mp h
      rw [hT, sub_eq_zero] at this
      exact this
    -- the quotient step
    set ρQ := hirschQuotRep ρ W' hW'inv
    have hρQ : ∀ g w, ρQ g (Submodule.Quotient.mk w) = Submodule.Quotient.mk (ρ g w) :=
      fun g w => rfl
    have h0Q : ∀ q : W ⧸ W', (∀ g, ρQ g q = q) → q = 0 := by
      intro q hq
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective W' q
      have hTw : T w = 0 := by
        refine h0 _ fun g => ?_
        have := hq g
        rw [hρQ, Submodule.Quotient.eq, hW', LinearMap.mem_ker, map_sub, hcomm] at this
        exact sub_eq_zero.mp this
      exact (Submodule.Quotient.mk_eq_zero W').mpr hTw
    have hdimQ : finrank K (W ⧸ W') < finrank K W := by
      have h1 := Submodule.finrank_quotient_add_finrank W'
      have h2 : finrank K W' ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.mp h)
      omega
    obtain ⟨xq, hxq⟩ := ih (W ⧸ W') ρQ hdimQ h0Q (fun g => Submodule.Quotient.mk (c g))
      (fun g h => by rw [hc, Submodule.Quotient.mk_add, hρQ])
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W' xq
    -- the subspace step
    set d : G → W := fun g => c g - (ρ g x - x) with hd
    have hdmem : ∀ g, d g ∈ W' := by
      intro g
      have := hxq g
      rw [hρQ, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at this
      exact this
    set ρS := hirschSubRep ρ W' hW'inv
    have hρS : ∀ g (y : W'), ((ρS g y : W') : W) = ρ g y := fun g y => rfl
    have h0S : ∀ y : W', (∀ g, ρS g y = y) → y = 0 := by
      intro y hy
      have := h0 (y : W) fun g => by rw [← hρS, hy g]
      exact Subtype.ext this
    have hdimS : finrank K W' < finrank K W := Submodule.finrank_lt htop
    obtain ⟨y, hy⟩ := ih W' ρS hdimS h0S (fun g => ⟨d g, hdmem g⟩) (fun g h => by
      apply Subtype.ext
      simp only [Submodule.coe_add, hρS, hd, hc, map_mul, Module.End.mul_apply, map_sub]
      abel)
    refine ⟨x + y, fun g => ?_⟩
    have := congrArg Subtype.val (hy g)
    simp only [Submodule.coe_sub, hρS, hd] at this
    rw [map_add]
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    abel

/-- **Reduction to `G ⧸ center G`** when the centre acts trivially. -/
theorem h1Vanishes_of_center_trivial (ρ : Representation K G W)
    (hZ : ∀ z ∈ Subgroup.center G, ρ z = 1)
    (hq : HirschH1.{u, v} K (G ⧸ Subgroup.center G)) : H1Vanishes ρ := by
  intro h0 c hc
  have hcz : ∀ z ∈ Subgroup.center G, c z = 0 := by
    intro z hz
    refine h0 _ fun g => ?_
    have h1 := hc g z
    have h2 := hc z g
    rw [Subgroup.mem_center_iff.mp hz g, hZ z hz, Module.End.one_apply] at *
    rw [h2] at h1
    have := h1.symm
    rw [add_comm] at this
    exact add_right_cancel this
  have hcmul : ∀ g, ∀ z ∈ Subgroup.center G, c (g * z) = c g := by
    intro g z hz
    rw [hc, hcz z hz, map_zero, add_zero]
  let ρq : Representation K (G ⧸ Subgroup.center G) W :=
    QuotientGroup.lift (Subgroup.center G) ρ fun z hz => (MonoidHom.mem_ker).mpr (hZ z hz)
  have hρq : ∀ g : G, ρq (g : G ⧸ Subgroup.center G) = ρ g := fun g =>
    QuotientGroup.lift_mk _ _ g
  let cq : G ⧸ Subgroup.center G → W := fun q => c q.out
  have hcq : ∀ g : G, cq (g : G ⧸ Subgroup.center G) = c g := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center G) g
    simp only [cq, hz]
    exact hcmul g z z.2
  have h0q : ∀ x : W, (∀ q, ρq q x = x) → x = 0 := fun x hx =>
    h0 x fun g => by rw [← hρq]; exact hx _
  have hcocq : ∀ p q, cq (p * q) = cq p + ρq p (cq q) := by
    intro p q
    induction p using QuotientGroup.induction_on with
    | H g =>
      induction q using QuotientGroup.induction_on with
      | H h => rw [← QuotientGroup.mk_mul, hcq, hcq, hcq, hρq, hc]
  obtain ⟨x, hx⟩ := hq W ρq h0q cq hcocq
  exact ⟨x, fun g => by rw [← hcq, hx, hρq]⟩

/-- **Hirsch's lemma, degree 1** (FGH Lemma 1.1, `i = 1`): for nilpotent `G`, `H¹(G; W) = 0`
whenever `W^G = 0`. -/
theorem hirschH1 (G : Type w) [Group G] [Group.IsNilpotent G] : HirschH1.{u, v} K G := by
  refine Group.nilpotent_center_quotient_ind (P := fun G _ _ => HirschH1.{u, v} K G) G
    (fun G _ _ => hirschH1_of_subsingleton) (fun G _ _ hq => ?_)
  suffices H : ∀ n, ∀ (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ρ : Representation K G W), finrank K W = n → H1Vanishes ρ from
    fun W _ _ _ ρ => H _ W ρ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ ρ hn
    by_cases h : ∃ z ∈ Subgroup.center G, ρ z ≠ 1
    · obtain ⟨z, hz, hρz⟩ := h
      exact h1Vanishes_of_central_ne_one ρ hz hρz fun W' _ _ _ ρ' hlt => ih _ (hn ▸ hlt) W' ρ' rfl
    · simp only [not_exists, not_and, not_not] at h
      exact h1Vanishes_of_center_trivial ρ h hq

/-- **Hirsch's lemma, unbundled** — the form the glue instantiates. -/
theorem exists_coboundary_of_isNilpotent [Group.IsNilpotent G] (ρ : Representation K G W)
    (h0 : ∀ x : W, (∀ g, ρ g x = x) → x = 0) (c : G → W)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) : ∃ x : W, ∀ g, c g = ρ g x - x :=
  hirschH1.{u, v} G W ρ h0 c hc

end Hirsch

end Causal.Flat
