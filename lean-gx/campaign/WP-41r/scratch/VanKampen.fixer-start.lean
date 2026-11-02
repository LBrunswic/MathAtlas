import GX.Branched.Paths
import Mathlib.GroupTheory.PushoutI

/-!
# A topological Seifert–van Kampen theorem: gluing and injectivity

Package WP-41r (wave 4d, DEC-85). mathlib has no van Kampen theorem; this file builds the two
consequences Antoine's lemma needs (`GXScaffold.Branched.GaloisExamples`), in full generality and
sorry-free.

* `GX.VanKampen.exists_extension` — **the gluing half of SvK**: for an open cover `U ∪ V` of a
  space, with *tethers* (paths from the base point `x₀` to every point, inside `U`, `V`, `U ∩ V`
  according to where the point lies), two homotopy-invariant multiplicative invariants of loops
  of `U` and of `V` that agree on loops of `U ∩ V` extend to one homotopy-invariant invariant of
  loops of `U ∪ V`. Proof: the classical subdivision argument — fine subdivisions of a path by
  the Lebesgue number lemma, the product of the invariants of the tethered pieces, independence
  of the subdivision by common refinement, and homotopy invariance by a grid on the square.
* `GX.VanKampen.homotopicIn_of_homotopicIn_union` — **the injectivity consequence**: for `U`, `V`
  open and path-connected with `U ∩ V` path-connected, if loops of `U ∩ V` null-homotopic in `U`
  (resp. in `V`) are null-homotopic in `U ∩ V`, then a loop of `U` null-homotopic in `U ∪ V` is
  null-homotopic in `U`. Proof: the gluing half with values in the amalgamated product
  `π₁(U) *_{π₁(U ∩ V)} π₁(V)` (`Monoid.PushoutI`), and mathlib's injectivity of the factors of an
  amalgam along injective maps (`Monoid.PushoutI.of_injective`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace VanKampen

/-! ### Membership of composite paths -/

section Mem

variable {Y : Type*} [TopologicalSpace Y] {S : Set Y} {a b c : Y}

theorem mem_trans {p : Path a b} {q : Path b c} (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) :
    ∀ t, (p.trans q) t ∈ S := fun t => by
  rw [Path.trans_apply]; split_ifs
  · exact hp _
  · exact hq _

theorem mem_symm {p : Path a b} (hp : ∀ t, p t ∈ S) : ∀ t, p.symm t ∈ S := fun _ => hp _

theorem mem_refl (h : a ∈ S) : ∀ t, (Path.refl a) t ∈ S := fun _ => h

/-- Homotopy in `S` from an equality of classes in the subspace `S`. -/
theorem homotopicIn_of_mk_eq {p q : Path a b} (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (h : Path.Homotopic.Quotient.mk (pathToSub p hp) = .mk (pathToSub q hq)) :
    HomotopicIn S p q :=
  homotopicIn_iff.2 ⟨hp, hq, Path.Homotopic.Quotient.eq.1 h⟩

theorem pathToSub_refl (h : ∀ t, (Path.refl a) t ∈ S) :
    pathToSub (Path.refl a) h = Path.refl (⟨a, h 0⟩ : S) := by
  ext t; rfl

/-- Homotopy in `S` from a homotopy in the subspace `S` of paths with the same values. -/
theorem homotopicIn_of_sub {p q : Path a b} (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    {p' q' : Path (⟨a, p.source ▸ hp 0⟩ : S) (⟨b, p.target ▸ hp 1⟩ : S)} (hp' : ∀ t, (p' t : Y) = p t)
    (hq' : ∀ t, (q' t : Y) = q t) (h : p'.Homotopic q') : HomotopicIn S p q := by
  have e1 : p' = pathToSub p hp := by ext t; exact hp' t
  have e2 : q' = pathToSub q hq := by ext t; exact hq' t
  exact homotopicIn_iff.2 ⟨hp, hq, e1 ▸ e2 ▸ h⟩

end Mem

/-! ### The data of the gluing argument -/

/-- The data of the gluing half of Seifert–van Kampen: an open cover `S true ∪ S false` of `Y`,
tethers `τ y : x₀ ⇝ y` inside every `S b` containing `y` (`τ x₀` constant), and invariants
`f b` of the loops of `S b` at `x₀`, homotopy-invariant in `S b`, multiplicative, agreeing on the
loops of `S true ∩ S false`. -/
structure Data (Y : Type*) [TopologicalSpace Y] (G : Type*) [Group G] where
  S : Bool → Set Y
  isOpen : ∀ b, IsOpen (S b)
  cover : ∀ y, ∃ b, y ∈ S b
  x₀ : Y
  τ : ∀ y : Y, Path x₀ y
  τ_mem : ∀ b y, y ∈ S b → ∀ t, τ y t ∈ S b
  τ_x₀ : τ x₀ = Path.refl x₀
  f : Bool → Path x₀ x₀ → G
  f_hom : ∀ b γ γ', HomotopicIn (S b) γ γ' → f b γ = f b γ'
  f_trans : ∀ b γ γ', (∀ t, γ t ∈ S b) → (∀ t, γ' t ∈ S b) → f b (γ.trans γ') = f b γ * f b γ'
  agree : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ S true) → (∀ t, γ t ∈ S false) → f true γ = f false γ

namespace Data

variable {Y : Type*} [TopologicalSpace Y] {G : Type*} [Group G] (D : Data Y G)

theorem x₀_mem {b : Bool} {y : Y} (hy : y ∈ D.S b) : D.x₀ ∈ D.S b := by
  have := D.τ_mem b y hy 0
  rwa [Path.source] at this

theorem f_refl {b : Bool} (h : D.x₀ ∈ D.S b) : D.f b (Path.refl D.x₀) = 1 := by
  have h1 := D.f_trans b _ _ (mem_refl h) (mem_refl h)
  have h2 : HomotopicIn (D.S b) ((Path.refl D.x₀).trans (Path.refl D.x₀)) (Path.refl D.x₀) := by
    refine homotopicIn_of_sub (mem_trans (mem_refl h) (mem_refl h)) (mem_refl h)
      (p' := (Path.refl (⟨D.x₀, h⟩ : D.S b)).trans (Path.refl (⟨D.x₀, h⟩ : D.S b)))
      (q' := Path.refl (⟨D.x₀, h⟩ : D.S b))
      (fun t => ?_) (fun t => rfl) ?_
    · simp only [Path.trans_apply]; split_ifs <;> rfl
    · rw [← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]
  rw [D.f_hom b _ _ h2] at h1
  exact left_eq_mul.1 h1

/-- The tethered loop `τ_y · β · τ_{y'}⁻¹`. -/
def loopOf {y y' : Y} (β : Path y y') : Path D.x₀ D.x₀ := ((D.τ y).trans β).trans (D.τ y').symm

theorem loopOf_mem {b : Bool} {y y' : Y} {β : Path y y'} (hβ : ∀ t, β t ∈ D.S b) :
    ∀ t, D.loopOf β t ∈ D.S b := by
  have hy : y ∈ D.S b := β.source ▸ hβ 0
  have hy' : y' ∈ D.S b := β.target ▸ hβ 1
  exact mem_trans (mem_trans (D.τ_mem b y hy) hβ) (mem_symm (D.τ_mem b y' hy'))

/-- The invariant of a path contained in one of the two open sets. -/
def ψ {y y' : Y} (β : Path y y') : G :=
  if ∀ t, β t ∈ D.S true then D.f true (D.loopOf β) else D.f false (D.loopOf β)

theorem ψ_eq {b : Bool} {y y' : Y} {β : Path y y'} (hβ : ∀ t, β t ∈ D.S b) :
    D.ψ β = D.f b (D.loopOf β) := by
  cases b
  · by_cases h : ∀ t, β t ∈ D.S true
    · rw [ψ, if_pos h]; exact D.agree _ (D.loopOf_mem h) (D.loopOf_mem hβ)
    · rw [ψ, if_neg h]
  · rw [ψ, if_pos hβ]

theorem ψ_cast {y₁ y₂ y₁' y₂' : Y} (β : Path y₁ y₂) (h₁ : y₁' = y₁) (h₂ : y₂' = y₂) :
    D.ψ (β.cast h₁ h₂) = D.ψ β := by
  subst h₁; subst h₂; rfl

/-- `ψ` depends only on the values of the path. -/
theorem ψ_congr {y₁ y₂ y₁' y₂' : Y} (β : Path y₁ y₂) (β' : Path y₁' y₂') (h : ∀ t, β t = β' t) :
    D.ψ β = D.ψ β' := by
  have e1 : y₁ = y₁' := by rw [← β.source, ← β'.source, h]
  have e2 : y₂ = y₂' := by rw [← β.target, ← β'.target, h]
  subst e1; subst e2
  have : β = β' := by ext t; exact h t
  rw [this]

theorem ψ_hom {b : Bool} {y y' : Y} {β β' : Path y y'} (h : HomotopicIn (D.S b) β β') :
    D.ψ β = D.ψ β' := by
  have hy : y ∈ D.S b := β.source ▸ h.mem_left 0
  have hy' : y' ∈ D.S b := β.target ▸ h.mem_left 1
  rw [D.ψ_eq h.mem_left, D.ψ_eq h.mem_right]
  exact D.f_hom b _ _ (((HomotopicIn.refl (D.τ_mem b y hy)).hcomp h).hcomp
    (HomotopicIn.refl (mem_symm (D.τ_mem b y' hy'))))

theorem ψ_trans {b : Bool} {y y' y'' : Y} {β : Path y y'} {β' : Path y' y''}
    (hβ : ∀ t, β t ∈ D.S b) (hβ' : ∀ t, β' t ∈ D.S b) :
    D.ψ (β.trans β') = D.ψ β * D.ψ β' := by
  have hy : y ∈ D.S b := β.source ▸ hβ 0
  have hy' : y' ∈ D.S b := β.target ▸ hβ 1
  have hy'' : y'' ∈ D.S b := β'.target ▸ hβ' 1
  have h1 := D.τ_mem b y hy
  have h2 := D.τ_mem b y' hy'
  have h3 := D.τ_mem b y'' hy''
  rw [D.ψ_eq (mem_trans hβ hβ'), D.ψ_eq hβ, D.ψ_eq hβ',
    ← D.f_trans b _ _ (D.loopOf_mem hβ) (D.loopOf_mem hβ')]
  refine D.f_hom b _ _ (homotopicIn_of_sub (D.loopOf_mem (mem_trans hβ hβ'))
    (mem_trans (D.loopOf_mem hβ) (D.loopOf_mem hβ'))
    (p' := ((pathToSub _ h1).trans ((pathToSub _ hβ).trans (pathToSub _ hβ'))).trans
      (pathToSub _ h3).symm)
    (q' := (((pathToSub _ h1).trans (pathToSub _ hβ)).trans (pathToSub _ h2).symm).trans
      (((pathToSub _ h2).trans (pathToSub _ hβ')).trans (pathToSub _ h3).symm))
    (fun t => ?_) (fun t => ?_) ?_)
  · simp only [loopOf, Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl
  · simp only [loopOf, Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl
  · rw [← Path.Homotopic.Quotient.eq]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm _),
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- `ψ` of a constant path is `1`. -/
theorem ψ_const {b : Bool} {y y' : Y} {β : Path y y'} (hβ : ∀ t, β t = y) (hy : y ∈ D.S b) :
    D.ψ β = 1 := by
  have hm : ∀ t, β t ∈ D.S b := fun t => (hβ t).symm ▸ hy
  have e : y = y' := by rw [← β.target, hβ]
  subst e
  have hβr : β = Path.refl y := by ext t; exact hβ t
  subst hβr
  have hx := D.x₀_mem hy
  have h1 := D.τ_mem b y hy
  rw [D.ψ_eq hm, ← D.f_refl hx]
  refine D.f_hom b _ _ (homotopicIn_of_sub (D.loopOf_mem hm) (mem_refl hx)
    (p' := ((pathToSub _ h1).trans (Path.refl (⟨y, hy⟩ : D.S b))).trans (pathToSub _ h1).symm)
    (q' := Path.refl (⟨D.x₀, hx⟩ : D.S b)) (fun t => ?_) (fun t => rfl) ?_)
  · simp only [loopOf, Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl
  · rw [← Path.Homotopic.Quotient.eq]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_symm]


/-! ### Subdivisions -/

/-- `j / N`, clamped to `[0,1]`. -/
def pt (N j : ℕ) : I := Set.projIcc 0 1 zero_le_one ((j : ℝ) / N)

theorem pt_val {N j : ℕ} (hj : j ≤ N) : (pt N j : ℝ) = (j : ℝ) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : j = 0 := by omega
    simp [pt]
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have : (j : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hN').2 (by exact_mod_cast hj)⟩
    rw [pt, Set.projIcc_of_mem _ this]

theorem pt_zero (N : ℕ) : pt N 0 = 0 := Subtype.ext (by simp [pt])

theorem pt_self {N : ℕ} (hN : 0 < N) : pt N N = 1 := by
  apply Subtype.ext
  rw [pt_val le_rfl]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [this]

/-- The `j`-th piece of the subdivision of `γ` into `N` pieces. -/
def seg {a b : Y} (γ : Path a b) (N j : ℕ) : Path (γ (pt N j)) (γ (pt N (j + 1))) :=
  subpath γ (pt N j) (pt N (j + 1))

theorem subpath_mem_of {a b : Y} (γ : Path a b) {u v : I} (huv : (u : ℝ) ≤ v) {T : Set Y}
    (h : ∀ r : ℝ, (u : ℝ) ≤ r → r ≤ v → γ.extend r ∈ T) : ∀ t, subpath γ u v t ∈ T := by
  intro t
  rw [subpath_apply']
  have := t.2.1
  have := t.2.2
  exact h _ (by nlinarith) (by nlinarith)

/-- The product of the invariants of the `N` pieces. -/
def prodN {a b : Y} (γ : Path a b) (N : ℕ) : G :=
  ((List.range N).map fun j => D.ψ (seg γ N j)).prod

/-- `N` pieces are fine for `γ`: each lies in one of the two open sets. -/
def Fine {a b : Y} (γ : Path a b) (N : ℕ) : Prop :=
  0 < N ∧ ∀ j < N, ∃ c, ∀ r : ℝ, (j : ℝ) / N ≤ r → r ≤ ((j : ℝ) + 1) / N → γ.extend r ∈ D.S c

theorem exists_fine {a b : Y} (γ : Path a b) : ∃ N₀, ∀ N ≥ N₀, D.Fine γ N := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set I)) isCompact_univ
    (c := fun b => γ ⁻¹' D.S b) (fun b => (D.isOpen b).preimage γ.continuous)
    (fun t _ => mem_iUnion.2 (D.cover (γ t)))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  have hN₀pos : (0 : ℝ) < N₀ := lt_trans (by positivity) hN₀
  refine ⟨N₀, fun N hN => ⟨by
    have : (0 : ℝ) < N := hN₀pos.trans_le (by exact_mod_cast hN)
    exact_mod_cast this, ?_⟩⟩
  intro j hj
  have hNr : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := hN₀pos.trans_le hNr
  obtain ⟨c, hc⟩ := hball (pt N j) trivial
  refine ⟨c, fun r h1 h2 => ?_⟩
  have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  have hr0 : 0 ≤ r := le_trans (by positivity) h1
  have hr1 : r ≤ 1 := h2.trans ((div_le_one hNpos).2 hj')
  rw [Path.extend_apply γ ⟨hr0, hr1⟩]
  apply hc
  rw [Metric.mem_ball, Subtype.dist_eq, pt_val hj.le, Real.dist_eq]
  have hlt : 1 / (N : ℝ) < δ := by
    calc 1 / (N : ℝ) ≤ 1 / N₀ := one_div_le_one_div_of_le hN₀pos hNr
      _ < δ := by rw [div_lt_iff₀ hN₀pos]; rw [div_lt_iff₀ hδ] at hN₀; linarith
  have : r - j / N ≤ 1 / N := by rw [add_div] at h2; linarith
  have : 0 ≤ r - j / N := by linarith
  rw [abs_of_nonneg this]; linarith

theorem Fine.mul {a b : Y} {γ : Path a b} {N M : ℕ} (h : D.Fine γ N) (hM : 0 < M) :
    D.Fine γ (N * M) := by
  refine ⟨Nat.mul_pos h.1 hM, fun j hj => ?_⟩
  have hk : j / M < N := (Nat.div_lt_iff_lt_mul hM).2 hj
  obtain ⟨c, hc⟩ := h.2 _ hk
  refine ⟨c, fun r h1 h2 => hc r ?_ ?_⟩
  · have e : j / M * M ≤ j := Nat.div_mul_le_self j M
    have hN : (0 : ℝ) < N := by exact_mod_cast h.1
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ hN (by exact_mod_cast Nat.mul_pos h.1 hM)]
    have : ((j / M : ℕ) : ℝ) * M ≤ j := by exact_mod_cast e
    push_cast; nlinarith
  · have e : j < (j / M + 1) * M := Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hM
    have hN : (0 : ℝ) < N := by exact_mod_cast h.1
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos h.1 hM) hN]
    have : (j : ℝ) + 1 ≤ ((j / M : ℕ) + 1) * M := by exact_mod_cast e
    push_cast; nlinarith

/-- The two halves of a piece contained in one open set. -/
theorem ψ_subpath_trans {a b : Y} (γ : Path a b) {u v w : I} (huv : (u : ℝ) ≤ v)
    (hvw : (v : ℝ) ≤ w) {c : Bool} (h : ∀ r : ℝ, (u : ℝ) ≤ r → r ≤ w → γ.extend r ∈ D.S c) :
    D.ψ (subpath γ u w) = D.ψ (subpath γ u v) * D.ψ (subpath γ v w) := by
  rw [← D.ψ_trans (subpath_mem_of γ huv fun r h1 h2 => h r h1 (h2.trans hvw))
    (subpath_mem_of γ hvw fun r h1 h2 => h r (huv.trans h1) h2)]
  refine D.ψ_hom (subpath_trans_homotopicIn γ u v w fun r h1 h2 => h r ?_ ?_)
  · rwa [min_eq_left huv, min_eq_left (huv.trans hvw)] at h1
  · rwa [max_eq_right huv, max_eq_right hvw] at h2

theorem ψ_subpath_self {a b : Y} (γ : Path a b) (u : I) : D.ψ (subpath γ u u) = 1 := by
  obtain ⟨c, hc⟩ := D.cover (γ u)
  refine D.ψ_const (fun t => ?_) hc
  rw [subpath_apply', show (1 - (t : ℝ)) * u + t * u = u by ring, Path.extend_extends']

theorem pt_mono {N j k : ℕ} (hjk : j ≤ k) (hk : k ≤ N) : (pt N j : ℝ) ≤ pt N k := by
  rw [pt_val (hjk.trans hk), pt_val hk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (Nat.cast_nonneg _)

theorem prod_block {a b : Y} (γ : Path a b) {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hk : k < N)
    {c : Bool} (h : ∀ r : ℝ, (k : ℝ) / N ≤ r → r ≤ ((k : ℝ) + 1) / N → γ.extend r ∈ D.S c) :
    ∀ n ≤ M, ((List.range n).map fun l => D.ψ (seg γ (N * M) (k * M + l))).prod =
      D.ψ (subpath γ (pt (N * M) (k * M)) (pt (N * M) (k * M + n))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkM : k * M + M ≤ N * M := by nlinarith
  intro n
  induction n with
  | zero => intro; simp [D.ψ_subpath_self]
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [show k * M + (n + 1) = k * M + n + 1 by omega]
    refine (D.ψ_subpath_trans γ (pt_mono (by omega) (by omega)) (pt_mono (by omega) (by omega))
      fun r h1 h2 => h r ?_ ?_).symm
    · rw [pt_val (by omega)] at h1
      refine le_trans (le_of_eq ?_) h1
      push_cast; field_simp
    · rw [pt_val (by omega)] at h2
      refine h2.trans ?_
      rw [div_le_div_iff₀ (by positivity) hNr]
      have : ((k * M + n + 1 : ℕ) : ℝ) ≤ k * M + M := by exact_mod_cast (by omega : k * M + n + 1 ≤ k * M + M)
      push_cast at this ⊢; nlinarith

theorem prodN_refine {a b : Y} {γ : Path a b} {N M : ℕ} (h : D.Fine γ N) (hM : 0 < M) :
    D.prodN γ (N * M) = D.prodN γ N := by
  have hN := h.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  suffices ∀ k ≤ N, ((List.range (k * M)).map fun j => D.ψ (seg γ (N * M) j)).prod =
      ((List.range k).map fun j => D.ψ (seg γ N j)).prod from this N le_rfl
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    rw [Nat.succ_mul, List.range_add, List.map_append, List.prod_append, ih (by omega),
      List.range_succ, List.map_append, List.prod_append, List.map_map]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    obtain ⟨c, hc⟩ := h.2 k (by omega)
    rw [show (fun j => D.ψ (seg γ (N * M) j)) ∘ (fun x => k * M + x) =
      fun l => D.ψ (seg γ (N * M) (k * M + l)) from rfl,
      D.prod_block γ hN hM (by omega) hc M le_rfl]
    have e1 : pt (N * M) (k * M) = pt N k := by
      apply Subtype.ext
      rw [pt_val (by nlinarith), pt_val (by omega)]
      push_cast; field_simp
    have e2 : pt (N * M) (k * M + M) = pt N (k + 1) := by
      apply Subtype.ext
      rw [pt_val (by nlinarith), pt_val (by omega)]
      push_cast; field_simp
    rw [e1, e2]; rfl

theorem prodN_eq {a b : Y} {γ : Path a b} {N N' : ℕ} (h : D.Fine γ N) (h' : D.Fine γ N') :
    D.prodN γ N = D.prodN γ N' := by
  rw [← D.prodN_refine h h'.1, ← D.prodN_refine h' h.1, Nat.mul_comm]

/-- The invariant of an arbitrary path (through any fine subdivision). -/
def Φ {a b : Y} (γ : Path a b) : G := D.prodN γ (Classical.choose (D.exists_fine γ))

theorem Φ_eq {a b : Y} {γ : Path a b} {N : ℕ} (h : D.Fine γ N) : D.Φ γ = D.prodN γ N :=
  D.prodN_eq (Classical.choose_spec (D.exists_fine γ) _ le_rfl) h


/-! ### Homotopy invariance: the grid on the square -/

section Grid

variable {F : ℝ × ℝ → Y} (hF : Continuous F)

/-- The grid edge in the path direction, at homotopy time `i/N`, from `j/N` to `(j+1)/N`. -/
def edgeT (N i j : ℕ) : Path (F ((i : ℝ) / N, (j : ℝ) / N)) (F ((i : ℝ) / N, ((j + 1 : ℕ) : ℝ) / N)) :=
  (Path.segment ((i : ℝ) / N, (j : ℝ) / N) ((i : ℝ) / N, ((j + 1 : ℕ) : ℝ) / N)).map hF

/-- The grid edge in the homotopy direction, at path time `j/N`, from `i/N` to `(i+1)/N`. -/
def edgeS (N i j : ℕ) : Path (F ((i : ℝ) / N, (j : ℝ) / N)) (F (((i + 1 : ℕ) : ℝ) / N, (j : ℝ) / N)) :=
  (Path.segment ((i : ℝ) / N, (j : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N, (j : ℝ) / N)).map hF

/-- The closed grid square `[i/N, (i+1)/N] × [j/N, (j+1)/N]`. -/
def box (N i j : ℕ) : Set (ℝ × ℝ) :=
  Icc ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) ×ˢ Icc ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N)

theorem convex_box (N i j : ℕ) : Convex ℝ (box N i j) := (convex_Icc _ _).prod (convex_Icc _ _)

theorem div_le_succ_div (N i : ℕ) : (i : ℝ) / N ≤ ((i + 1 : ℕ) : ℝ) / N :=
  div_le_div_of_nonneg_right (by push_cast; linarith) (Nat.cast_nonneg _)

theorem segment_mem_box {N i j : ℕ} {p q : ℝ × ℝ} (hp : p ∈ box N i j) (hq : q ∈ box N i j)
    (t : I) : Path.segment p q t ∈ box N i j := by
  rw [Path.segment_apply]; exact (convex_box N i j).lineMap_mem hp hq t.2

theorem corner_mem_box (N i j : ℕ) {u v : ℝ}
    (hu : u = (i : ℝ) / N ∨ u = ((i + 1 : ℕ) : ℝ) / N)
    (hv : v = (j : ℝ) / N ∨ v = ((j + 1 : ℕ) : ℝ) / N) : (u, v) ∈ box N i j := by
  have h1 := div_le_succ_div N i
  have h2 := div_le_succ_div N j
  refine ⟨?_, ?_⟩
  · rcases hu with rfl | rfl
    · exact ⟨le_rfl, h1⟩
    · exact ⟨h1, le_rfl⟩
  · rcases hv with rfl | rfl
    · exact ⟨le_rfl, h2⟩
    · exact ⟨h2, le_rfl⟩

/-- The square relation of the grid. -/
theorem ψ_square {N i j : ℕ} {c : Bool} (hbox : ∀ p ∈ box N i j, F p ∈ D.S c) :
    D.ψ (edgeT hF N i j) * D.ψ (edgeS hF N i (j + 1)) =
      D.ψ (edgeS hF N i j) * D.ψ (edgeT hF N (i + 1) j) := by
  have m : ∀ {p q : ℝ × ℝ}, p ∈ box N i j → q ∈ box N i j →
      ∀ t, ((Path.segment p q).map hF) t ∈ D.S c := fun hp hq t =>
    hbox _ (segment_mem_box hp hq t)
  have c00 := corner_mem_box N i j (Or.inl rfl) (Or.inl rfl)
  have c01 := corner_mem_box N i j (Or.inl rfl) (Or.inr rfl)
  have c10 := corner_mem_box N i j (Or.inr rfl) (Or.inl rfl)
  have c11 := corner_mem_box N i j (Or.inr rfl) (Or.inr rfl)
  simp only [edgeT, edgeS]
  rw [← D.ψ_trans (m c00 c01) (m c01 c11), ← D.ψ_trans (m c00 c10) (m c10 c11)]
  refine D.ψ_hom (b := c) ?_
  simp only [← Path.map_trans]
  refine homotopicIn_map_of_convex _ _ (convex_box N i j) (fun t => ?_) (fun t => ?_) hF hbox
  · rw [Path.trans_apply]; split_ifs
    · exact segment_mem_box c00 c01 _
    · exact segment_mem_box c01 c11 _
  · rw [Path.trans_apply]; split_ifs
    · exact segment_mem_box c00 c10 _
    · exact segment_mem_box c10 c11 _

/-- The product along the `i`-th row of the grid. -/
def rowProd (N i m : ℕ) : G := ((List.range m).map fun j => D.ψ (edgeT hF N i j)).prod

theorem rowProd_telescope {N i : ℕ} (hsq : ∀ j < N, ∃ c, ∀ p ∈ box N i j, F p ∈ D.S c) :
    ∀ m ≤ N, D.rowProd hF N i m * D.ψ (edgeS hF N i m) =
      D.ψ (edgeS hF N i 0) * D.rowProd hF N (i + 1) m := by
  intro m
  induction m with
  | zero => intro; simp [rowProd]
  | succ m ih =>
    intro hm
    obtain ⟨c, hc⟩ := hsq m (by omega)
    simp only [rowProd, List.range_succ, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    rw [mul_assoc, D.ψ_square hF hc, ← mul_assoc, ih (by omega), mul_assoc]

end Grid

theorem Φ_homotopic {a b : Y} {γ γ' : Path a b} (F : Path.Homotopy γ γ') : D.Φ γ = D.Φ γ' := by
  set F' : ℝ × ℝ → Y := squareExt F with hF'
  have hF : Continuous F' := continuous_squareExt F.continuous
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set (I × I)))
    isCompact_univ (c := fun c => F ⁻¹' D.S c) (fun c => (D.isOpen c).preimage F.continuous)
    (fun z _ => mem_iUnion.2 (D.cover (F z)))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNr : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNr
  have hlt : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNr]; rw [div_lt_iff₀ hδ] at hN; linarith
  -- every grid square lies in one open set
  have hsq : ∀ i < N, ∀ j < N, ∃ c, ∀ p ∈ box N i j, F' p ∈ D.S c := by
    intro i hi j hj
    obtain ⟨c, hc⟩ := hball (pt N i, pt N j) trivial
    refine ⟨c, fun p hp => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    have hi' : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hi
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
    have hp1 : p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) h1, h2.trans ((div_le_one hNr).2 hi')⟩
    have hp2 : p.2 ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) h3, h4.trans ((div_le_one hNr).2 hj')⟩
    show F (Set.projIcc 0 1 zero_le_one p.1, Set.projIcc 0 1 zero_le_one p.2) ∈ D.S c
    rw [Set.projIcc_of_mem _ hp1, Set.projIcc_of_mem _ hp2]
    apply hc
    rw [Metric.mem_ball, Prod.dist_eq, Subtype.dist_eq, Subtype.dist_eq, pt_val hi.le,
      pt_val hj.le, Real.dist_eq, Real.dist_eq]
    have e1 : p.1 - i / N ≤ 1 / N := by push_cast at h2; rw [add_div] at h2; linarith
    have e2 : p.2 - j / N ≤ 1 / N := by push_cast at h4; rw [add_div] at h4; linarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact max_lt (by linarith) (by linarith)
  -- the boundary columns are constant
  have hcol0 : ∀ i, D.ψ (edgeS hF N i 0) = 1 := fun i => by
    obtain ⟨c, hc⟩ := D.cover a
    refine D.ψ_const (fun t => ?_) (show F' ((i : ℝ) / N, ((0 : ℕ) : ℝ) / N) ∈ D.S c by
      simp only [hF', squareExt, Nat.cast_zero, zero_div, projIcc_zero']
      rw [F.source]; exact hc)
    simp only [edgeS, Path.map_coe, comp_apply, Path.segment_apply, AffineMap.lineMap_apply_module,
      hF', squareExt, Nat.cast_zero, zero_div, smul_eq_mul, mul_zero, add_zero, Prod.smul_mk,
      Prod.mk_add_mk, projIcc_zero']
    rw [F.source, F.source]
  have hcolN : ∀ i, D.ψ (edgeS hF N i N) = 1 := fun i => by
    obtain ⟨c, hc⟩ := D.cover b
    refine D.ψ_const (y := F' ((i : ℝ) / N, (N : ℝ) / N)) (fun t => ?_) (by
      show F (_, _) ∈ _
      rw [div_self hNr.ne', projIcc_one', F.target]; exact hc)
    simp only [edgeS, Path.map_coe, comp_apply, Path.segment_apply, AffineMap.lineMap_apply_module,
      hF', squareExt, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk, div_self hNr.ne']
    simp only [mul_one, sub_add_cancel, projIcc_one']
    rw [F.target, F.target]
  -- row by row
  have hrow : ∀ i < N, D.rowProd hF N i N = D.rowProd hF N (i + 1) N := fun i hi => by
    have := D.rowProd_telescope hF (hsq i hi) N le_rfl
    rwa [hcol0, hcolN, mul_one, one_mul] at this
  have hall : ∀ i ≤ N, D.rowProd hF N 0 N = D.rowProd hF N i N := by
    intro i
    induction i with
    | zero => intro; rfl
    | succ i ih => intro hi; rw [ih (by omega), hrow i (by omega)]
  -- the end rows are `γ` and `γ'`
  have hfine0 : D.Fine γ N := ⟨hN0, fun j hj => by
    obtain ⟨c, hc⟩ := hsq 0 hN0 j hj
    refine ⟨c, fun r h1 h2 => ?_⟩
    have hmem := hc (0, r) ⟨⟨by simp, by positivity⟩, h1, by push_cast; exact h2⟩
    simp only [hF', squareExt, projIcc_zero', F.apply_zero] at hmem
    exact hmem⟩
  have hfine1 : D.Fine γ' N := ⟨hN0, fun j hj => by
    obtain ⟨c, hc⟩ := hsq (N - 1) (by omega) j hj
    refine ⟨c, fun r h1 h2 => ?_⟩
    have e : (((N - 1 + 1 : ℕ) : ℝ)) / N = 1 := by
      rw [Nat.sub_add_cancel hN0, div_self hNr.ne']
    have hmem := hc (1, r) ⟨⟨by
      rw [div_le_one hNr]; exact_mod_cast Nat.sub_le N 1, e.ge⟩, h1, by push_cast; exact h2⟩
    simp only [hF', squareExt, projIcc_one', F.apply_one] at hmem
    exact hmem⟩
  have hγ : D.rowProd hF N 0 N = D.prodN γ N := by
    unfold rowProd prodN
    congr 1
    refine List.map_congr_left fun j hj => D.ψ_congr _ _ fun t => ?_
    have hj' : j < N := List.mem_range.1 hj
    simp only [edgeT, seg, Path.map_coe, comp_apply, Path.segment_apply,
      AffineMap.lineMap_apply_module, hF', squareExt, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk,
      Nat.cast_zero, zero_div, mul_zero, add_zero, projIcc_zero', F.apply_zero, subpath_apply']
    rw [pt_val hj'.le, pt_val hj']
    rfl
  have hγ' : D.rowProd hF N N N = D.prodN γ' N := by
    unfold rowProd prodN
    congr 1
    refine List.map_congr_left fun j hj => D.ψ_congr _ _ fun t => ?_
    have hj' : j < N := List.mem_range.1 hj
    simp only [edgeT, seg, Path.map_coe, comp_apply, Path.segment_apply,
      AffineMap.lineMap_apply_module, hF', squareExt, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk,
      div_self hNr.ne', subpath_apply']
    simp only [mul_one, sub_add_cancel, projIcc_one', F.apply_one]
    rw [pt_val hj'.le, pt_val hj']
    rfl
  rw [D.Φ_eq hfine0, D.Φ_eq hfine1, ← hγ, ← hγ', hall N le_rfl]


/-- On a loop contained in one open set, the invariant is the given one. -/
theorem Φ_of_mem {b : Bool} {γ : Path D.x₀ D.x₀} (hγ : ∀ t, γ t ∈ D.S b) : D.Φ γ = D.f b γ := by
  obtain ⟨N₀, hfine⟩ := D.exists_fine γ
  set N := max N₀ 1
  have hN : D.Fine γ N := hfine N (le_max_left _ _)
  have hN0 : 0 < N := hN.1
  have hext : ∀ r : ℝ, ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ r → r ≤ (((0 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ) →
      γ.extend r ∈ D.S b := fun r _ _ => by
    exact hγ (Set.projIcc 0 1 zero_le_one r)
  have hb := D.prod_block γ (N := 1) (M := N) (k := 0) one_pos hN0 one_pos hext N le_rfl
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_add] at hb
  rw [show (fun l => D.ψ (seg γ N (0 + l))) = fun l => D.ψ (seg γ N l) from
    funext fun l => by rw [Nat.zero_add]] at hb
  rw [D.Φ_eq hN, prodN, hb, pt_zero, pt_self hN0]
  have hx : D.x₀ ∈ D.S b := by have := hγ 0; rwa [Path.source] at this
  rw [D.ψ_congr _ γ fun t => by
    rw [subpath_apply', show (1 - (t : ℝ)) * ((0 : I) : ℝ) + t * ((1 : I) : ℝ) = t by simp,
      Path.extend_extends'], D.ψ_eq hγ]
  refine D.f_hom b _ _ (homotopicIn_of_sub (D.loopOf_mem hγ) hγ
    (p' := ((Path.refl (⟨D.x₀, hx⟩ : D.S b)).trans (pathToSub γ hγ)).trans
      (Path.refl (⟨D.x₀, hx⟩ : D.S b)).symm) (q' := pathToSub γ hγ) (fun t => ?_) (fun t => rfl) ?_)
  · simp only [loopOf, D.τ_x₀, Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl
  · rw [← Path.Homotopic.Quotient.eq]
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans, Path.refl_symm,
      Path.Homotopic.Quotient.trans_refl]

/-- **The gluing half of Seifert–van Kampen**: the invariants of the loops of the two open sets
extend to a homotopy-invariant invariant of all loops. -/
theorem exists_extension : ∃ Φ : Path D.x₀ D.x₀ → G, (∀ γ γ', γ.Homotopic γ' → Φ γ = Φ γ') ∧
    ∀ b γ, (∀ t, γ t ∈ D.S b) → Φ γ = D.f b γ :=
  ⟨D.Φ, fun _ _ ⟨F⟩ => D.Φ_homotopic F, fun _ _ h => D.Φ_of_mem h⟩

end Data



/-! ### The injectivity consequence -/

section Injectivity

variable {X : Type*} [TopologicalSpace X]

/-- A path of `X` with values in `S`, read in the subspace `S` (any proof of the end points). -/
def toSub {S : Set X} {x y : X} (γ : Path x y) (h : ∀ t, γ t ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    Path (⟨x, hx⟩ : S) ⟨y, hy⟩ where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

theorem homotopicIn_iff_toSub {S : Set X} {x y : X} {γ γ' : Path x y} (h : ∀ t, γ t ∈ S)
    (h' : ∀ t, γ' t ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    HomotopicIn S γ γ' ↔ (toSub γ h hx hy).Homotopic (toSub γ' h' hx hy) := by
  have e : ∀ {p : Path x y} (hp : ∀ t, p t ∈ S), toSub p hp hx hy = pathToSub p hp := fun _ => by
    ext; rfl
  rw [e h, e h', homotopicIn_iff]
  exact ⟨fun ⟨_, _, H⟩ => H, fun H => ⟨h, h', H⟩⟩

/-- **The injectivity consequence of Seifert–van Kampen.** `U`, `V` open and path-connected, `U ∩ V`
path-connected, `x₀ ∈ U ∩ V`; if loops of `U ∩ V` null-homotopic in `U` (resp. `V`) are
null-homotopic in `U ∩ V`, then a loop of `U` null-homotopic in `U ∪ V` is null-homotopic in
`U`. (`π₁(U) → π₁(U ∪ V)` is injective when `π₁(U ∩ V)` injects in both.) -/
theorem homotopicIn_of_homotopicIn_union {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPathConnected U) (hVc : IsPathConnected V) (hW : IsPathConnected (U ∩ V)) {x₀ : X}
    (hx₀ : x₀ ∈ U ∩ V)
    (hinjU : ∀ δ : Path x₀ x₀, (∀ t, δ t ∈ U ∩ V) → HomotopicIn U δ (Path.refl x₀) →
      HomotopicIn (U ∩ V) δ (Path.refl x₀))
    (hinjV : ∀ δ : Path x₀ x₀, (∀ t, δ t ∈ U ∩ V) → HomotopicIn V δ (Path.refl x₀) →
      HomotopicIn (U ∩ V) δ (Path.refl x₀))
    {γ : Path x₀ x₀} (hγ : ∀ t, γ t ∈ U) (h : HomotopicIn (U ∪ V) γ (Path.refl x₀)) :
    HomotopicIn U γ (Path.refl x₀) := by
  -- the amalgamated product `π₁(U) *_{π₁(U ∩ V)} π₁(V)`
  set S : Bool → Set X := fun b => cond b U V with hSdef
  have hS : ∀ b, x₀ ∈ S b := fun b => by cases b; exacts [hx₀.2, hx₀.1]
  have hWS : ∀ b, U ∩ V ⊆ S b := fun b => by cases b; exacts [inter_subset_right, inter_subset_left]
  have hSU : ∀ b, S b ⊆ U ∪ V := fun b => by cases b; exacts [subset_union_right, subset_union_left]
  let A : Bool → Type _ := fun b => FundamentalGroup (S b) ⟨x₀, hS b⟩
  let H := FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩
  let φ : ∀ b, H →* A b := fun b =>
    FundamentalGroup.map ⟨Set.inclusion (hWS b), continuous_inclusion (hWS b)⟩ ⟨x₀, hx₀⟩
  have hφ_mk : ∀ b (δ : Path x₀ x₀) (hδ : ∀ t, δ t ∈ U ∩ V),
      φ b (FundamentalGroup.fromPath (.mk (toSub δ hδ hx₀ hx₀))) =
        FundamentalGroup.fromPath (.mk (toSub δ (fun t => hWS b (hδ t)) (hS b) (hS b))) :=
    fun b δ hδ => by
      show (Path.Homotopic.Quotient.mk _).map _ = _
      rw [← Path.Homotopic.Quotient.mk_map]; rfl
  have hφinj : ∀ b, Injective (φ b) := by
    intro b
    refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    induction a using Path.Homotopic.Quotient.ind with
    | mk δ' =>
      set δ : Path x₀ x₀ := δ'.map continuous_subtype_val
      have hδ : ∀ t, δ t ∈ U ∩ V := fun t => (δ' t).2
      have e : δ' = toSub δ hδ hx₀ hx₀ := by ext; rfl
      rw [e] at ha ⊢
      change φ b (FundamentalGroup.fromPath (.mk (toSub δ hδ hx₀ hx₀))) =
        FundamentalGroup.fromPath (.mk (Path.refl _)) at ha
      rw [hφ_mk, show (Path.refl (⟨x₀, hS b⟩ : S b)) = toSub (Path.refl x₀) (fun _ => hS b) (hS b)
        (hS b) from by ext; rfl] at ha
      have h1 : HomotopicIn (S b) δ (Path.refl x₀) :=
        (homotopicIn_iff_toSub _ (fun _ => hS b) _ _).2 (Path.Homotopic.Quotient.eq.1 ha)
      have h2 : HomotopicIn (U ∩ V) δ (Path.refl x₀) := by
        cases b
        · exact hinjV δ hδ h1
        · exact hinjU δ hδ h1
      have h3 := (homotopicIn_iff_toSub hδ (fun _ => hx₀) hx₀ hx₀).1 h2
      show FundamentalGroup.fromPath (.mk _) = FundamentalGroup.fromPath (.mk (Path.refl _))
      rw [show (Path.refl (⟨x₀, hx₀⟩ : (U ∩ V : Set X))) = toSub (Path.refl x₀) (fun _ => hx₀) hx₀
        hx₀ from by ext; rfl]
      exact congrArg _ (Path.Homotopic.Quotient.eq.2 h3)
  -- the space `U ∪ V` and the data of the gluing
  let Y := (U ∪ V : Set X)
  let S' : Bool → Set Y := fun b => Subtype.val ⁻¹' S b
  let y₀ : Y := ⟨x₀, Or.inl hx₀.1⟩
  let lift : ∀ {T : Set X} (_ : T ⊆ U ∪ V) {y : Y} (_ : JoinedIn T x₀ y), Path y₀ y :=
    fun hT _ hj => pathToSub hj.somePath fun t => hT (hj.somePath_mem t)
  let τ : ∀ y : Y, Path y₀ y := fun y =>
    if hy0 : y = y₀ then (Path.refl y₀).cast rfl hy0
    else if hyW : (y : X) ∈ U ∩ V then lift (inter_subset_left.trans subset_union_left)
      (hW.joinedIn x₀ hx₀ y hyW)
    else if hyU : (y : X) ∈ U then lift subset_union_left (hUc.joinedIn x₀ hx₀.1 y hyU)
    else lift subset_union_right (hVc.joinedIn x₀ hx₀.2 y (y.2.resolve_left hyU))
  have τ_mem : ∀ b y, y ∈ S' b → ∀ t, τ y t ∈ S' b := by
    intro b y hy t
    simp only [τ]
    split_ifs with hy0 hyW hyU
    · exact hy0 ▸ hy
    · exact hWS b ((hW.joinedIn x₀ hx₀ y hyW).somePath_mem t)
    · cases b
      · exact absurd ⟨hyU, hy⟩ hyW
      · exact (hUc.joinedIn x₀ hx₀.1 y hyU).somePath_mem t
    · cases b
      · exact (hVc.joinedIn x₀ hx₀.2 y (y.2.resolve_left hyU)).somePath_mem t
      · exact absurd hy hyU
  let G := Monoid.PushoutI φ
  let f : Bool → Path y₀ y₀ → G := fun b γ =>
    if hγ : ∀ t, ((γ t : Y) : X) ∈ S b then
      (Monoid.PushoutI.of (φ := φ) b (FundamentalGroup.fromPath
        (.mk (toSub (γ.map continuous_subtype_val) hγ (hS b) (hS b)))))⁻¹
    else 1
  have f_eq : ∀ b (γ : Path y₀ y₀) (hγ : ∀ t, ((γ t : Y) : X) ∈ S b), f b γ =
      (Monoid.PushoutI.of (φ := φ) b (FundamentalGroup.fromPath
        (.mk (toSub (γ.map continuous_subtype_val) hγ (hS b) (hS b)))))⁻¹ :=
    fun b γ hγ => dif_pos hγ
  have hS'open : ∀ b, IsOpen (S' b) := fun b => by
    cases b
    · exact hV.preimage continuous_subtype_val
    · exact hU.preimage continuous_subtype_val
  let D : Data Y G :=
    { S := S'
      isOpen := hS'open
      cover := fun y => by
        rcases y.2 with h | h
        · exact ⟨true, h⟩
        · exact ⟨false, h⟩
      x₀ := y₀
      τ := τ
      τ_mem := τ_mem
      τ_x₀ := by simp only [τ, dif_pos rfl]; rfl
      f := f
      f_hom := fun b γ γ' hh => by
        rw [f_eq b γ hh.mem_left, f_eq b γ' hh.mem_right]
        congr 3
        obtain ⟨F, hF⟩ := hh
        refine Path.Homotopic.Quotient.eq.2 ⟨
          { toFun := fun z => ⟨(F z : X), hF z⟩
            continuous_toFun := (continuous_subtype_val.comp F.continuous).subtype_mk _
            map_zero_left := fun t => Subtype.ext (by
              show ((F (0, t) : Y) : X) = _; rw [F.apply_zero]; rfl)
            map_one_left := fun t => Subtype.ext (by
              show ((F (1, t) : Y) : X) = _; rw [F.apply_one]; rfl)
            prop' := fun s t ht => Subtype.ext (by
              have := F.eq_fst s ht
              simp only [ContinuousMap.coe_mk] at this ⊢
              rw [this]; rfl) }⟩
      f_trans := fun b γ γ' h h' => by
        rw [f_eq b γ h, f_eq b γ' h', f_eq b _ (mem_trans h h'), ← mul_inv_rev, ← map_mul]
        congr 2
        have e : ∀ hh, toSub ((γ.trans γ').map continuous_subtype_val) hh (hS b) (hS b) =
            (toSub (γ.map continuous_subtype_val) h (hS b) (hS b)).trans
              (toSub (γ'.map continuous_subtype_val) h' (hS b) (hS b)) := fun hh => by
          ext t
          show ((γ.trans γ') t : X) = (((toSub (γ.map continuous_subtype_val) h (hS b) (hS b)).trans
            (toSub (γ'.map continuous_subtype_val) h' (hS b) (hS b))) t : X)
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs <;> rfl
        rw [e]; rfl
      agree := fun γ h h' => by
        rw [f_eq true γ h, f_eq false γ h']
        congr 1
        have hW' : ∀ t, ((γ t : Y) : X) ∈ U ∩ V := fun t => ⟨h t, h' t⟩
        have e := fun b => (congrArg (fun F => F (FundamentalGroup.fromPath
          (.mk (toSub (γ.map continuous_subtype_val) hW' hx₀ hx₀)))) (Monoid.PushoutI.of_comp_eq_base
            (φ := φ) b))
        simp only [MonoidHom.coe_comp, comp_apply, hφ_mk] at e
        exact (e true).trans (e false).symm }
  obtain ⟨Φ, hΦ, hΦf⟩ := D.exists_extension
  -- read the null-homotopy in `U ∪ V`
  have hγY : ∀ t, γ t ∈ U ∪ V := fun t => Or.inl (hγ t)
  obtain ⟨hY₁, hY₂, hYh⟩ := homotopicIn_iff.1 h
  have e1 := hΦ _ _ hYh
  have hγ' : ∀ t, ((pathToSub γ hγY t : Y) : X) ∈ S true := hγ
  rw [hΦf true _ hγ', show pathToSub (Path.refl x₀) hY₂ = Path.refl y₀ from by ext; rfl,
    hΦf true _ (fun _ => hx₀.1)] at e1
  change f true _ = f true _ at e1
  rw [f_eq true _ hγ', f_eq true (Path.refl y₀) (fun _ => hx₀.1)] at e1
  have e3 : ∀ hh, toSub ((Path.refl y₀).map continuous_subtype_val) hh (hS true) (hS true) =
      Path.refl _ := fun _ => by ext; rfl
  rw [e3, inv_inj] at e1
  have e4 := Monoid.PushoutI.of_injective hφinj true e1
  change FundamentalGroup.fromPath (.mk _) = FundamentalGroup.fromPath (.mk (Path.refl _)) at e4
  have e5 := Path.Homotopic.Quotient.eq.1 e4
  have e6 : ∀ hh, toSub ((pathToSub γ hγY).map continuous_subtype_val) hh (hS true) (hS true) =
      toSub γ hγ hx₀.1 hx₀.1 := fun _ => by ext; rfl
  rw [e6, show (Path.refl (⟨x₀, hS true⟩ : S true)) = toSub (Path.refl x₀) (fun _ => hx₀.1)
    hx₀.1 hx₀.1 from by ext; rfl] at e5
  exact (homotopicIn_iff_toSub hγ (fun _ => hx₀.1) hx₀.1 hx₀.1).2 e5


/-- `U ∖ pathComponentIn U x` is open (a union of path components of `U`). -/
theorem isOpen_diff_pathComponentIn [LocPathConnectedSpace X] {U : Set X} (hU : IsOpen U)
    (x : X) : IsOpen (U \ pathComponentIn U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y ⟨hyU, hyx⟩
  refine Filter.mem_of_superset ((hU.pathComponentIn y).mem_nhds (mem_pathComponentIn_self hyU))
    fun z hz => ⟨pathComponentIn_subset hz, fun hzx => hyx ?_⟩
  exact hzx.trans hz.symm

/-- **The injectivity consequence of Seifert–van Kampen, without connectedness of `U`, `V`**
(`X` locally path-connected): only `U ∩ V` is assumed path-connected; the theorem is applied to
the path components of `x₀` in `U` and `V`, and a null-homotopy in `U ∪ V` (path-connected,
containing `x₀`) stays in their union, which is clopen in `U ∪ V`. -/
theorem homotopicIn_of_homotopicIn_union' [LocPathConnectedSpace X] {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hW : IsPathConnected (U ∩ V)) {x₀ : X} (hx₀ : x₀ ∈ U ∩ V)
    (hinjU : ∀ δ : Path x₀ x₀, (∀ t, δ t ∈ U ∩ V) → HomotopicIn U δ (Path.refl x₀) →
      HomotopicIn (U ∩ V) δ (Path.refl x₀))
    (hinjV : ∀ δ : Path x₀ x₀, (∀ t, δ t ∈ U ∩ V) → HomotopicIn V δ (Path.refl x₀) →
      HomotopicIn (U ∩ V) δ (Path.refl x₀))
    {γ : Path x₀ x₀} (hγ : ∀ t, γ t ∈ U) (h : HomotopicIn (U ∪ V) γ (Path.refl x₀)) :
    HomotopicIn U γ (Path.refl x₀) := by
  set U₀ := pathComponentIn U x₀
  set V₀ := pathComponentIn V x₀
  have hWU : U ∩ V ⊆ U₀ := hW.subset_pathComponentIn hx₀ inter_subset_left
  have hWV : U ∩ V ⊆ V₀ := hW.subset_pathComponentIn hx₀ inter_subset_right
  have hW₀ : U₀ ∩ V₀ = U ∩ V := Subset.antisymm
    (inter_subset_inter pathComponentIn_subset pathComponentIn_subset) (subset_inter hWU hWV)
  have hγ₀ : ∀ t, γ t ∈ U₀ := fun t =>
    (isPathConnected_range γ.continuous).subset_pathComponentIn ⟨0, γ.source⟩
      (range_subset_iff.2 hγ) ⟨t, rfl⟩
  -- the null-homotopy stays in `U₀ ∪ V₀`
  obtain ⟨F, hF⟩ := h
  have hFr : range F ⊆ U₀ ∪ V₀ := by
    have hO : IsOpen (U₀ ∪ V₀) := (hU.pathComponentIn x₀).union (hV.pathComponentIn x₀)
    have hO' : IsOpen ((U \ U₀) ∪ (V \ V₀)) :=
      (isOpen_diff_pathComponentIn hU x₀).union (isOpen_diff_pathComponentIn hV x₀)
    have hdisj : Disjoint (U₀ ∪ V₀) ((U \ U₀) ∪ (V \ V₀)) := by
      rw [Set.disjoint_left]
      rintro z (hz | hz) (⟨hzU, hzU₀⟩ | ⟨hzV, hzV₀⟩)
      · exact hzU₀ hz
      · exact hzV₀ (hWV ⟨pathComponentIn_subset hz, hzV⟩)
      · exact hzU₀ (hWU ⟨hzU, pathComponentIn_subset hz⟩)
      · exact hzV₀ hz
    have hcov : range F ⊆ (U₀ ∪ V₀) ∪ ((U \ U₀) ∪ (V \ V₀)) := by
      rintro _ ⟨z, rfl⟩
      rcases hF z with hz | hz
      · by_cases h0 : F z ∈ U₀
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl ⟨hz, h0⟩)
      · by_cases h0 : F z ∈ V₀
        · exact Or.inl (Or.inr h0)
        · exact Or.inr (Or.inr ⟨hz, h0⟩)
    refine (isPreconnected_range F.continuous).subset_left_of_subset_union hO hO' hdisj hcov
      ⟨x₀, ⟨(0, 0), by simp⟩, Or.inl (mem_pathComponentIn_self hx₀.1)⟩
  have hres := homotopicIn_of_homotopicIn_union (hU.pathComponentIn x₀) (hV.pathComponentIn x₀)
    (isPathConnected_pathComponentIn hx₀.1) (isPathConnected_pathComponentIn hx₀.2)
    (hW₀ ▸ hW) (hW₀ ▸ hx₀)
    (fun δ hδ hh => hW₀ ▸ hinjU δ (hW₀ ▸ hδ) (hh.mono pathComponentIn_subset))
    (fun δ hδ hh => hW₀ ▸ hinjV δ (hW₀ ▸ hδ) (hh.mono pathComponentIn_subset))
    hγ₀ ⟨F, fun z => hFr ⟨z, rfl⟩⟩
  exact hres.mono pathComponentIn_subset

end Injectivity

end VanKampen

end GX
