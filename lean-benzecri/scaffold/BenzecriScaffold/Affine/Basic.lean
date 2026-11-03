import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Real.Irrational

/-!
# `BenzecriScaffold.Affine.Basic` — affine spaces and affine maps (Ch. 1 § 1, Déf. 1–2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 233–234; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45b (wave 1, layer L0).

* **`bzdef:c1s1d1_espace_affin`** — `benzecri1960_ch1.tex:132` (Déf. 1, l.132–147: the definition
  l.132–142, the Exemple l.144–147, p. 233): `Benzecri.IsSimplyTransitive` (as printed, which admits
  `A = ∅`) and `Benzecri.IsAffineSpace` (the reading of DEC-114: an affine space is nonempty), proved
  equivalent to Mathlib's `AddTorsor` (`Benzecri.exists_addTorsor_iff`,
  `Benzecri.isAffineSpace_iff_exists_addTorsor`), the vector `MN` (`Benzecri.vec`,
  `Benzecri.vec_vadd`, `Benzecri.eq_vec_iff`), the example (`Benzecri.vec_eq_sub`).
* **`bzdef:c1s1d2_application_affine`** — `benzecri1960_ch1.tex:149` (Déf. 2, l.149–165: the
  definition l.149–157, the Exemple l.159–165, pp. 233–234). Certified under DEC-114, which rules the
  missing « linéaire » before « application $l'$ » an evident slip: `Benzecri.IsAffine k l` (`l'`
  linear over the common scalars `k`), proved equivalent to Mathlib's `AffineMap`
  (`Benzecri.isAffine_iff`); the Exemple (affine functions to the scalars, `l'` in the dual) is
  `Benzecri.affineFunction_iff` / `Benzecri.affineFunction_iff_isAffine`. The literal reading
  (`Benzecri.IsAffinePrinted`, `l'` any map) is kept as a remark, not a finding against the paper:
  `l'` is then unique and additive, printed + continuity ⟺ continuous affine
  (`isAffinePrinted_and_continuous_iff`), hence ⟺ affine in finite dimension
  (`isAffinePrinted_and_continuous_iff_of_finiteDimensional`), and without continuity it admits a
  non-affine map (`not_isAffinePrinted_imp_affine`, which needs choice).

> **Déf. 1.** On définit sur $A$ une structure d'*espace affin* par la donnée d'un espace vectoriel
> $T(A)$ et d'une opération de $T(A)$ sur $A$ par laquelle $T(A)$, considéré comme groupe abélien,
> opère simplement et transitivement sur $A$.
>
> $T(A)$ est appelé *espace vectoriel de translation* de $A$. L'opération de $T(A)$ sur $A$
> est notée $+$.
>
> Soit $M$ et $N$ deux éléments de $A$. On note $MN$ l'unique élément de $T(A)$ tel que
> $M+MN=N$.
>
> *Exemple.* Soit $E$ un espace vectoriel. E est muni canoniquement d'une structure d'espace affin
> dont le groupe des translations est $E$ : on fait opérer $E$ sur lui-même par l'addition.
>
> **Déf. 2.** Soit $A$ et $B$ deux espaces affins; $T(A)$ et $T(B)$ les espaces vectoriels définis
> sur un même corps, des translations de $A$ et $B$ respectivement. Une application $l$ de $A$ dans
> $B$ est appelée *application affine* s'il existe une application $l'$ de $T(A)$ dans $T(B)$
> telle que, quels que soient $M\in A$ et $m\in T(A)$, on ait $l(M+m)=l(M)+l'(m)$.
>
> *Exemple.* Soit $A$ un espace affin, $T(A)$ l'espace vectoriel sur $\R$ des translations de $A$.
> Une application $l$ de $A$ dans $\R$ est appelée application affine de $A$ dans $\R$, ou fonction
> linéaire sur $A$, s'il existe un élément $l'$ du dual de $T(A)$ tel que, quels que soient $M$ et
> $N$ dans $A$, on ait $l(N)-l(M)=l'(MN)$.

**Notation.** Benzécri writes the action on the right, `M + m`; Mathlib writes `m +ᵥ M` (the group
is abelian, so nothing is lost). His `MN` is Mathlib's `N -ᵥ M`, named `Benzecri.vec M N` here.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 1: `T(A)` a vector space acting simply and transitively, as an abelian group | ✓ carried: `IsSimplyTransitive V P` for `[AddGroup V] [AddAction V P]` (⚠ weakened: commutativity and the scalars are not used by the definition) |
| Déf. 1: `A` nonempty (reading, DEC-114) | ✓ carried by `IsAffineSpace` (`Nonempty P ∧ IsSimplyTransitive V P`), which is Mathlib's `AddTorsor`; `IsSimplyTransitive` alone also admits `A = ∅` |
| Déf. 2: `T(A)`, `T(B)` over a common field, `l'` linear (« linéaire » restored, DEC-114) | ✓ carried by `IsAffine k l` (⚠ weakened: `k` any ring) |
| Déf. 2 Exemple: `l'` in the dual of `T(A)`, over `ℝ` | ✓ carried (`Module.Dual k V`), over any commutative ring `k` (⚠ weakened from `ℝ`) |

## SCOPE (disclosed)

* **Reading (Déf. 2, l.149–157, DEC-114).** The printed text says « une application $l'$ », without
  « linéaire »; the intent is evident from « sur un même corps » (l.150), idle unless `l'` is linear,
  and from the Exemple's « élément $l'$ du dual » (l.162). Déf. 2 is therefore `IsAffine k`, which is
  Mathlib's `AffineMap` (`isAffine_iff`). **Remark on the literal reading** (not a finding): with `l'`
  any map, the identity forces `l'` additive (`IsAffinePrinted.exists_addMonoidHom`) and unique
  (`IsAffinePrinted.linear_unique`), not `ℝ`-linear: `not_isAffinePrinted_imp_affine` exhibits a
  `ℚ`-linear, non-`ℝ`-linear `l : ℝ → ℝ`; that witness needs the axiom of choice (every measurable or
  locally bounded solution is affine), and under continuity the two readings agree
  (`isAffinePrinted_and_continuous_iff`).
* **Reading (Déf. 1, DEC-114).** An affine space is nonempty: `IsAffineSpace`. The printed
  definition does not exclude `A = ∅` (`IsSimplyTransitive` admits it); Mathlib's `AddTorsor` does.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

namespace Benzecri

/-! ### Déf. 1 — affine spaces -/

section Def1

variable (V P : Type*) [AddGroup V] [AddAction V P]

/-- **Déf. 1** (`bzdef:c1s1d1_espace_affin`, p. 233): the group `V` (« $T(A)$, considéré comme
groupe abélien ») acts *simply and transitively* on `P`: for all `M, N` there is exactly one `v`
with `M + v = N` (Mathlib: `v +ᵥ M = N`). -/
def IsSimplyTransitive : Prop := ∀ M N : P, ∃! v : V, v +ᵥ M = N

variable {V P}

/-- « simplement et transitivement »: simply transitive = transitive and free. -/
theorem isSimplyTransitive_iff :
    IsSimplyTransitive V P ↔
      AddAction.IsPretransitive V P ∧ ∀ (v : V) (M : P), v +ᵥ M = M → v = 0 := by
  constructor
  · intro h
    refine ⟨⟨fun M N => (h M N).exists⟩, fun v M hv => ?_⟩
    exact (h M M).unique hv (zero_vadd V M)
  · rintro ⟨ht, hf⟩ M N
    obtain ⟨v, hv⟩ := ht.exists_vadd_eq M N
    refine ⟨v, hv, fun w hw => ?_⟩
    have : (-v + w) +ᵥ M = M := by rw [add_vadd, hw, ← hv, ← add_vadd, neg_add_cancel, zero_vadd]
    have h0 := hf _ _ this
    rw [neg_add_eq_zero] at h0
    exact h0.symm

end Def1

section Torsor

variable {V P : Type*} [AddGroup V] [AddTorsor V P]

/-- A Mathlib `AddTorsor` is a simply transitive action. -/
theorem isSimplyTransitive_of_addTorsor : IsSimplyTransitive V P := fun M N =>
  ⟨N -ᵥ M, vsub_vadd N M, fun v hv => by rw [← hv, vadd_vsub]⟩

/-- **The vector `MN`** (Déf. 1, « On note $MN$ l'unique élément de $T(A)$ tel que $M+MN=N$ »):
Mathlib's `N -ᵥ M`. -/
def vec (M N : P) : V := N -ᵥ M

/-- `M + MN = N`. -/
@[simp] theorem vec_vadd (M N : P) : vec M N +ᵥ M = N := vsub_vadd N M

/-- `MN` is the unique vector with `M + MN = N`. -/
theorem eq_vec_iff {M N : P} {v : V} : v = vec M N ↔ v +ᵥ M = N := by
  constructor
  · rintro rfl; exact vec_vadd M N
  · rintro rfl; exact (vadd_vsub v M).symm

/-- The example after Déf. 1: a group acting on itself by addition; there `MN = N - M`. -/
theorem vec_eq_sub {E : Type*} [AddGroup E] (M N : E) : vec M N = N - M := vsub_eq_sub N M

end Torsor

/-- The `AddTorsor` structure of a nonempty simply transitive action, extending the given action
(`MN` is the unique `v` with `v +ᵥ M = N`). -/
@[reducible] def addTorsorOfIsSimplyTransitive {V P : Type*} [AddGroup V] [inst : AddAction V P]
    (hne : Nonempty P) (h : IsSimplyTransitive V P) : AddTorsor V P where
  toAddAction := inst
  vsub N M := Classical.choose (h M N).exists
  nonempty := hne
  vsub_vadd' N M := Classical.choose_spec (h M N).exists
  vadd_vsub' v M := (h M (v +ᵥ M)).unique (Classical.choose_spec (h M (v +ᵥ M)).exists) rfl

/-- Mathlib's `AddTorsor` is Déf. 1 for a NONEMPTY `A`: an action of `V` on `P` extends to an
`AddTorsor` (with the same action) iff `P` is nonempty and the action is simply transitive. -/
theorem exists_addTorsor_iff (V P : Type*) [AddGroup V] [inst : AddAction V P] :
    (∃ T : AddTorsor V P, T.toAddAction = inst) ↔ Nonempty P ∧ IsSimplyTransitive V P := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.nonempty, isSimplyTransitive_of_addTorsor⟩
  · rintro ⟨hne, h⟩
    exact ⟨addTorsorOfIsSimplyTransitive hne h, rfl⟩

/-- **Déf. 1 in the reading of DEC-114** (`bzdef:c1s1d1_espace_affin`): an *affine space* is a
nonempty set on which `T(A)` acts simply and transitively. -/
def IsAffineSpace (V P : Type*) [AddGroup V] [AddAction V P] : Prop :=
  Nonempty P ∧ IsSimplyTransitive V P

/-- Déf. 1 (read nonempty) is exactly Mathlib's `AddTorsor` with the given action. -/
theorem isAffineSpace_iff_exists_addTorsor (V P : Type*) [AddGroup V] [inst : AddAction V P] :
    IsAffineSpace V P ↔ ∃ T : AddTorsor V P, T.toAddAction = inst :=
  (exists_addTorsor_iff V P).symm

/-! ### Déf. 2 — affine maps -/

section Def2

variable {V₁ P₁ V₂ P₂ : Type*} [AddCommGroup V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂]
  [AddTorsor V₂ P₂]

variable (k : Type*) [Ring k] [Module k V₁] [Module k V₂] in
/-- **Déf. 2** (`bzdef:c1s1d2_application_affine`, pp. 233–234), with `l'` linear (DEC-114: the
missing « linéaire » is an evident slip): `l : A → B` is *affine* if there is a `k`-linear map
`l' : T(A) → T(B)`, `T(A)` and `T(B)` being vector spaces over the same `k` (« définis sur un même
corps »), such that `l(M + m) = l(M) + l'(m)` for all `M ∈ A`, `m ∈ T(A)`. -/
def IsAffine (l : P₁ → P₂) : Prop :=
  ∃ l' : V₁ →ₗ[k] V₂, ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l' m +ᵥ l M

/-- **Déf. 2 is Mathlib's `AffineMap`**: `l` is affine (`IsAffine k l`) iff it is the underlying
function of a `k`-affine map. -/
theorem isAffine_iff (k : Type*) [Ring k] [Module k V₁] [Module k V₂] (l : P₁ → P₂) :
    IsAffine k l ↔ ∃ f : P₁ →ᵃ[k] P₂, ⇑f = l := by
  constructor
  · rintro ⟨l', h⟩
    exact ⟨⟨l, l', h⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.linear, fun M m => f.map_vadd M m⟩

/-- An affine map is affine in the sense of Déf. 2. -/
theorem isAffine_of_affineMap {k : Type*} [Ring k] [Module k V₁] [Module k V₂] (f : P₁ →ᵃ[k] P₂) :
    IsAffine k f :=
  (isAffine_iff k f).2 ⟨f, rfl⟩

variable (V₁ V₂) in
/-- **Déf. 2 read literally** (remark, DEC-114): `l : A → B` such that there is a MAP
`l' : T(A) → T(B)` (« linéaire » omitted) with `l(M + m) = l(M) + l'(m)`. Kept to record what the
literal text admits (`not_isAffinePrinted_imp_affine`); Déf. 2 itself is `IsAffine`. -/
def IsAffinePrinted (l : P₁ → P₂) : Prop :=
  ∃ l' : V₁ → V₂, ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l' m +ᵥ l M

/-- The map `l'` of Déf. 2 is unique: `l'(m) = l(M + m) - l(M)` for any `M`. -/
theorem IsAffinePrinted.linear_unique {l : P₁ → P₂} {l' l'' : V₁ → V₂}
    (h' : ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l' m +ᵥ l M)
    (h'' : ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l'' m +ᵥ l M) : l' = l'' := by
  obtain ⟨M⟩ := AddTorsor.nonempty (G := V₁) (P := P₁)
  funext m
  exact vadd_right_cancel (l M) ((h' M m).symm.trans (h'' M m))

/-- The map `l'` of the printed Déf. 2 is automatically **additive**. -/
theorem additive_of_isAffinePrinted {l : P₁ → P₂} {l' : V₁ → V₂}
    (h : ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l' m +ᵥ l M) (m n : V₁) :
    l' (m + n) = l' m + l' n := by
  obtain ⟨M⟩ := AddTorsor.nonempty (G := V₁) (P := P₁)
  apply vadd_right_cancel (l M)
  rw [← h, add_vadd, h, h, add_vadd]

/-- Under the printed Déf. 2, `l'` is an additive group homomorphism. -/
theorem IsAffinePrinted.exists_addMonoidHom {l : P₁ → P₂} (hl : IsAffinePrinted V₁ V₂ l) :
    ∃ l' : V₁ →+ V₂, ∀ (M : P₁) (m : V₁), l (m +ᵥ M) = l' m +ᵥ l M := by
  obtain ⟨l', h⟩ := hl
  exact ⟨AddMonoidHom.mk' l' (additive_of_isAffinePrinted h), h⟩

/-- An affine map (Mathlib, `l'` linear) satisfies the printed Déf. 2. -/
theorem isAffinePrinted_of_affineMap {k : Type*} [Ring k] [Module k V₁] [Module k V₂]
    (f : P₁ →ᵃ[k] P₂) : IsAffinePrinted V₁ V₂ f :=
  ⟨f.linear, fun M m => f.map_vadd M m⟩

/-- Déf. 2 implies its literal reading. -/
theorem IsAffine.isAffinePrinted {k : Type*} [Ring k] [Module k V₁] [Module k V₂] {l : P₁ → P₂}
    (hl : IsAffine k l) : IsAffinePrinted V₁ V₂ l :=
  let ⟨l', h⟩ := hl; ⟨l', h⟩

/-- **The example after Déf. 2** (affine functions to the scalars, « fonction linéaire sur $A$ »):
`l(N) - l(M) = l'(MN)` for some `l'` in the dual of `T(A)` iff `l` is an affine map. -/
theorem affineFunction_iff {k : Type*} [CommRing k] [Module k V₁] (l : P₁ → k) :
    (∃ l' : Module.Dual k V₁, ∀ M N : P₁, l N - l M = l' (vec M N)) ↔
      ∃ f : P₁ →ᵃ[k] k, ⇑f = l := by
  constructor
  · rintro ⟨l', h⟩
    refine ⟨⟨l, l', fun M m => ?_⟩, rfl⟩
    have := h M (m +ᵥ M)
    simp only [vec, vadd_vsub] at this
    rw [vadd_eq_add, ← this, sub_add_cancel]
  · rintro ⟨f, rfl⟩
    exact ⟨f.linear, fun M N => by simp [vec]⟩

/-- **The example after Déf. 2 is Déf. 2 with `B` the scalars**: `l(N) - l(M) = l'(MN)` for some
`l'` in the dual of `T(A)` iff `l : A → k` is affine in the sense of `IsAffine k`. -/
theorem affineFunction_iff_isAffine {k : Type*} [CommRing k] [Module k V₁] (l : P₁ → k) :
    (∃ l' : Module.Dual k V₁, ∀ M N : P₁, l N - l M = l' (vec M N)) ↔ IsAffine k l :=
  (affineFunction_iff l).trans (isAffine_iff k l).symm

/-! #### Over `ℝ`: the printed Déf. 2, continuity, and linearity -/

section Real

variable {V₁ P₁ V₂ P₂ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [MetricSpace P₁]
  [NormedAddTorsor V₁ P₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [MetricSpace P₂]
  [NormedAddTorsor V₂ P₂]

/-- **Printed Déf. 2 + continuity ⟺ continuous affine map** (real normed affine spaces, any
dimension): continuity forces the additive `l'` to be `ℝ`-linear. -/
theorem isAffinePrinted_and_continuous_iff (l : P₁ → P₂) :
    IsAffinePrinted V₁ V₂ l ∧ Continuous l ↔ ∃ f : P₁ →ᴬ[ℝ] P₂, ⇑f = l := by
  constructor
  · rintro ⟨hl, hc⟩
    obtain ⟨l', h⟩ := hl.exists_addMonoidHom
    obtain ⟨M₀⟩ := AddTorsor.nonempty (G := V₁) (P := P₁)
    have hl' : ∀ m, l' m = l (m +ᵥ M₀) -ᵥ l M₀ := fun m => by rw [h, vadd_vsub]
    have hcont : Continuous l' := by
      have : (l' : V₁ → V₂) = fun m => l (m +ᵥ M₀) -ᵥ l M₀ := funext hl'
      rw [this]
      exact (hc.comp (continuous_id.vadd continuous_const)).vsub continuous_const
    let L : V₁ →L[ℝ] V₂ := l'.toRealLinearMap hcont
    exact ⟨⟨⟨l, L.toLinearMap, fun M m => h M m⟩, hc⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨isAffinePrinted_of_affineMap f.toAffineMap, f.cont⟩

/-- In finite dimension: **printed Déf. 2 + continuity ⟺ affine map** (every affine map of a
finite-dimensional real affine space is continuous). -/
theorem isAffinePrinted_and_continuous_iff_of_finiteDimensional [FiniteDimensional ℝ V₁]
    (l : P₁ → P₂) : IsAffinePrinted V₁ V₂ l ∧ Continuous l ↔ ∃ f : P₁ →ᵃ[ℝ] P₂, ⇑f = l := by
  rw [isAffinePrinted_and_continuous_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.toAffineMap, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f, f.continuous_of_finiteDimensional⟩, rfl⟩

end Real

/-- **Remark on the literal reading of Déf. 2** (DEC-114: not a finding against the paper, whose
`l'` is linear): over `ℝ`, the literal text (`l'` any map) does not imply that `l` is an affine map.
Witness: a `ℚ`-linear `l : ℝ → ℝ` with `l 1 = 0` and `l √2 ≠ 0` (from a `ℚ`-linear form given by
`Submodule.exists_le_ker_of_notMem`, which uses the axiom of choice: no measurable or locally
bounded witness exists); it satisfies `l(M + m) = l(M) + l(m)` but is not `ℝ`-linear. -/
theorem not_isAffinePrinted_imp_affine :
    ∃ l : ℝ → ℝ, IsAffinePrinted ℝ ℝ l ∧ ¬ ∃ f : ℝ →ᵃ[ℝ] ℝ, ⇑f = l := by
  have hnot : Real.sqrt 2 ∉ Submodule.span ℚ ({1} : Set ℝ) := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨q, hq⟩
    apply irrational_sqrt_two
    exact ⟨q, by rw [← hq, Rat.smul_def, mul_one]⟩
  obtain ⟨g, hg2, hg1⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hg1' : g 1 = 0 := hg1 (Submodule.mem_span_singleton_self 1)
  let l : ℝ →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom.comp g.toAddMonoidHom
  refine ⟨l, ⟨l, fun M m => by simp [vadd_eq_add, map_add]⟩, ?_⟩
  rintro ⟨f, hf⟩
  have hlin : ∀ x : ℝ, l x = x * l 1 := by
    intro x
    have h1 := f.map_vadd 0 x
    have h2 := f.map_vadd 0 1
    rw [hf] at h1 h2
    simp only [vadd_eq_add, add_zero] at h1 h2
    have h0 : l 0 = 0 := map_zero l
    rw [h0, add_zero] at h1 h2
    rw [h1, h2, ← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]
  have := hlin (Real.sqrt 2)
  simp only [l, AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, Rat.coe_castHom, LinearMap.toAddMonoidHom_coe, hg1', Rat.cast_zero,
    mul_zero, Rat.cast_eq_zero] at this
  exact hg2 this

end Def2

end Benzecri
