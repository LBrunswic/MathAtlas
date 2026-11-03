import Causal.Flat.Externals
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.FiniteType

/-!
# `Causal.Flat.SelbergBase` — the shared vocabulary of the proof of Selberg's lemma (DEC-115)

The named external `SelbergLemma` (DEC-36, DEC-44; `Flat/Externals.lean` §5) is to be **proved**
by the congruence-subgroup argument (DEC-115). This file holds what the three step modules share,
and **no label is marked**: Selberg's lemma has no paper environment (Barbot cites it, [10.G]).

* `SelbergProperty Γ` — Selberg's conclusion for an abstract group `Γ`; `SelbergLemma V` is
  `SelbergProperty (V ≃ₗ[ℝ] V)` by definition (`selbergLemma_iff_selbergProperty`).
* `SelbergProperty.of_injective` — transport along an injective morphism, **no `sorry`**.
* `glLinearEquiv b : GL (Fin n) ℝ ≃* (V ≃ₗ[ℝ] V)` for a basis `b`, and
  `selbergLemma_of_selbergProperty_GL`, **no `sorry`**: the matrix form gives `SelbergLemma V`.
* `congrKer n φ` — the congruence kernel `ker (GL_n(R) → GL_n(F))` of a ring morphism `φ : R → F`.
* The two step statements, as `Prop`s, so that the matrix reduction (`Flat/SelbergMatrix`) is
  provable in parallel with them: `ResidueCharsStatement` (proved in `Flat/SelbergResidue`) and
  `CongrStatement` (proved in `Flat/SelbergTorsion`).

> Selberg's lemma: a finitely generated subgroup of $GL(n, \mathbb{R})$ has a torsion-free
> subgroup of finite index. (cited by Barbot, [10.G]; the form of DEC-44)

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| finitely generated linear group, char 0 | ✓ carried as in `SelbergLemma` (over `ℝ`, finite-dimensional `V`) |

## SCOPE (disclosed)
* Definitions and transport only; the mathematics is in `Flat/SelbergResidue`,
  `Flat/SelbergTorsion`, `Flat/SelbergMatrix`, assembled in `Flat/SelbergProof`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-115.
-/

namespace Causal.Flat

open Function

/-- **Selberg's conclusion for an abstract group**: every finitely generated subgroup has a
torsion-free subgroup of finite (relative) index. -/
def SelbergProperty (Γ : Type*) [Group Γ] : Prop :=
  ∀ G : Subgroup Γ, G.FG →
    ∃ H : Subgroup Γ, H ≤ G ∧ H.relIndex G ≠ 0 ∧ IsTorsionFreeSubgroup H

theorem selbergLemma_iff_selbergProperty (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] : SelbergLemma V ↔ SelbergProperty (V ≃ₗ[ℝ] V) :=
  Iff.rfl

/-- **Selberg's property descends along an injective group morphism.** -/
theorem SelbergProperty.of_injective {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ)
    (hf : Injective f) (h : SelbergProperty Δ) : SelbergProperty Γ := by
  intro G hG
  obtain ⟨H', -, hi, htf⟩ := h (G.map f) (fg_map_of_fg hG f)
  refine ⟨G ⊓ H'.comap f, inf_le_left, ?_, fun g hg hfin => ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    exact hi
  · exact hf ((htf _ hg.2 (f.isOfFinOrder hfin)).trans f.map_one.symm)

/-- `GL_n(ℝ) ≃* GL(V)` through a basis `b` of `V`. -/
noncomputable def glLinearEquiv {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) : Matrix.GeneralLinearGroup (Fin n) ℝ ≃* (V ≃ₗ[ℝ] V) :=
  (Matrix.GeneralLinearGroup.toLin' b).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ V)

/-- **The matrix form gives `SelbergLemma V`**, for every finite-dimensional real `V`. -/
theorem selbergLemma_of_selbergProperty_GL
    (h : ∀ n : ℕ, SelbergProperty (Matrix.GeneralLinearGroup (Fin n) ℝ))
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] : SelbergLemma V :=
  let b := Module.finBasis ℝ V
  (h _).of_injective (glLinearEquiv b).symm.toMonoidHom (glLinearEquiv b).symm.injective

/-- **The congruence kernel** of a ring morphism `φ : R →+* F`: the kernel of the reduction
`GL_n(R) →* GL_n(F)`, entrywise `φ`. -/
def congrKer (n : ℕ) {R F : Type*} [CommRing R] [CommRing F] (φ : R →+* F) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) R) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) φ).ker

/-- **Step 2 (residue fields), as a statement**: a domain of characteristic `0` that is a finitely
generated `ℤ`-algebra has two finite residue fields of distinct characteristics. Proved as
`residueCharsStatement` in `Flat/SelbergResidue`. -/
def ResidueCharsStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R],
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂)
      (_ : R →+* F₁) (_ : R →+* F₂), ringChar F₁ ≠ ringChar F₂

/-- **Steps 3–4 (congruence kernels), as a statement**: for a domain `R` and two morphisms to
finite fields of distinct characteristics, the intersection of the two congruence kernels has
finite index in `GL_n(R)` and is torsion-free. Proved as `congrStatement` in
`Flat/SelbergTorsion`. -/
def CongrStatement : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (F₁ F₂ : Type) [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (φ₁ : R →+* F₁) (φ₂ : R →+* F₂), ringChar F₁ ≠ ringChar F₂ →
      (congrKer n φ₁ ⊓ congrKer n φ₂).index ≠ 0 ∧
        IsTorsionFreeSubgroup (congrKer n φ₁ ⊓ congrKer n φ₂)

end Causal.Flat
