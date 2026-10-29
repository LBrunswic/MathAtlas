import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases

/-!
# Causalities: a causal preorder and an open chronological relation on every open set

**`defi:causalite`** — `ETT.tex:237`. **`def:precausality`** — `ETT.tex:364`.

> Equivalently, a causality is a pair $(\leq,\ll)=(\leq_{\U},\ll_\U)_{\U\subset M}$ of families
> of preorder relations on $M$, where $\U$ ranges over the open subsets of $M$, such that the
> following holds for every open subset $\U$ of $M$: (a) $\leq_\U$ is a preorder, i.e. reflexive
> and transitive; (b) for every open $\V\subset \U$ and all $x,y\in \V$,
> $x\leq_{\V}y \Rightarrow x\leq_{\U}y$ and $x\ll_{\V}y\Rightarrow x\ll_{\U}y$; (c) for every
> $A\subset \U$, $I_\U^\pm(A)\subset J_\U^\pm(A)$.

> A sheaf $(\leq,\ll)$ of pairs of transitive binary relations is a precausality if it satisfies
> hypotheses $(a)$ and $(b)$ of Definition `defi:causalite`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `≤_U`, `≪_U` are relations on `U` | ✓ carried: `le_mem_left/right`, `lt_mem_left/right` — the relations live on `M` and hold only between points of `U` |
| (a) `≤_U` is a preorder | ✓ carried: `le_refl`, `le_trans` |
| `≪_U` is transitive (`defi:categorie_C`) | ✓ carried: `lt_trans` |
| (b) monotone in the open set | ✓ carried: `le_mono`, `lt_mono` |
| (c) `I^±_U(A) ⊂ J^±_U(A)` | ✓ carried: `Causality.le_of_lt`, the relational form (`Iplus_subset_Jplus`) |
| `≪_U` is open (`defi:categorie_C`; "a standing assumption") | ✓ carried: `isOpen_lt_right`, `isOpen_lt_left`, stated in `M`; `U` being open this is openness in `U` |
| `M` second countable and Hausdorff (`def:category_topological_spacetimes`) | not part of the structure: each theorem asks for what it uses |

## SCOPE (disclosed)

* The structure is the paper's **"equivalently"** form. The paper's first sentence says *sheaf
  with values in `𝐂`*; no gluing axiom is stated there and none is carried here.
* `defi:categorie_C` is carried on the side of objects only (a preorder and an open transitive
  relation contained in it, which is what each `(U, ≤_U, ≪_U)` is); its morphisms are not defined
  in this file, so that label is not claimed.
* `dual` (time reversal) is not in the paper: it is the device by which a statement about the
  past is the statement about the future of the reversed causality.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

universe u

/-- A **precausality** on `M` (`def:precausality`): for every open `U`, a preorder `le U` and a
transitive relation `lt U` on `U`, both monotone in `U`. The relations are relations on `M`
which hold only between points of `U`. -/
@[ext]
structure Precausality (M : Type u) [TopologicalSpace M] where
  /-- The causal relation `x ≤_U y`. -/
  le : Opens M → M → M → Prop
  /-- The chronological relation `x ≪_U y`. -/
  lt : Opens M → M → M → Prop
  le_mem_left : ∀ {U : Opens M} {x y : M}, le U x y → x ∈ U
  le_mem_right : ∀ {U : Opens M} {x y : M}, le U x y → y ∈ U
  lt_mem_left : ∀ {U : Opens M} {x y : M}, lt U x y → x ∈ U
  lt_mem_right : ∀ {U : Opens M} {x y : M}, lt U x y → y ∈ U
  /-- (a), reflexivity on `U`. -/
  le_refl : ∀ {U : Opens M} {x : M}, x ∈ U → le U x x
  /-- (a), transitivity. -/
  le_trans : ∀ {U : Opens M} {x y z : M}, le U x y → le U y z → le U x z
  lt_trans : ∀ {U : Opens M} {x y z : M}, lt U x y → lt U y z → lt U x z
  /-- (b) for the causal relation. -/
  le_mono : ∀ {U V : Opens M}, V ≤ U → ∀ {x y : M}, le V x y → le U x y
  /-- (b) for the chronological relation. -/
  lt_mono : ∀ {U V : Opens M}, V ≤ U → ∀ {x y : M}, lt V x y → lt U x y

/-- A **causality** on `M` (`defi:causalite`): a precausality whose chronological relation is
contained in the causal one, axiom (c), and is open. -/
@[ext]
structure Causality (M : Type u) [TopologicalSpace M] extends Precausality M where
  /-- (c), in relational form. -/
  le_of_lt : ∀ {U : Opens M} {x y : M}, lt U x y → le U x y
  /-- `I^+_U(x)` is open. -/
  isOpen_lt_right : ∀ (U : Opens M) (x : M), IsOpen {y | lt U x y}
  /-- `I^-_U(x)` is open. -/
  isOpen_lt_left : ∀ (U : Opens M) (x : M), IsOpen {y | lt U y x}

variable {M : Type u} [TopologicalSpace M]

namespace Precausality

variable (P : Precausality M)

/-- The causal future `J^+_U(A)`. -/
def Jplus (U : Opens M) (A : Set M) : Set M := {y | ∃ x ∈ A, P.le U x y}

/-- The causal past `J^-_U(A)`. -/
def Jminus (U : Opens M) (A : Set M) : Set M := {y | ∃ x ∈ A, P.le U y x}

/-- The chronological future `I^+_U(A)`. -/
def Iplus (U : Opens M) (A : Set M) : Set M := {y | ∃ x ∈ A, P.lt U x y}

/-- The chronological past `I^-_U(A)`. -/
def Iminus (U : Opens M) (A : Set M) : Set M := {y | ∃ x ∈ A, P.lt U y x}

/-- Time reversal: the precausality whose future is the past of `P`. -/
def dual : Precausality M where
  le U x y := P.le U y x
  lt U x y := P.lt U y x
  le_mem_left h := P.le_mem_right h
  le_mem_right h := P.le_mem_left h
  lt_mem_left h := P.lt_mem_right h
  lt_mem_right h := P.lt_mem_left h
  le_refl h := P.le_refl h
  le_trans h₁ h₂ := P.le_trans h₂ h₁
  lt_trans h₁ h₂ := P.lt_trans h₂ h₁
  le_mono h _ _ h' := P.le_mono h h'
  lt_mono h _ _ h' := P.lt_mono h h'

variable {P} {U V : Opens M} {A B : Set M} {x y z : M}

@[simp] theorem dual_le : P.dual.le U x y ↔ P.le U y x := Iff.rfl
@[simp] theorem dual_lt : P.dual.lt U x y ↔ P.lt U y x := Iff.rfl
@[simp] theorem dual_dual : P.dual.dual = P := rfl
@[simp] theorem dual_Jplus : P.dual.Jplus U A = P.Jminus U A := rfl
@[simp] theorem dual_Jminus : P.dual.Jminus U A = P.Jplus U A := rfl
@[simp] theorem dual_Iplus : P.dual.Iplus U A = P.Iminus U A := rfl
@[simp] theorem dual_Iminus : P.dual.Iminus U A = P.Iplus U A := rfl

theorem mem_Jplus : y ∈ P.Jplus U A ↔ ∃ x ∈ A, P.le U x y := Iff.rfl
theorem mem_Jminus : y ∈ P.Jminus U A ↔ ∃ x ∈ A, P.le U y x := Iff.rfl
theorem mem_Iplus : y ∈ P.Iplus U A ↔ ∃ x ∈ A, P.lt U x y := Iff.rfl
theorem mem_Iminus : y ∈ P.Iminus U A ↔ ∃ x ∈ A, P.lt U y x := Iff.rfl

@[simp] theorem mem_Jplus_singleton : y ∈ P.Jplus U {x} ↔ P.le U x y := by
  simp [Jplus]

@[simp] theorem mem_Jminus_singleton : y ∈ P.Jminus U {x} ↔ P.le U y x := by
  simp [Jminus]

@[simp] theorem mem_Iplus_singleton : y ∈ P.Iplus U {x} ↔ P.lt U x y := by
  simp [Iplus]

@[simp] theorem mem_Iminus_singleton : y ∈ P.Iminus U {x} ↔ P.lt U y x := by
  simp [Iminus]

theorem Jplus_subset_carrier : P.Jplus U A ⊆ U := fun _ ⟨_, _, h⟩ => P.le_mem_right h
theorem Jminus_subset_carrier : P.Jminus U A ⊆ U := fun _ ⟨_, _, h⟩ => P.le_mem_left h
theorem Iplus_subset_carrier : P.Iplus U A ⊆ U := fun _ ⟨_, _, h⟩ => P.lt_mem_right h
theorem Iminus_subset_carrier : P.Iminus U A ⊆ U := fun _ ⟨_, _, h⟩ => P.lt_mem_left h

/-- A subset of `U` is contained in its causal future in `U`: reflexivity. -/
theorem subset_Jplus (hA : A ⊆ U) : A ⊆ P.Jplus U A := fun x hx => ⟨x, hx, P.le_refl (hA hx)⟩

theorem subset_Jminus (hA : A ⊆ U) : A ⊆ P.Jminus U A := fun x hx => ⟨x, hx, P.le_refl (hA hx)⟩

theorem Jplus_mono (h : A ⊆ B) : P.Jplus U A ⊆ P.Jplus U B :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem Jminus_mono (h : A ⊆ B) : P.Jminus U A ⊆ P.Jminus U B :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem Iplus_mono (h : A ⊆ B) : P.Iplus U A ⊆ P.Iplus U B :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem Iminus_mono (h : A ⊆ B) : P.Iminus U A ⊆ P.Iminus U B :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

/-- Axiom (b) on causal futures. -/
theorem Jplus_mono_opens (h : V ≤ U) : P.Jplus V A ⊆ P.Jplus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, P.le_mono h hxy⟩

theorem Jminus_mono_opens (h : V ≤ U) : P.Jminus V A ⊆ P.Jminus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, P.le_mono h hxy⟩

theorem Iplus_mono_opens (h : V ≤ U) : P.Iplus V A ⊆ P.Iplus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, P.lt_mono h hxy⟩

theorem Iminus_mono_opens (h : V ≤ U) : P.Iminus V A ⊆ P.Iminus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, P.lt_mono h hxy⟩

/-- `J^+_U(J^+_U(A)) ⊂ J^+_U(A)`: transitivity. -/
theorem Jplus_Jplus_subset : P.Jplus U (P.Jplus U A) ⊆ P.Jplus U A :=
  fun _ ⟨_, ⟨x, hx, hxy⟩, hyz⟩ => ⟨x, hx, P.le_trans hxy hyz⟩

theorem Jminus_Jminus_subset : P.Jminus U (P.Jminus U A) ⊆ P.Jminus U A :=
  fun _ ⟨_, ⟨x, hx, hyx⟩, hzy⟩ => ⟨x, hx, P.le_trans hzy hyx⟩

theorem Iplus_Iplus_subset : P.Iplus U (P.Iplus U A) ⊆ P.Iplus U A :=
  fun _ ⟨_, ⟨x, hx, hxy⟩, hyz⟩ => ⟨x, hx, P.lt_trans hxy hyz⟩

theorem Iminus_Iminus_subset : P.Iminus U (P.Iminus U A) ⊆ P.Iminus U A :=
  fun _ ⟨_, ⟨x, hx, hyx⟩, hzy⟩ => ⟨x, hx, P.lt_trans hzy hyx⟩

theorem Jplus_Jplus : P.Jplus U (P.Jplus U A) = P.Jplus U A :=
  Jplus_Jplus_subset.antisymm (subset_Jplus Jplus_subset_carrier)

theorem Jminus_Jminus : P.Jminus U (P.Jminus U A) = P.Jminus U A :=
  Jminus_Jminus_subset.antisymm (subset_Jminus Jminus_subset_carrier)

theorem Jplus_eq_biUnion : P.Jplus U A = ⋃ x ∈ A, P.Jplus U {x} := by
  ext y; simp [mem_Jplus]

theorem Jminus_eq_biUnion : P.Jminus U A = ⋃ x ∈ A, P.Jminus U {x} := by
  ext y; simp [mem_Jminus]

theorem Iplus_eq_biUnion : P.Iplus U A = ⋃ x ∈ A, P.Iplus U {x} := by
  ext y; simp [mem_Iplus]

theorem Iminus_eq_biUnion : P.Iminus U A = ⋃ x ∈ A, P.Iminus U {x} := by
  ext y; simp [mem_Iminus]

@[simp] theorem Jplus_empty : P.Jplus U ∅ = ∅ := by ext; simp [mem_Jplus]
@[simp] theorem Jminus_empty : P.Jminus U ∅ = ∅ := by ext; simp [mem_Jminus]
@[simp] theorem Iplus_empty : P.Iplus U ∅ = ∅ := by ext; simp [mem_Iplus]
@[simp] theorem Iminus_empty : P.Iminus U ∅ = ∅ := by ext; simp [mem_Iminus]

/-- The causal future of a point grows when the point moves to the past. -/
theorem Jplus_singleton_subset (h : P.le U x y) : P.Jplus U {y} ⊆ P.Jplus U {x} := by
  intro z hz
  rw [mem_Jplus_singleton] at hz ⊢
  exact P.le_trans h hz

/-- The causal past of a point grows when the point moves to the future. -/
theorem Jminus_singleton_subset (h : P.le U x y) : P.Jminus U {x} ⊆ P.Jminus U {y} := by
  intro z hz
  rw [mem_Jminus_singleton] at hz ⊢
  exact P.le_trans hz h

end Precausality

namespace Causality

variable (C : Causality M)

/-- Time reversal of a causality. -/
def dual : Causality M where
  toPrecausality := C.toPrecausality.dual
  le_of_lt h := C.le_of_lt h
  isOpen_lt_right U x := C.isOpen_lt_left U x
  isOpen_lt_left U x := C.isOpen_lt_right U x

variable {C} {U V : Opens M} {A B : Set M} {x y z : M}

@[simp] theorem dual_toPrecausality : C.dual.toPrecausality = C.toPrecausality.dual := rfl
@[simp] theorem dual_dual : C.dual.dual = C := rfl

/-- Axiom (c) of `defi:causalite`, for the future. -/
theorem Iplus_subset_Jplus : C.Iplus U A ⊆ C.Jplus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, C.le_of_lt hxy⟩

/-- Axiom (c) of `defi:causalite`, for the past. -/
theorem Iminus_subset_Jminus : C.Iminus U A ⊆ C.Jminus U A :=
  fun _ ⟨x, hx, hxy⟩ => ⟨x, hx, C.le_of_lt hxy⟩

/-- Chronological futures are open. -/
theorem isOpen_Iplus : IsOpen (C.Iplus U A) := by
  rw [Precausality.Iplus_eq_biUnion]
  refine isOpen_biUnion fun x _ => ?_
  have : C.Iplus U {x} = {y | C.lt U x y} := by ext y; simp
  rw [this]
  exact C.isOpen_lt_right U x

/-- Chronological pasts are open. -/
theorem isOpen_Iminus : IsOpen (C.Iminus U A) := C.dual.isOpen_Iplus

/-- A chronological future lies in the interior of the causal future. -/
theorem Iplus_subset_interior_Jplus : C.Iplus U A ⊆ interior (C.Jplus U A) :=
  interior_maximal Iplus_subset_Jplus isOpen_Iplus

theorem Iminus_subset_interior_Jminus : C.Iminus U A ⊆ interior (C.Jminus U A) :=
  interior_maximal Iminus_subset_Jminus isOpen_Iminus

end Causality

end Causal
