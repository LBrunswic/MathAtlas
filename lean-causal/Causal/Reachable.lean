import Causal.Properties
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.CountablyGenerated

/-!
# The continuously reachable past and future `K^±`

**`defi:futur_continue`** — `ETT.tex:759`. **`rem:K_ensemble`** — `ETT.tex:768`.
**`rem:suite_croissante`** — `ETT.tex:790`. **`lem:K_facile`** — `ETT.tex:798`.
**`rem:equivalent_lemma_obviously_holds`** — `ETT.tex:827`.
**`lem:passe_coherent`** — `ETT.tex:837`. **`prop:tarentin_fort_K`** — `ETT.tex:850`.
**`rem:comparable_property_obviously_holds`** — `ETT.tex:868`.
**`prop:K_plongement_ordre`** — `ETT.tex:922`.

> $$K^\pm(p)=\bigcap_{p_n\rightarrow p} \bigcup_{N\in \N} \mathrm{Int}_{J^\pm(p)}\left(
> J^\pm(p)\cap \bigcap_{n\geq N} J^\pm(p_n)\right),$$ the intersection being taken over all
> sequences $(p_n)_{n\in \N}$ of $M$ converging to $p$. For a subset $A\subset M$ we set
> $K^\pm(A):=\bigcup_{p\in A} K^\pm(p)$, and for $\U$ open we write $K^\pm_\U$ for the operator
> obtained by applying these definitions inside the topological spacetime $\U$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `lem:K_facile`: `p_n → p`, `p ∈ \ring J^+(p_n)` for every `n` | ✓ carried |
| — `M` tarentin | ⚠ weakened: not used |
| — second countable, Hausdorff | ⚠ weakened: not used |
| — stated in `M` | ⚠ weakened: stated in every open `U` |
| `rem:suite_croissante`: `p` strongly tarentin in the past; a countable basis of neighbourhoods of `p` | ✓ carried: `FirstCountableTopology M` |
| `lem:passe_coherent`: causally plain, `p ∈ Z^-(M)` | ✓ carried |
| `prop:tarentin_fort_K`: causally plain, `p ∈ Z^-(M)` | ✓ carried |
| — second countable | ⚠ weakened: `FirstCountableTopology M` |
| — absolutely minimal, tarentin, Hausdorff | ⚠ weakened: not used |
| `prop:K_plongement_ordre`: (a) `J^±(x)` closed, (b) `J^±(x) ⊂ closure(K^±(x))` | ✓ carried |
| — `M` causal | ✓ carried for injectivity; ⚠ weakened, not used, for the two implications and the equivalences |
| — second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* **`K^±_U` is defined with sequences of `M`, not of `U`.** For `p ∈ U` the two definitions
  agree, a sequence converging to `p` being eventually in `U` and the sets
  `⋂_{n ≥ N} J^±_U(p_n)` increasing with `N`: this is `mem_Kplus_singleton_iff_seq_mem`. For
  `p ∉ U` the definition here gives `K^±_U(p) = ∅`.
* The relative interior `Int_A(S)` is `interiorWithin A S`, the set of the points of `A` at
  which `S` is a neighbourhood within `A`.
* `rem:K_ensemble` is certified for its three general assertions. Its last sentence is about BTZ
  points of `E^{1,2}_{≥0}`-manifolds and belongs to `prop:K_calcul`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

/-- The interior of `S` relative to `A`: the points of `A` at which `S` is a neighbourhood
within `A`. For `S ⊆ A` this is the interior of `S` in the subspace `A`. -/
def interiorWithin (A S : Set M) : Set M := {x | x ∈ A ∧ S ∈ 𝓝[A] x}

section interiorWithin

variable {A S T : Set M} {x : M}

theorem mem_interiorWithin : x ∈ interiorWithin A S ↔ x ∈ A ∧ S ∈ 𝓝[A] x := Iff.rfl

theorem interiorWithin_subset_left : interiorWithin A S ⊆ A := fun _ h => h.1

theorem interiorWithin_subset : interiorWithin A S ⊆ S :=
  fun _ h => mem_of_mem_nhdsWithin h.1 h.2

theorem interiorWithin_mono (h : S ⊆ T) : interiorWithin A S ⊆ interiorWithin A T :=
  fun _ hx => ⟨hx.1, mem_of_superset hx.2 h⟩

theorem mem_interiorWithin_of_mem_nhds (hx : x ∈ A) (h : S ∈ 𝓝 x) : x ∈ interiorWithin A S :=
  ⟨hx, mem_nhdsWithin_of_mem_nhds h⟩

theorem interiorWithin_inter_self : interiorWithin A (A ∩ S) = interiorWithin A S := by
  refine Subset.antisymm (interiorWithin_mono inter_subset_right) fun x hx => ?_
  exact ⟨hx.1, inter_mem self_mem_nhdsWithin hx.2⟩

end interiorWithin

namespace Causality

variable (C : Causality M)

/-- `defi:futur_continue`: the continuously reachable future `K^+_U(A)`. -/
def Kplus (U : Opens M) (A : Set M) : Set M :=
  ⋃ p ∈ A, ⋂ (u : ℕ → M) (_ : Tendsto u atTop (𝓝 p)),
    ⋃ N : ℕ, interiorWithin (C.Jplus U {p}) (C.Jplus U {p} ∩ ⋂ n ≥ N, C.Jplus U {u n})

/-- `defi:futur_continue`: the continuously reachable past `K^-_U(A)`. -/
def Kminus (U : Opens M) (A : Set M) : Set M :=
  ⋃ p ∈ A, ⋂ (u : ℕ → M) (_ : Tendsto u atTop (𝓝 p)),
    ⋃ N : ℕ, interiorWithin (C.Jminus U {p}) (C.Jminus U {p} ∩ ⋂ n ≥ N, C.Jminus U {u n})

variable {C} {U : Opens M} {A B : Set M} {p q x y : M}

@[simp] theorem dual_Kplus : C.dual.Kplus U A = C.Kminus U A := rfl

@[simp] theorem dual_Kminus : C.dual.Kminus U A = C.Kplus U A := rfl

theorem mem_Kplus : y ∈ C.Kplus U A ↔ ∃ p ∈ A, ∀ u : ℕ → M, Tendsto u atTop (𝓝 p) →
    ∃ N : ℕ, y ∈ interiorWithin (C.Jplus U {p}) (C.Jplus U {p} ∩ ⋂ n ≥ N, C.Jplus U {u n}) := by
  simp only [Kplus, mem_iUnion, mem_iInter, exists_prop]

theorem mem_Kminus : y ∈ C.Kminus U A ↔ ∃ p ∈ A, ∀ u : ℕ → M, Tendsto u atTop (𝓝 p) →
    ∃ N : ℕ, y ∈ interiorWithin (C.Jminus U {p})
      (C.Jminus U {p} ∩ ⋂ n ≥ N, C.Jminus U {u n}) :=
  mem_Kplus (C := C.dual)

theorem mem_Kplus_singleton : y ∈ C.Kplus U {p} ↔ ∀ u : ℕ → M, Tendsto u atTop (𝓝 p) →
    ∃ N : ℕ, y ∈ interiorWithin (C.Jplus U {p}) (C.Jplus U {p} ∩ ⋂ n ≥ N, C.Jplus U {u n}) := by
  simp [mem_Kplus]

theorem mem_Kminus_singleton : y ∈ C.Kminus U {p} ↔ ∀ u : ℕ → M, Tendsto u atTop (𝓝 p) →
    ∃ N : ℕ, y ∈ interiorWithin (C.Jminus U {p})
      (C.Jminus U {p} ∩ ⋂ n ≥ N, C.Jminus U {u n}) :=
  mem_Kplus_singleton (C := C.dual)

theorem Kplus_eq_biUnion : C.Kplus U A = ⋃ p ∈ A, C.Kplus U {p} := by
  ext y
  simp only [mem_iUnion, exists_prop, mem_Kplus_singleton]
  exact mem_Kplus

theorem Kminus_eq_biUnion : C.Kminus U A = ⋃ p ∈ A, C.Kminus U {p} :=
  Kplus_eq_biUnion (C := C.dual)

/-! ### `rem:K_ensemble` -/

/-- `rem:K_ensemble`: `K^+(∅) = ∅`. -/
@[simp] theorem Kplus_empty : C.Kplus U ∅ = ∅ := by
  ext y
  simp [mem_Kplus]

@[simp] theorem Kminus_empty : C.Kminus U ∅ = ∅ := Kplus_empty (C := C.dual)

/-- `rem:K_ensemble`: `K^+` is monotone for inclusion. -/
theorem Kplus_mono (h : A ⊆ B) : C.Kplus U A ⊆ C.Kplus U B := by
  intro y hy
  obtain ⟨p, hp, hy⟩ := mem_Kplus.1 hy
  exact mem_Kplus.2 ⟨p, h hp, hy⟩

theorem Kminus_mono (h : A ⊆ B) : C.Kminus U A ⊆ C.Kminus U B := Kplus_mono (C := C.dual) h

/-- `rem:K_ensemble`: `K^+(A) ⊂ J^+(A)`. -/
theorem Kplus_subset_Jplus : C.Kplus U A ⊆ C.Jplus U A := by
  intro y hy
  obtain ⟨p, hp, hy⟩ := mem_Kplus.1 hy
  obtain ⟨N, hN⟩ := hy (fun _ => p) tendsto_const_nhds
  have : y ∈ C.Jplus U {p} := interiorWithin_subset_left hN
  exact Precausality.Jplus_mono (singleton_subset_iff.2 hp) this

theorem Kminus_subset_Jminus : C.Kminus U A ⊆ C.Jminus U A :=
  Kplus_subset_Jplus (C := C.dual)

/-- **`rem:K_ensemble`**, the three general assertions. -/
theorem K_ensemble (U : Opens M) :
    (C.Kplus U ∅ = ∅ ∧ C.Kminus U ∅ = ∅) ∧
      (∀ A, C.Kplus U A ⊆ C.Jplus U A ∧ C.Kminus U A ⊆ C.Jminus U A) ∧
      ∀ A B, A ⊆ B → C.Kplus U A ⊆ C.Kplus U B ∧ C.Kminus U A ⊆ C.Kminus U B :=
  ⟨⟨Kplus_empty, Kminus_empty⟩, fun _ => ⟨Kplus_subset_Jplus, Kminus_subset_Jminus⟩,
    fun _ _ h => ⟨Kplus_mono h, Kminus_mono h⟩⟩

/-! ### The definition inside an open subset -/

/-- For `p ∈ U`, `K^+_U(p)` may be computed with the sequences of `U` converging to `p`: this
is the paper's definition of `K^+_U`, "applying these definitions inside the topological
spacetime `U`". -/
theorem mem_Kplus_singleton_iff_seq_mem (hp : p ∈ U) :
    y ∈ C.Kplus U {p} ↔ ∀ u : ℕ → M, (∀ n, u n ∈ U) → Tendsto u atTop (𝓝 p) →
      ∃ N : ℕ, y ∈ interiorWithin (C.Jplus U {p})
        (C.Jplus U {p} ∩ ⋂ n ≥ N, C.Jplus U {u n}) := by
  rw [mem_Kplus_singleton]
  refine ⟨fun h u _ hu => h u hu, fun h u hu => ?_⟩
  -- a tail of `u` lies in `U`
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hu.eventually (U.isOpen.mem_nhds hp))
  have hv : Tendsto (fun n => u (n + N₀)) atTop (𝓝 p) := (tendsto_add_atTop_iff_nat N₀).2 hu
  obtain ⟨N, hN⟩ := h (fun n => u (n + N₀)) (fun n => hN₀ _ (Nat.le_add_left _ _)) hv
  refine ⟨N + N₀, interiorWithin_mono (inter_subset_inter_right _ ?_) hN⟩
  intro z hz
  simp only [mem_iInter] at hz ⊢
  intro m hm
  have := hz (m - N₀) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

theorem mem_Kminus_singleton_iff_seq_mem (hp : p ∈ U) :
    y ∈ C.Kminus U {p} ↔ ∀ u : ℕ → M, (∀ n, u n ∈ U) → Tendsto u atTop (𝓝 p) →
      ∃ N : ℕ, y ∈ interiorWithin (C.Jminus U {p})
        (C.Jminus U {p} ∩ ⋂ n ≥ N, C.Jminus U {u n}) :=
  mem_Kplus_singleton_iff_seq_mem (C := C.dual) hp

/-! ### `lem:K_facile` -/

/-- **`lem:K_facile`**, past. If `p_n → p` and `p ∈ \ring J^+(p_n)` for every `n`, then
`K^-(p) = ⋃_N Int_{J^-(p)} (⋂_{n ≥ N} J^-(p_n))`: one sequence computes `K^-(p)`. -/
theorem Kminus_eq_of_tendsto {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p))
    (hp : ∀ n, p ∈ interior (C.Jplus U {u n})) :
    C.Kminus U {p} =
      ⋃ N : ℕ, interiorWithin (C.Jminus U {p}) (⋂ n ≥ N, C.Jminus U {u n}) := by
  ext y
  simp only [mem_iUnion]
  constructor
  · intro hy
    obtain ⟨N, hN⟩ := mem_Kminus_singleton.1 hy u hu
    exact ⟨N, interiorWithin_mono inter_subset_right hN⟩
  · rintro ⟨N₀, hN₀⟩
    rw [mem_Kminus_singleton]
    intro v hv
    -- eventually `u N₀ ≤ v n`
    have hev : ∀ᶠ n in atTop, v n ∈ interior (C.Jplus U {u N₀}) :=
      hv.eventually (isOpen_interior.mem_nhds (hp N₀))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hup : C.le U (u N₀) p := by simpa using interior_subset (hp N₀)
    refine ⟨N, interiorWithin_mono ?_ hN₀⟩
    intro z hz
    simp only [mem_iInter] at hz
    have hz0 : C.le U z (u N₀) := by simpa using hz N₀ le_rfl
    refine ⟨by simpa using C.le_trans hz0 hup, ?_⟩
    simp only [mem_iInter]
    intro n hn
    have hun : C.le U (u N₀) (v n) := by simpa using interior_subset (hN n hn)
    simpa using C.le_trans hz0 hun

/-- **`rem:equivalent_lemma_obviously_holds`**: `lem:K_facile` for `K^+`. -/
theorem Kplus_eq_of_tendsto {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p))
    (hp : ∀ n, p ∈ interior (C.Jminus U {u n})) :
    C.Kplus U {p} =
      ⋃ N : ℕ, interiorWithin (C.Jplus U {p}) (⋂ n ≥ N, C.Jplus U {u n}) :=
  Kminus_eq_of_tendsto (C := C.dual) hu hp

/-! ### `lem:passe_coherent` -/

/-- **`lem:passe_coherent`.** On a causally plain spacetime, at a point strongly tarentin in the
past, `J^-(I^-(p)) = I^-(p)`. -/
theorem Jminus_Iminus_eq_of_mem_Zminus (hP : C.CausallyPlain) (hp : p ∈ C.Zminus) :
    C.Jminus ⊤ (C.Iminus ⊤ {p}) = C.Iminus ⊤ {p} := by
  refine Subset.antisymm ?_ (Precausality.subset_Jminus Precausality.Iminus_subset_carrier)
  rintro q ⟨p', hp', hqp'⟩
  have hp'p : C.lt ⊤ p' p := by simpa using hp'
  -- the open set `I^+(p') ∩ I^-(p)` is non-empty and contained in `J^+(q)`
  have hopen : IsOpen (C.Iplus ⊤ {p'} ∩ C.Iminus ⊤ {p}) := isOpen_Iplus.inter isOpen_Iminus
  have hne : (C.Iplus ⊤ {p'} ∩ C.Iminus ⊤ {p}).Nonempty := by
    obtain ⟨r, hr, hr'⟩ := hp (C.Iplus ⊤ {p'}) (isOpen_Iplus.mem_nhds (by simpa using hp'p))
    exact ⟨r, hr', hr⟩
  have hsub : C.Iplus ⊤ {p'} ∩ C.Iminus ⊤ {p} ⊆ C.Jplus ⊤ {q} := by
    rintro r ⟨hr, -⟩
    have hp'r : C.lt ⊤ p' r := by simpa using hr
    simpa using C.le_trans hqp' (C.le_of_lt hp'r)
  obtain ⟨r, ⟨-, hrp⟩, hqr⟩ := ((causallyPlain_iff.1 hP) ⊤ {q} _ hopen hne).1 hsub
  have hqr' : C.lt ⊤ q r := by simpa using hqr
  have hrp' : C.lt ⊤ r p := by simpa using hrp
  simpa using C.lt_trans hqr' hrp'

/-- `lem:passe_coherent`, future. -/
theorem Jplus_Iplus_eq_of_mem_Zplus (hP : C.CausallyPlain) (hp : p ∈ C.Zplus) :
    C.Jplus ⊤ (C.Iplus ⊤ {p}) = C.Iplus ⊤ {p} :=
  Jminus_Iminus_eq_of_mem_Zminus (C := C.dual) (dual_causallyPlain.2 hP) hp

/-! ### `rem:suite_croissante` -/

/-- **`rem:suite_croissante`.** If `p` is strongly tarentin in the past, every point of `I^-(p)`
is the first term of a sequence of `I^-(p)`, increasing for `≪` and converging to `p`. -/
theorem exists_seq_lt_tendsto_of_mem_Zminus [FirstCountableTopology M] (hp : p ∈ C.Zminus)
    (hq : C.lt ⊤ q p) :
    ∃ u : ℕ → M, u 0 = q ∧ (∀ n, C.lt ⊤ (u n) (u (n + 1))) ∧ (∀ n, C.lt ⊤ (u n) p) ∧
      Tendsto u atTop (𝓝 p) := by
  obtain ⟨B, hB⟩ := (𝓝 p).exists_antitone_basis
  -- one step: from `x ≪ p`, a point of `I^+(x) ∩ B (n+1) ∩ I^-(p)`
  have step : ∀ (n : ℕ) (x : {x : M // C.lt ⊤ x p}),
      ∃ y : {y : M // C.lt ⊤ y p}, C.lt ⊤ x.1 y.1 ∧ y.1 ∈ B (n + 1) := by
    intro n x
    have hN : C.Iplus ⊤ {x.1} ∩ B (n + 1) ∈ 𝓝 p :=
      inter_mem (isOpen_Iplus.mem_nhds (by simpa using x.2)) (hB.mem (n + 1))
    obtain ⟨y, hy, hxy, hyB⟩ := hp _ hN
    exact ⟨⟨y, by simpa using hy⟩, by simpa using hxy, hyB⟩
  choose next hnext hnextB using step
  let w : ℕ → {x : M // C.lt ⊤ x p} := fun n => Nat.rec ⟨q, hq⟩ (fun k x => next k x) n
  have hw_succ : ∀ n, w (n + 1) = next n (w n) := fun _ => rfl
  refine ⟨fun n => (w n).1, rfl, fun n => ?_, fun n => (w n).2, ?_⟩
  · show C.lt ⊤ (w n).1 (w (n + 1)).1
    rw [hw_succ]
    exact hnext n (w n)
  · refine (tendsto_add_atTop_iff_nat 1).1 ?_
    refine hB.tendsto fun n => ?_
    show (w (n + 1)).1 ∈ B n
    rw [hw_succ]
    exact hB.antitone (Nat.le_succ n) (hnextB n (w n))

/-- `rem:suite_croissante`, future. -/
theorem exists_seq_lt_tendsto_of_mem_Zplus [FirstCountableTopology M] (hp : p ∈ C.Zplus)
    (hq : C.lt ⊤ p q) :
    ∃ u : ℕ → M, u 0 = q ∧ (∀ n, C.lt ⊤ (u (n + 1)) (u n)) ∧ (∀ n, C.lt ⊤ p (u n)) ∧
      Tendsto u atTop (𝓝 p) :=
  exists_seq_lt_tendsto_of_mem_Zminus (C := C.dual) hp hq

/-- A sequence increasing for `≪` is non-decreasing for `≤`. -/
theorem le_of_forall_lt_succ {u : ℕ → M} (h : ∀ n, C.lt U (u n) (u (n + 1))) {m n : ℕ}
    (hmn : m ≤ n) : C.le U (u m) (u n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact C.le_refl (C.lt_mem_left (h m))
  | succ n _ ih => exact C.le_trans ih (C.le_of_lt (h n))

/-! ### `prop:tarentin_fort_K` -/

/-- **`prop:tarentin_fort_K`.** On a causally plain spacetime, at a point strongly tarentin in
the past, `K^-(p) = I^-(p)`. -/
theorem Kminus_eq_Iminus_of_mem_Zminus [FirstCountableTopology M] (hP : C.CausallyPlain)
    (hp : p ∈ C.Zminus) : C.Kminus ⊤ {p} = C.Iminus ⊤ {p} := by
  -- every increasing sequence converging to `p` computes `K^-(p)`
  have hK : ∀ u : ℕ → M, (∀ n, C.lt ⊤ (u n) p) → Tendsto u atTop (𝓝 p) →
      C.Kminus ⊤ {p} =
        ⋃ N : ℕ, interiorWithin (C.Jminus ⊤ {p}) (⋂ n ≥ N, C.Jminus ⊤ {u n}) := by
    intro u hup hu
    refine Kminus_eq_of_tendsto hu fun n => ?_
    exact Iplus_subset_interior_Jplus (by simpa using hup n)
  refine Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨q, hq⟩ := Iminus_nonempty_of_mem_Zminus hp
    have hqp : C.lt ⊤ q p := by simpa using hq
    obtain ⟨u, -, -, hup, hu⟩ := exists_seq_lt_tendsto_of_mem_Zminus hp hqp
    rw [hK u hup hu] at hx
    obtain ⟨N, hN⟩ := mem_iUnion.1 hx
    have hxN : x ∈ ⋂ n ≥ N, C.Jminus ⊤ {u n} := interiorWithin_subset hN
    simp only [mem_iInter] at hxN
    have hxu : C.le ⊤ x (u N) := by simpa using hxN N le_rfl
    rw [← Jminus_Iminus_eq_of_mem_Zminus hP hp]
    exact ⟨u N, by simpa using hup N, hxu⟩
  · intro q hq
    have hqp : C.lt ⊤ q p := by simpa using hq
    obtain ⟨u, hu0, hmono, hup, hu⟩ := exists_seq_lt_tendsto_of_mem_Zminus hp hqp
    rw [hK u hup hu]
    refine mem_iUnion.2 ⟨1, mem_interiorWithin_of_mem_nhds ?_ ?_⟩
    · simpa using C.le_of_lt hqp
    · -- `I^-(u 1)` is an open neighbourhood of `q` contained in `⋂_{n ≥ 1} J^-(u n)`
      have hq1 : C.lt ⊤ q (u 1) := by
        have := hmono 0
        rwa [hu0] at this
      have hmem : q ∈ C.Iminus ⊤ {u 1} := by simpa using hq1
      refine mem_of_superset (isOpen_Iminus.mem_nhds hmem) ?_
      intro z hz
      have hz1 : C.lt ⊤ z (u 1) := by simpa using hz
      simp only [mem_iInter]
      intro n hn
      simpa using C.le_trans (C.le_of_lt hz1) (le_of_forall_lt_succ hmono hn)

/-- **`rem:comparable_property_obviously_holds`**: `prop:tarentin_fort_K` for `K^+`. -/
theorem Kplus_eq_Iplus_of_mem_Zplus [FirstCountableTopology M] (hP : C.CausallyPlain)
    (hp : p ∈ C.Zplus) : C.Kplus ⊤ {p} = C.Iplus ⊤ {p} :=
  Kminus_eq_Iminus_of_mem_Zminus (C := C.dual) (dual_causallyPlain.2 hP) hp

/-! ### `prop:K_plongement_ordre` -/

/-- `prop:K_plongement_ordre`, the implication for `K^-`, at a pair of points. -/
theorem le_of_Kminus_subset (hJ : IsClosed (C.Jminus ⊤ {y}))
    (hK : C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (h : C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) : C.le ⊤ x y := by
  have hx : x ∈ C.Jminus ⊤ {x} := by simpa using C.le_refl (U := ⊤) (x := x) trivial
  have hxy : x ∈ closure (C.Jminus ⊤ {y}) :=
    closure_mono (h.trans Kminus_subset_Jminus) (hK hx)
  rw [hJ.closure_eq] at hxy
  simpa using hxy

/-- `prop:K_plongement_ordre`, the implication for `K^+`, at a pair of points. -/
theorem le_of_Kplus_subset (hJ : IsClosed (C.Jplus ⊤ {x}))
    (hK : C.Jplus ⊤ {y} ⊆ closure (C.Kplus ⊤ {y}))
    (h : C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) : C.le ⊤ x y :=
  le_of_Kminus_subset (C := C.dual) hJ hK h

/-- **`prop:K_plongement_ordre`.** If the causal pasts and futures of points are closed and
`K^±(x)` is dense in `J^±(x)`, then `K^-(x) ⊂ K^-(y)` implies `x ≤ y` and `K^+(y) ⊂ K^+(x)`
implies `x ≤ y`; if `M` is causal the maps `x ↦ K^±(x)` are injective; and if `K^-` (resp.
`K^+`) is monotone then `x ≤ y ↔ K^-(x) ⊂ K^-(y)` (resp. `↔ K^+(y) ⊂ K^+(x)`). -/
theorem K_order_embedding
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hKp : ∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}))
    (hKm : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) :
    (∀ x y, C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y} → C.le ⊤ x y) ∧
    (∀ x y, C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x} → C.le ⊤ x y) ∧
    (C.IsCausal → Function.Injective (fun x => C.Kminus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kplus ⊤ {x})) ∧
    ((∀ q p, C.le ⊤ q p → C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p}) →
      ∀ x y, C.le ⊤ x y ↔ C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) ∧
    ((∀ q p, C.le ⊤ q p → C.Kplus ⊤ {p} ⊆ C.Kplus ⊤ {q}) →
      ∀ x y, C.le ⊤ x y ↔ C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) := by
  have hm : ∀ x y, C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y} → C.le ⊤ x y :=
    fun x y h => le_of_Kminus_subset (hJm y) (hKm x) h
  have hpl : ∀ x y, C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x} → C.le ⊤ x y :=
    fun x y h => le_of_Kplus_subset (hJp x) (hKp y) h
  refine ⟨hm, hpl, fun hc => ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩, fun hmono x y => ?_,
    fun hmono x y => ?_⟩
  · have hxy' : C.Kminus ⊤ {x} = C.Kminus ⊤ {y} := hxy
    exact hc (hm x y hxy'.subset) (hm y x hxy'.symm.subset)
  · have hxy' : C.Kplus ⊤ {x} = C.Kplus ⊤ {y} := hxy
    exact hc (hpl x y hxy'.symm.subset) (hpl y x hxy'.subset)
  · exact ⟨hmono x y, hm x y⟩
  · exact ⟨hmono x y, hpl x y⟩

end Causality

end Causal
