import Causal.Properties
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Galileo's spacetime is not strongly causal

`rem:galileo_spacetime_not_strongly` — `ETT.tex:670`.

> Galileo's spacetime is not strongly causal: if a causally convex open set contains two
> points with distinct times $t_0<t_1$ --- and every non-empty open set does --- then it contains the
> whole slab $\{t_0<t<t_1\}$, so no point has a basis of causally convex neighbourhoods. The flat
> model spacetimes of Section \ref{subsec:sing_spacetime_defi} are, by contrast, strongly causal.

Galileo's spacetime is item 4 of `ex:causalities_lines` (`ETT.tex:265`):

> Galileo's spacetime $(\RR^{n+1},\leq,\ll)$, where for every open $\U$,
> $$(t,x_1,\cdots,x_n)\ll_{\U}  (t',x_1',\cdots,x_n')$$ if $t<t'$ and both points lie in the same
> connected component of $\U$; and $p\leq_\U q$ if $p\ll_\U q$ or $p=q$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Galileo's spacetime `ℝ^{n+1}`, `n` unrestricted | **⚠ strengthened: `n ≥ 1`** — for `n = 0` the statement is false (`galileo_zero_stronglyCausal`) |
| — `ℝ^{n+1}` | ✓ carried as `ℝ × (Fin n → ℝ)`, homeomorphic to it; the general construction `galileoOn X` is over `ℝ × X` |
| "a causally convex open set" | ⚠ weakened: any causally convex set (`CausallyConvexIn V ⊤`), open or not |
| — `M` connected (used: the slab is the full diamond) | ✓ carried: `ConnectedSpace (ℝ × X)` in the general form |

## SCOPE (disclosed)

* **The remark is certified for `n ≥ 1` only, and is false for `n = 0`.** Galileo's spacetime of
  dimension `1` is the timelike line (`ℝ`, `p ≪_U q` iff `p < q` in the same component of `U`),
  and it is strongly causal (`galileo_zero_stronglyCausal`); the argument of the remark needs a
  spatial direction for the slab to escape every small neighbourhood. `ex:causalities_lines`
  writes `ℝ^{n+1}` without bounding `n` (Minkowski space, item 5, has `n ≥ 1`). The label is
  therefore written without its mark.
* The paper's relation `p ≤_U q iff p ≪_U q or p = q` is carried with `p ∈ U` in the second
  case: the relations of a causality on `U` hold between points of `U` only.
* The last sentence ("the flat model spacetimes … are, by contrast, strongly causal") is about the
  model spaces of `subsec:sing_spacetime_defi`, which the library does not have; it is not stated.
* Proved besides: Galileo's spacetime is a causality (`galileoOn`), it is causal
  (`galileoOn_isCausal`, so the converse of `rem:topological_spacetime_strongly_causal` fails),
  the full diamond between points of distinct times is the slab plus its two vertices
  (`galileoOn_diamond_top`), the slab lemma (`galileoOn_slab_subset`), and the stronger
  "no point has a basis of causally convex neighbourhoods" (`galileoOn_not_convex_basis`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### The construction -/

/-- The chronological relation of Galileo's spacetime over `ℝ × X`: later time, same connected
component of `U`. -/
def galileoLt (U : Opens (ℝ × X)) (p q : ℝ × X) : Prop :=
  p ∈ U ∧ p.1 < q.1 ∧ q ∈ connectedComponentIn (U : Set (ℝ × X)) p

theorem galileoLt.mem_right {U : Opens (ℝ × X)} {p q : ℝ × X} (h : galileoLt U p q) : q ∈ U :=
  connectedComponentIn_subset _ _ h.2.2

theorem galileoLt.trans {U : Opens (ℝ × X)} {p q r : ℝ × X} (h₁ : galileoLt U p q)
    (h₂ : galileoLt U q r) : galileoLt U p r := by
  refine ⟨h₁.1, h₁.2.1.trans h₂.2.1, ?_⟩
  rw [connectedComponentIn_eq h₁.2.2]
  exact h₂.2.2

theorem galileoLt.mono {U V : Opens (ℝ × X)} (hVU : V ≤ U) {p q : ℝ × X} (h : galileoLt V p q) :
    galileoLt U p q :=
  ⟨hVU h.1, h.2.1, connectedComponentIn_mono p hVU h.2.2⟩

/-- `q` is in the component of `p` iff `p` is in the component of `q`. -/
theorem mem_connectedComponentIn_comm {F : Set (ℝ × X)} {p q : ℝ × X} (hp : p ∈ F) :
    q ∈ connectedComponentIn F p ↔ q ∈ F ∧ p ∈ connectedComponentIn F q := by
  constructor
  · intro h
    refine ⟨connectedComponentIn_subset _ _ h, ?_⟩
    rw [← connectedComponentIn_eq h]
    exact mem_connectedComponentIn hp
  · rintro ⟨hq, h⟩
    rw [← connectedComponentIn_eq h]
    exact mem_connectedComponentIn hq

variable [LocallyConnectedSpace (ℝ × X)]

theorem isOpen_galileoLt_right (U : Opens (ℝ × X)) (p : ℝ × X) :
    IsOpen {q | galileoLt U p q} := by
  by_cases hp : p ∈ U
  · have : {q | galileoLt U p q} =
        {q : ℝ × X | p.1 < q.1} ∩ connectedComponentIn (U : Set (ℝ × X)) p := by
      ext q; simp [galileoLt, hp]
    rw [this]
    exact (isOpen_lt continuous_const continuous_fst).inter U.isOpen.connectedComponentIn
  · have : {q | galileoLt U p q} = ∅ := by
      ext q; simp [galileoLt, hp]
    rw [this]; exact isOpen_empty

theorem isOpen_galileoLt_left (U : Opens (ℝ × X)) (q : ℝ × X) :
    IsOpen {p | galileoLt U p q} := by
  by_cases hq : q ∈ U
  · have : {p | galileoLt U p q} =
        {p : ℝ × X | p.1 < q.1} ∩ connectedComponentIn (U : Set (ℝ × X)) q := by
      ext p
      simp only [galileoLt, mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro ⟨hp, hpq, h⟩
        exact ⟨hpq, ((mem_connectedComponentIn_comm hp).1 h).2⟩
      · rintro ⟨hpq, h⟩
        have hp : p ∈ (U : Set (ℝ × X)) := connectedComponentIn_subset _ _ h
        exact ⟨hp, hpq, (mem_connectedComponentIn_comm hp).2 ⟨hq, h⟩⟩
    rw [this]
    exact (isOpen_lt continuous_fst continuous_const).inter U.isOpen.connectedComponentIn
  · have : {p | galileoLt U p q} = ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun h => hq h.mem_right
    rw [this]; exact isOpen_empty

variable (X) in
/-- `ex:causalities_lines`, item 4, over `ℝ × X`: **Galileo's spacetime**. `p ≪_U q` iff
`t < t'` and `q` lies in the connected component of `p` in `U`; `p ≤_U q` iff `p ≪_U q` or
`p = q ∈ U`. -/
def galileoOn : Causality (ℝ × X) where
  le U p q := galileoLt U p q ∨ (p = q ∧ p ∈ U)
  lt := galileoLt
  le_mem_left h := h.elim (fun h => h.1) fun h => h.2
  le_mem_right h := h.elim galileoLt.mem_right fun h => h.1 ▸ h.2
  lt_mem_left h := h.1
  lt_mem_right h := h.mem_right
  le_refl hx := Or.inr ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · rcases h₂ with h₂ | ⟨rfl, -⟩
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inl h₁
    · exact h₂
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono hVU _ _ h := h.elim (fun h => Or.inl (h.mono hVU)) fun h => Or.inr ⟨h.1, hVU h.2⟩
  lt_mono hVU _ _ h := h.mono hVU
  le_of_lt h := Or.inl h
  isOpen_lt_right := isOpen_galileoLt_right
  isOpen_lt_left := isOpen_galileoLt_left

/-- Galileo's spacetime `ℝ^{n+1}`, carried as `ℝ × (Fin n → ℝ)`. -/
abbrev galileo (n : ℕ) : Causality (ℝ × (Fin n → ℝ)) := galileoOn (Fin n → ℝ)

variable {U : Opens (ℝ × X)} {p q r : ℝ × X}

@[simp] theorem galileoOn_lt : (galileoOn X).lt U p q ↔ galileoLt U p q := Iff.rfl

@[simp] theorem galileoOn_le :
    (galileoOn X).le U p q ↔ galileoLt U p q ∨ (p = q ∧ p ∈ U) := Iff.rfl

/-- A causal relation does not decrease time. -/
theorem galileoOn_le_fst (h : (galileoOn X).le U p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨rfl, -⟩
  · exact h.2.1.le
  · exact le_rfl

/-- Galileo's spacetime is causal: strong causality is strictly stronger than causality. -/
theorem galileoOn_isCausal : (galileoOn X).IsCausal := by
  intro p q hpq hqp
  rcases hpq with hpq | ⟨rfl, -⟩
  · exact absurd (galileoOn_le_fst hqp) (not_le.2 hpq.2.1)
  · rfl

/-! ### The full diamond is a slab -/

/-- On a connected `ℝ × X`, between two points of distinct times the full diamond of `M` is the
open slab together with its two vertices. -/
theorem galileoOn_diamond_top [ConnectedSpace (ℝ × X)] (hpq : p.1 < q.1) :
    (galileoOn X).diamond ⊤ p q = {r | p.1 < r.1 ∧ r.1 < q.1} ∪ {p, q} := by
  have hlt : ∀ a b : ℝ × X, galileoLt ⊤ a b ↔ a.1 < b.1 := fun a b => by
    simp [galileoLt, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  ext r
  rw [Causality.mem_diamond, galileoOn_le, galileoOn_le, hlt, hlt]
  simp only [Opens.mem_top, and_true, mem_union, mem_setOf_eq, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨h₁ | rfl, h₂ | rfl⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
  · rintro (⟨h₁, h₂⟩ | rfl | rfl)
    · exact ⟨Or.inl h₁, Or.inl h₂⟩
    · exact ⟨Or.inr rfl, Or.inl hpq⟩
    · exact ⟨Or.inl hpq, Or.inr rfl⟩

/-- The slab lemma of `rem:galileo_spacetime_not_strongly`: a causally convex set containing two
points of times `t₀ < t₁` contains the whole slab `{t₀ < t < t₁}`. -/
theorem galileoOn_slab_subset [ConnectedSpace (ℝ × X)] {V : Set (ℝ × X)}
    (hV : (galileoOn X).CausallyConvexIn V ⊤) (hp : p ∈ V) (hq : q ∈ V) (hpq : p.1 < q.1) :
    {r : ℝ × X | p.1 < r.1 ∧ r.1 < q.1} ⊆ V := by
  intro r hr
  apply hV.2 p hp q hq
  rw [galileoOn_diamond_top hpq]
  exact Or.inl hr

omit [LocallyConnectedSpace (ℝ × X)] in
/-- "Every non-empty open set" contains two points of distinct times: a neighbourhood of `p`
contains a point before `p` and a point after `p`, at the same position. -/
theorem exists_before_after_of_mem_nhds {V : Set (ℝ × X)} (hV : V ∈ 𝓝 p) :
    ∃ a ∈ V, ∃ b ∈ V, a.1 < p.1 ∧ p.1 < b.1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hV
  obtain ⟨l, h, ⟨hl, hh⟩, hlh⟩ := mem_nhds_iff_exists_Ioo_subset.1 hu
  have hp2 : p.2 ∈ v := mem_of_mem_nhds hv
  refine ⟨((l + p.1) / 2, p.2), huv ⟨hlh ⟨by linarith, by linarith⟩, hp2⟩,
    ((p.1 + h) / 2, p.2), huv ⟨hlh ⟨by linarith, by linarith⟩, hp2⟩, ?_, ?_⟩
  · show (l + p.1) / 2 < p.1; linarith
  · show p.1 < (p.1 + h) / 2; linarith

/-- "No point has a basis of causally convex neighbourhoods", when the spatial factor `X` is
connected and has two points separated by an open set. -/
theorem galileoOn_not_convex_basis [ConnectedSpace (ℝ × X)] [T1Space X] [Nontrivial X]
    (p : ℝ × X) :
    ¬ ∀ N ∈ 𝓝 p, ∃ V ∈ 𝓝 p, V ⊆ N ∧ (galileoOn X).CausallyConvexIn V ⊤ := by
  intro h
  obtain ⟨x₁, hx₁⟩ := exists_ne (p.2 : X)
  -- the neighbourhood `ℝ × (X ∖ {x₁})` of `p`
  have hN : (univ ×ˢ {x₁}ᶜ : Set (ℝ × X)) ∈ 𝓝 p :=
    prod_mem_nhds Filter.univ_mem (isOpen_compl_singleton.mem_nhds hx₁.symm)
  obtain ⟨V, hV, hVN, hconv⟩ := h _ hN
  obtain ⟨a, ha, b, hb, hap, hpb⟩ := exists_before_after_of_mem_nhds hV
  have : ((p.1, x₁) : ℝ × X) ∈ V :=
    galileoOn_slab_subset hconv ha hb (hap.trans hpb) ⟨hap, hpb⟩
  exact (hVN this).2 rfl

/-- **`rem:galileo_spacetime_not_strongly`**, general form: Galileo's spacetime over `ℝ × X`,
`X` connected, `T1` and with two points, is not strongly causal. -/
theorem galileoOn_not_stronglyCausal [ConnectedSpace (ℝ × X)] [T1Space X] [Nontrivial X] :
    ¬ (galileoOn X).StronglyCausal := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact galileoOn_not_convex_basis ((0 : ℝ), x) fun N hN => h _ N hN

/-- `rem:galileo_spacetime_not_strongly`: Galileo's spacetime `ℝ^{n+1}`, `n ≥ 1`, is not
strongly causal. -/
theorem galileo_not_stronglyCausal (n : ℕ) (hn : 1 ≤ n) : ¬ (galileo n).StronglyCausal := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact galileoOn_not_stronglyCausal (X := Fin (m + 1) → ℝ)

/-- The remark fails for `n = 0`: if the spatial factor is a point, Galileo's spacetime is
strongly causal. -/
theorem galileoOn_stronglyCausal_of_subsingleton [Subsingleton X] :
    (galileoOn X).StronglyCausal := by
  intro p N hN
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
  obtain ⟨l, h, ⟨hl, hh⟩, hlh⟩ := mem_nhds_iff_exists_Ioo_subset.1 hu
  have hvuniv : v = univ := by
    refine eq_univ_of_forall fun x => ?_
    rw [Subsingleton.elim x p.2]
    exact mem_of_mem_nhds hv
  refine ⟨Ioo l h ×ˢ univ, prod_mem_nhds (Ioo_mem_nhds hl hh) Filter.univ_mem, ?_, ?_⟩
  · rintro r ⟨hr1, -⟩
    exact huv ⟨hlh hr1, hvuniv ▸ trivial⟩
  · refine ⟨subset_univ _, fun a ha b hb r hr => ?_⟩
    rw [Causality.mem_diamond] at hr
    exact ⟨⟨ha.1.1.trans_le (galileoOn_le_fst hr.1),
      (galileoOn_le_fst hr.2).trans_lt hb.1.2⟩, trivial⟩

/-- For `n = 0` Galileo's spacetime `ℝ^1` is strongly causal: `rem:galileo_spacetime_not_strongly`
needs `n ≥ 1`. -/
theorem galileo_zero_stronglyCausal : (galileo 0).StronglyCausal :=
  galileoOn_stronglyCausal_of_subsingleton (X := Fin 0 → ℝ)

end Causal
