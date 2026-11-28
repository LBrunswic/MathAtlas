import Benzecri.Chapter3.DualiteSn
import Benzecri.Chapter2.Hilbert

/-!
# `Benzecri.Chapter3.DualiteInterieur` — duality and interiors on `S(n)` (Ch. 3 § 3, Prop. 9, its Corollary, Prop. 10)

J.-P. Benzécri, Bull. SMF 88 (1960), Chapter 3 § 3 « Dualité des corps convexes », journal
pp. 271–272; transcription `papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY
THE AUTHOR, OQ-160). Target T-bz-c3-dualite-interieur. On `S(n)` the form is the dot product
`Benzecri.Sphere.dotPairing n` (strict `Chapter3/Dualite`), which meets (a)–(d) as a Lean term
(`hypD_dotPairing`), with `D′ = D` (`D'_dotPairing`) and `D ∘ D = id` on `C(S(n))`
(`dotPairing_prop1`): nothing here waits on OQ-160's reading of « mis en dualité ».

* **`bzprop:c3s3p9_hemisphere_dual`** — `benzecri1960_ch3.tex:801` (Prop. 9):
  `Benzecri.Sphere.prop9`, for every `A ∈ C(S(n))` and every point `M` (so every closed hemisphere
  `H = D({M})`, `dotPairing_D_point`); `Benzecri.Sphere.prop9_of_isClosed` drops convexity. The
  key lemma is `mem_interior_D_iff` (`X ∈ int D(A)` iff `⟨a, x⟩ > 0` on `F(A)`, `A` closed), and
  `mem_interior_D_singleton` (`int D({M})` is the open hemisphere `⟨m, ·⟩ > 0`).
* **`bzcor:c3s3p9c_corps_convexe_hemisphere`** — `benzecri1960_ch3.tex:825` (Corollary):
  `Benzecri.Sphere.corollaire_hemisphere_ouvert`, a wrapper of the strict `IsCorpsConvexeS.exists_forall_pos`
  (Chapter 2, `Hilbert`), with the hemisphere an open hemisphere of Déf. 5 (`IsOpenHemisphere`,
  nonempty); `Benzecri.Sphere.corollaire_hemisphere_prop9` gives it by the paper's route (Prop. 8, then Prop. 9),
  with the hemisphere `int D({M})` for any `M ∈ int D(A)`.
* **`bzprop:c3s3p10_interieur_dual`** — `benzecri1960_ch3.tex:831` (Prop. 10):
  `Benzecri.Sphere.prop10`; the direct implication holds for `A` closed and `B` arbitrary
  (`prop10_forward`).
* Instances (the dispatch's « closed spherical cap of radius π/4 about M »): on `S(1)`,
  `capQuart = D({s(1,1), s(1,−1)})`, the rays `s(v)` with `|v₁| ≤ v₀` (`mk_mem_capQuart`), the cap
  of angular radius `π/4` about `capCentre = s(1, 0)`: it lies in `C(S(1))` (`capQuart_mem_CS`) and in the
  open hemisphere `int D({capCentre})` (`capQuart_subset`), so Prop. 9 gives `capCentre ∈ int D(capQuart)`
  (`prop9_capQuart`) and Prop. 10, with `B = D({capCentre})`, gives `D(D{capCentre}) ⊆ int D(capQuart)`
  (`prop10_capQuart`).

> **Proposition 9.** Soit $A\in C(S(n))$ un convexe fermé de $S(n)$, $H=D(\{M\})$ un hémisphère
> fermé de $S(n)$, les deux propriétés suivantes sont équivalentes :
> 1° $A\subset\mathring{H}$; 2° $M\in\intr{DA}$.
>
> **Corollaire.** Si $A$ est un corps convexe de $S(n)$, on peut trouver un hémisphère ouvert de
> $S(n)$ contenant $A$.
>
> **Proposition 10.** Soient $A$, $B$ des convexes fermés : $A$, $B\in C(S(n))$.
> $A\subset\mathring{B}$ entraîne $D(B)\subset\intr{D(A)}$ et réciproquement.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `S(n)`, `D` for `⟨M, N⟩ = Σ mᵢnᵢ` | ✓ carried: `D (dotPairing n)` on `S n` |
| Prop. 9: `A ∈ C(S(n))` | ✓ carried (`prop9`); ⚠ weakened in `prop9_of_isClosed` (`A` closed, not necessarily convex) |
| Prop. 9: `H = D({M})` a closed hemisphere | ✓ every point `M` (each `D({M})` is a closed hemisphere, `dotPairing_D_point`, and each closed hemisphere is one, `D_isClosedHemisphere` with `D ∘ D = id`) |
| Corollary: `A` a convex body (Déf. 11, `IsCorpsConvexeS`) | ✓ carried |
| Corollary: « hémisphère ouvert » | Déf. 5 (`IsOpenHemisphere`), nonempty (DEC-114) |
| Prop. 10: `A, B ∈ C(S(n))` | ✓ carried (`prop10`); ⚠ weakened for the direct implication (`prop10_forward`: `A` closed, `B` any part) |
| `Å`, `int` | Mathlib's `interior` in the topology of `S(n)` (the quotient topology of `ℝⁿ⁺¹ − {O}`) |

## SCOPE (disclosed)

* **The printed proof of Prop. 10 is not followed.** It writes
  `int D(A) = ⋂_{M ∈ A} int D({M})`, an interchange of interior and an infinite intersection that
  holds here only because `A` is compact (OQ-160 (a), NOTES.md), and then asks for
  `D(B) ⊂ D({M})` where its display needs `D(B) ⊂ int D({M})` (`[sic?]`, p. 272). The Lean proof
  goes through `mem_interior_D_iff`, whose `←` direction is exactly that interchange, proved by
  the tube lemma on the compact `A` (`IsCompact.eventually_forall_of_forall_eventually`), and through
  `dotPairing_pos_of_mem_interior` (a point of `int F(B)` pairs strictly positively with every nonzero
  `y ∈ F(D B) `). The converse is the paper's: `D ∘ D = id` on `C(S(n))` exchanges the two sides.
* The printed proof of Prop. 9 identifies `S(n)` with the round sphere and its geodesic balls; the
  Lean proof does not use the metric (only the compactness of `A` and the open cone
  `F(int X) = int F(X)`, strict `F_interior`). Its `[sic]` « D(B) ⊂ A » is read « D(B) ⊂ D(A) » as
  the transcription's comment says; it is not used.
* No proof of the Corollary is printed; the anchor is the strict Chapter 2 theorem.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology Filter

namespace Benzecri

namespace Sphere

variable {n : ℕ}

/-! ### Two lemmas on the dot product -/

theorem dotPairing_self_pos {a : Fin (n + 1) → ℝ} (ha : a ≠ 0) : 0 < dotPairing n a a := by
  rw [dotPairing_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

/-- A point `c` of the interior of `C` pairs strictly positively with every nonzero `y` that is
nonnegative on `C`. -/
theorem dotPairing_pos_of_mem_interior {C : Set (Fin (n + 1) → ℝ)} {c y : Fin (n + 1) → ℝ}
    (hc : c ∈ interior C) (hy : y ≠ 0) (h : ∀ m ∈ C, 0 ≤ dotPairing n y m) :
    0 < dotPairing n y c := by
  have hpos := dotPairing_self_pos hy
  have hcont : Continuous fun t : ℝ => c - t • y :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c - t • y ∈ C := by
    have : Tendsto (fun t : ℝ => c - t • y) (𝓝 0) (𝓝 c) := by simpa using hcont.tendsto 0
    exact (this.mono_left nhdsWithin_le_nhds).eventually (mem_interior_iff_mem_nhds.1 hc)
  obtain ⟨t, htC, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have h1 := h _ htC
  rw [map_sub, map_smul, smul_eq_mul] at h1
  have ht' : (0 : ℝ) < t := ht
  nlinarith [mul_pos ht' hpos]

/-! ### The interior of `D(A)` for `A` closed -/

/-- **The key lemma**: for `A` closed in `S(n)`, `s(x) ∈ int D(A)` iff `⟨a, x⟩ > 0` for every
`a ∈ F(A)`. The `←` direction is the interchange `int ⋂_{M ∈ A} D({M}) = ⋂_{M ∈ A} int D({M})` of
the printed proof of Prop. 10, valid because `A` is compact. -/
theorem mem_interior_D_iff {A : Set (S n)} (hA : IsClosed A) {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    mk x hx ∈ interior (D (dotPairing n) A) ↔ ∀ a ∈ F A, 0 < dotPairing n a x := by
  constructor
  · intro hX a ha
    have hxF : x ∈ interior (F (D (dotPairing n) A)) := by
      rw [← F_interior]; exact (mk_mem_iff_mem_F hx).1 hX
    have hxC : x ∈ interior (dualCone (dotPairing n) (F A)) := by
      refine interior_mono ?_ hxF
      rw [F_D]; exact sdiff_subset
    exact dotPairing_pos_of_mem_interior hxC ha.1 (fun m hm => hm a ha)
  · intro h
    set u : S n → Fin (n + 1) → ℝ := fun X => (homeomorphUnitSphere X : Fin (n + 1) → ℝ) with hudef
    have hu : Continuous u := continuous_subtype_val.comp homeomorphUnitSphere.continuous
    have hg : Continuous fun p : (Fin (n + 1) → ℝ) × S n => dotPairing n (u p.2) p.1 := by
      simp only [dotPairing_apply]
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (hu.comp continuous_snd)).mul
          ((continuous_apply i).comp continuous_fst)
    have hu_mk : ∀ (v : Fin (n + 1) → ℝ) (hv : v ≠ 0), u (mk v hv) = ‖v‖⁻¹ • v :=
      fun v hv => homeomorphUnitSphere_mk v hv
    have hev : ∀ᶠ w in 𝓝 x, ∀ X ∈ A, 0 < dotPairing n (u X) w := by
      apply hA.isCompact.eventually_forall_of_forall_eventually
      intro X hX
      induction X using ind with
      | h v hv =>
        have h0 : 0 < dotPairing n (u (mk v hv)) x := by
          rw [hu_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]
          exact mul_pos (inv_pos.2 (norm_pos_iff.2 hv)) (h v ⟨hv, hX⟩)
        exact hg.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h0)
    have hne : ∀ᶠ w in 𝓝 x, w ≠ 0 := isOpen_compl_singleton.mem_nhds hx
    have hsub : ∀ᶠ w in 𝓝 x, w ∈ F (D (dotPairing n) A) := by
      filter_upwards [hev, hne] with w hw hw0
      refine ⟨hw0, ?_⟩
      rw [mk_mem_D]
      intro m hm
      have h1 := hw _ hm.2
      rw [hu_mk, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
      have hm0 : 0 < ‖m‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hm.1)
      exact (pos_of_mul_pos_right h1 hm0.le).le
    have hxi : x ∈ interior (F (D (dotPairing n) A)) := mem_interior_iff_mem_nhds.2 hsub
    rw [← F_interior] at hxi
    exact (mk_mem_iff_mem_F hx).2 hxi

/-- The interior of the closed hemisphere `D({M})` is the open hemisphere `⟨m, ·⟩ > 0`. -/
theorem mem_interior_D_singleton {m : Fin (n + 1) → ℝ} (hm : m ≠ 0) {x : Fin (n + 1) → ℝ}
    (hx : x ≠ 0) :
    mk x hx ∈ interior (D (dotPairing n) {mk m hm}) ↔ 0 < dotPairing n m x := by
  rw [mem_interior_D_iff (isClosed_singleton (x := mk m hm)) hx]
  constructor
  · intro h
    exact h m ⟨hm, rfl⟩
  · intro h a ha
    obtain ⟨ha0, haM⟩ := ha
    obtain ⟨c, hc, hcm⟩ := (mk_eq_mk_iff_exists_pos ha0 hm).1 (mem_singleton_iff.1 haM)
    rw [← hcm, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact pos_of_mul_pos_right h hc.le

theorem interior_D_singleton {m : Fin (n + 1) → ℝ} (hm : m ≠ 0) :
    interior (D (dotPairing n) {mk m hm}) = openHemisphere (dotPairing n m) := by
  ext X
  induction X using ind with
  | h x hx => rw [mem_interior_D_singleton, mk_mem_openHemisphere]

/-! ### Prop. 9 -/

/-- **Prop. 9** for every closed `A` (convexity is not used). -/
theorem prop9_of_isClosed {A : Set (S n)} (hA : IsClosed A) (M : S n) :
    A ⊆ interior (D (dotPairing n) {M}) ↔ M ∈ interior (D (dotPairing n) A) := by
  induction M using ind with
  | h m hm =>
    rw [mem_interior_D_iff hA hm]
    constructor
    · intro h a ha
      have h1 := (mem_interior_D_singleton hm ha.1).1 (h ha.2)
      rwa [dotPairing_swap]
    · intro h X hX
      induction X using ind with
      | h x hx =>
        rw [mem_interior_D_singleton, dotPairing_swap]
        exact h x ⟨hx, hX⟩

/-- **Prop. 9** (`bzprop:c3s3p9_hemisphere_dual`): for `A ∈ C(S(n))` and the closed hemisphere
`H = D({M})`, `A ⊂ int H` iff `M ∈ int D(A)`. -/
theorem prop9 {A : Set (S n)} (hA : A ∈ CS (Fin (n + 1) → ℝ)) (M : S n) :
    A ⊆ interior (D (dotPairing n) {M}) ↔ M ∈ interior (D (dotPairing n) A) :=
  prop9_of_isClosed hA.2 M

/-! ### The Corollary -/

/-- **Corollary** (`bzcor:c3s3p9c_corps_convexe_hemisphere`): a convex body of `S(n)` lies in a
(nonempty) open hemisphere of Déf. 5. A wrapper of `IsCorpsConvexeS.exists_forall_pos`. -/
theorem corollaire_hemisphere_ouvert {A : Set (S n)} (hA : IsCorpsConvexeS n A) :
    ∃ H : Set (S n), IsOpenHemisphere H ∧ H.Nonempty ∧ A ⊆ H := by
  obtain ⟨ℓ, hℓ⟩ := hA.exists_forall_pos
  have hsub : A ⊆ openHemisphere (ℓ : Module.Dual ℝ (Fin (n + 1) → ℝ)) := by
    intro X hX
    induction X using ind with
    | h v hv =>
      rw [mk_mem_openHemisphere]
      exact hℓ v ⟨hv, hX⟩
  refine ⟨openHemisphere (ℓ : Module.Dual ℝ (Fin (n + 1) → ℝ)),
    ⟨isOpen_openHemisphere ℓ, _, F_openHemisphere _⟩, ?_, hsub⟩
  obtain ⟨X, hX⟩ := hA.2.2
  exact ⟨X, hsub (interior_subset hX)⟩

/-- **Corollary by the paper's route**: `D(A)` is a convex body (Prop. 8), so it has an interior
point `M`, and Prop. 9 puts `A` in the open hemisphere `int D({M})`. -/
theorem corollaire_hemisphere_prop9 {A : Set (S n)} (hA : IsCorpsConvexeS n A) :
    ∃ M : S n, M ∈ interior (D (dotPairing n) A) ∧ A ⊆ interior (D (dotPairing n) {M}) ∧
      IsOpenHemisphere (interior (D (dotPairing n) {M})) := by
  obtain ⟨M, hM⟩ := (isCorpsConvexeS_D hA).2.2
  refine ⟨M, hM, (prop9 ⟨hA.1.1, hA.2.1.isClosed⟩ M).2 hM, ?_⟩
  induction M using ind with
  | h m hm =>
    exact ⟨isOpen_interior, dotPairing n m, by rw [interior_D_singleton, F_openHemisphere]⟩

/-! ### Prop. 10 -/

/-- **Prop. 10, the direct implication**, for `A` closed and `B` any part. -/
theorem prop10_forward {A B : Set (S n)} (hA : IsClosed A) (h : A ⊆ interior B) :
    D (dotPairing n) B ⊆ interior (D (dotPairing n) A) := by
  intro Y hY
  induction Y using ind with
  | h y hy =>
    rw [mem_interior_D_iff hA hy]
    intro a ha
    have haB : a ∈ interior (F B) := by
      rw [← F_interior]; exact ⟨ha.1, h ha.2⟩
    rw [mk_mem_D] at hY
    rw [dotPairing_swap]
    exact dotPairing_pos_of_mem_interior haB hy (fun m hm => by rw [dotPairing_swap]; exact hY m hm)

/-- **Prop. 10** (`bzprop:c3s3p10_interieur_dual`): for `A, B ∈ C(S(n))`,
`A ⊂ int B ⟺ D(B) ⊂ int D(A)`. -/
theorem prop10 {A B : Set (S n)} (hA : A ∈ CS (Fin (n + 1) → ℝ)) (hB : B ∈ CS (Fin (n + 1) → ℝ)) :
    A ⊆ interior B ↔ D (dotPairing n) B ⊆ interior (D (dotPairing n) A) := by
  refine ⟨prop10_forward hA.2, fun h => ?_⟩
  have hDB : IsClosed (D (dotPairing n) B) :=
    isClosed_D _ (fun m => (dotPairing n m).continuous_of_finiteDimensional) _
  have h1 := prop10_forward hDB h
  rwa [(dotPairing_prop1 n).2 A hA, (dotPairing_prop1 n).2 B hB] at h1

/-! ### Instances: the cap of radius `π/4` on `S(1)` -/

/-- The point `capCentre = s(1, 0)` of `S(1)`. -/
def capCentre : S 1 := mk ![1, 0] (by intro h; have := congrFun h 0; simp at this)

/-- The cap of angular radius `π/4` about `capCentre`: `D({s(1,1), s(1,−1)})`. -/
def capQuart : Set (S 1) :=
  D (dotPairing 1) {mk ![1, 1] (by intro h; have := congrFun h 0; simp at this),
    mk ![1, -1] (by intro h; have := congrFun h 0; simp at this)}

theorem mk_mem_capQuart {v : Fin (1 + 1) → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ capQuart ↔ |v 1| ≤ v 0 := by
  rw [capQuart, mk_mem_D]
  constructor
  · intro h
    have h1 := h ![1, 1] ⟨by intro h; have := congrFun h 0; simp at this, Or.inl rfl⟩
    have h2 := h ![1, -1] ⟨by intro h; have := congrFun h 0; simp at this, Or.inr rfl⟩
    simp [dotPairing_apply, Fin.sum_univ_two] at h1 h2
    rw [abs_le]; constructor <;> linarith
  · intro hv m hm
    obtain ⟨hm0, hmem⟩ := hm
    rw [abs_le] at hv
    rcases hmem with h | h
    · obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos _ hm0).1 h.symm
      simp [dotPairing_apply, Fin.sum_univ_two]
      nlinarith
    · obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos _ hm0).1 h.symm
      simp [dotPairing_apply, Fin.sum_univ_two]
      nlinarith

theorem capQuart_mem_CS : capQuart ∈ CS (Fin (1 + 1) → ℝ) :=
  ⟨claim_a_convexPart _ _,
    isClosed_D _ (fun m => (dotPairing 1 m).continuous_of_finiteDimensional) _⟩

theorem capQuart_subset : capQuart ⊆ interior (D (dotPairing 1) {capCentre}) := by
  intro X hX
  induction X using ind with
  | h v hv =>
    rw [mk_mem_capQuart] at hX
    rw [capCentre, mem_interior_D_singleton]
    simp only [dotPairing_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
    by_contra hneg
    push Not at hneg
    have h0 : v 0 = 0 := le_antisymm hneg ((abs_nonneg _).trans hX)
    have h1 : v 1 = 0 := abs_nonpos_iff.1 (h0 ▸ hX)
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1

theorem prop9_capQuart : capCentre ∈ interior (D (dotPairing 1) capQuart) :=
  (prop9 capQuart_mem_CS capCentre).1 capQuart_subset

theorem prop10_capQuart :
    D (dotPairing 1) (D (dotPairing 1) {capCentre}) ⊆ interior (D (dotPairing 1) capQuart) :=
  (prop10 capQuart_mem_CS ⟨claim_a_convexPart _ _,
    isClosed_D _ (fun m => (dotPairing 1 m).continuous_of_finiteDimensional) _⟩).1 capQuart_subset

end Sphere

end Benzecri
