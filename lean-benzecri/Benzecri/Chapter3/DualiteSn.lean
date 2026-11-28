import Benzecri.Chapter3.Dualite
import Benzecri.Chapter3.FacettesSphere

/-!
# `Benzecri.Chapter3.DualiteSn` — the duality `D` on `S(n)`: dimensions, noyau and support, convex bodies, the transposition `Δ` (Ch. 3 § 3, Props. 6–8 and the Remark)

J.-P. Benzécri, Bull. SMF 88 (1960), Chapter 3 § 3 « Dualité des corps convexes », journal
pp. 270–272; transcription `papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY
THE AUTHOR, OQ-160). Target T-bz-c3-dualite-sn. On `S(n)` the form is the dot product
`Benzecri.Sphere.dotPairing n` (strict `Chapter3/Dualite`), which meets (a)–(d) as a Lean term, so
nothing here waits on OQ-160's reading of « mis en dualité »; `D′ = D` there (`D'_dotPairing`).

* **`bzprop:c3s3p6_dual_sous_variete`** — `benzecri1960_ch3.tex:757` (Prop. 6):
  `Benzecri.Sphere.prop6`. Dimensions are integers, `dimS A = dim span F(A) − 1`, so that `∅` has
  dimension `−1` (`dimS_empty`) and `s(L − {O})` has dimension `dim L − 1`
  (`dimS_linearSubvariety`), between `−1` and `n` (`dimS_mem_Icc`); `dim L + dim L^⊥ = n + 1`
  (`finrank_add_finrank_orth`).
* **`bzprop:c3s3p7_noyau_support`** — `benzecri1960_ch3.tex:768` (Prop. 7):
  `Benzecri.Sphere.prop7`, with `D` of the noyau *equal* to the support of `D(W)` and conversely
  (`D_noyau`, `D_supportK`), `σ(W) + ν(D W) = n − 1` (`sigma_add_nu_D`) and
  `ν(W) + σ(D W) = n − 1` (`nu_add_sigma_D`); `σ` = `sigma`, `ν` = `nu`.
* **`bzprop:c3s3p8_dual_corps_convexe`** — `benzecri1960_ch3.tex:783` (Prop. 8):
  `Benzecri.Sphere.prop8` proves the printed « est un convexe » (`D(K)` a closed convex part) *and*
  the stronger « est un corps convexe » the proof gives (`isCorpsConvexeS_D`, OQ-160 (a)), so
  either ruling marks with no Lean change.
* `bzrem:c3s3r1_transposition` — `benzecri1960_ch3.tex:863` (Remark). Not marked (a reading,
  and a finding): « la transposition » is read as the dual representation `g ↦ ᵗg⁻¹`
  (`dualRep`, `dualRepEquiv`, `dotPairing_dualRep`), which induces `Δ`, an involutive automorphism
  of `GS(n, ℝ)` (`Delta`, `Delta_mk`, `Delta_Delta`), and `Δ(g) W = D(g(D W))` for every
  `W ∈ C(S(n))` (`remark_transposition`, from `D_smul`: `D(h W) = ᵗh⁻¹ D(W)` for every part).
  Read literally, `g ↦ ᵗg` fails the formula (`transpose_literal_differs`). See SCOPE.
* Instances (the dimension conventions): at `W = ∅` and `W = S(n)` (`prop7_empty_univ`:
  `σ(∅) = −1`, `D(∅) = S(n)`, `ν(S(n)) = n`; `σ(S(n)) = n`, `D(S(n)) = ∅`, `ν(∅) = −1`), and at a
  point (`prop7_point`: `σ = 0`, `ν = −1`, `D{x}` a closed hemisphere with `ν = n − 1`, `σ = n`).

> Nous supposerons maintenant que $E=\R^{n+1}$; $S(E)=S(n)$. $\R^{n+1}$ est muni d'un produit
> scalaire qui permet de l'identifier à son dual. […] On pose
> $\langle M, N\rangle=\sum_{i=0}^{n}m_in_i$.
>
> **Proposition 6.** Soit $L$ une sous-variété linéaire de dimension $p$ de $S(n)$
> ($-1\leqq p\leqq n$), $D(L)$ est une sous-variété linéaire de dimension $(n-p-1)$.
>
> **Proposition 7.** Soit $W\in C(S(n))$; désignons par $\nu(W)$ la dimension de son noyau, par
> $\sigma(W)$ la dimension de son support (c'est-à-dire de la plus petite variété linéaire
> contenant $W$). $D$ transforme le noyau (resp. support) de $W$ dans le support (resp. noyau) de
> $D(W)$ et l'on a $\sigma(W)+\nu(D(W))=n-1$, $\nu(W)+\sigma(D(W))=n-1$.
>
> **Proposition 8.** Le dual d'un corps convexe de $S(n)$ est un convexe.
>
> **Remarque.** Puisque $\R^n$ est canoniquement identifié à son dual, la représentation duale de
> $GL(n, \R)$ est un automorphisme de $GL(n, \R)$ : la transposition. Cet automorphisme induit un
> automorphisme de $GS(n-1, \R)$, que nous noterons $\Delta$; $\Delta$ peut s'exprimer au moyen de
> la dualité $D$ des parties convexes fermées de $S(n-1)$. Soit $g\in(GS(n-1, \R)$,
> $\Delta(g)\in GS(n-1, \R)$; $W\in C(S(n-1))$; on a $\Delta(g)\,W=D\circ g\circ DW$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E = ℝⁿ⁺¹` with `⟨M, N⟩ = Σ mᵢnᵢ` | ✓ carried: `Fin (n + 1) → ℝ`, `dotPairing n` (strict `Chapter3/Dualite`) |
| Prop. 6: `L` a linear subvariety of dimension `p`, `−1 ≤ p ≤ n` | ✓ carried: `L = linearSubvariety M`; `p = dimS L` (an integer; the range is `dimS_mem_Icc`) |
| Prop. 6: « dimension » of a linear subvariety | convention: `dim L − 1`, `∅` of dimension `−1` (the proof: « `F(L) ∪ {O}` … de dimension `(p+1)` »), checked at `∅`, `S(n)`, a point |
| Prop. 7: `W ∈ C(S(n))` | ✓ carried for `D(noyau W) = support D(W)` and `ν(W) + σ(D W) = n − 1`; ⚠ weakened for `D(support W) = noyau D(W)` and `σ(W) + ν(D W) = n − 1`, which hold for every part `W` |
| Prop. 7: « support », « la plus petite variété linéaire contenant `W` » | ✓ carried: `supportK W` (strict `Chapter3/FacettesSphere`: `subset_supportK`, `supportK_subset`) |
| Prop. 7: « noyau » (§ 1 Déf. 5) | ✓ carried: `noyau W` (`noyau_eq`, `noyau_eq_linearSubvariety`) |
| Prop. 7: « transforme … dans » | ✓ carried, and more: equalities `D(noyau W) = support D(W)`, `D(support W) = noyau D(W)` |
| Prop. 8: `K` a corps convexe of `S(n)` (Ch. 1 Déf. 11) | ✓ carried: `IsCorpsConvexeS n K` |
| Prop. 8: « est un convexe » | ✓ carried (`IsConvexPart`, and closed), and the stronger « corps convexe » (OQ-160 (a)) |
| Remark: `ℝⁿ`, `GL(n, ℝ)`, `GS(n−1, ℝ)`, `S(n−1)` | ✓ carried with the index shifted: `ℝⁿ⁺¹`, `GLR (n + 1)`, `GSR n`, `S n`, every `n ≥ 0` (the paper's `n ≥ 1`) |
| Remark: « la représentation duale … : la transposition » | reading: `g ↦ ᵗg⁻¹` (`dualRep`); `g ↦ ᵗg` fails the formula (`transpose_literal_differs`) |
| Remark: `W ∈ C(S(n−1))` | ✓ carried (`hW : W ∈ CS _`); `D_smul` holds for every part |

## SCOPE (disclosed)

* **The Remark is not marked.** « la représentation duale de `GL(n, ℝ)` est un automorphisme de
  `GL(n, ℝ)` : la transposition »: the dual (contragredient) representation for the dot product
  is `g ↦ ᵗg⁻¹` (`dotPairing_dualRep`: `⟨g x, ᵗg⁻¹ y⟩ = ⟨x, y⟩`), an automorphism
  (`dualRepEquiv`); the transposition `g ↦ ᵗg` itself reverses products (an anti-automorphism
  of `GL(m, ℝ)` for `m ≥ 2`), and with it the printed formula fails: for `g = diag(2, 1)` and `W = {s(1, 1)}`
  in `S(1)`, `ᵗg W = {s(2, 1)} ≠ {s(1/2, 1)} = D(g(D W))` (`transpose_literal_differs`). Under the
  reading `Δ = ` the map induced by `g ↦ ᵗg⁻¹`, everything printed is proved. The printed wording
  is imprecise, not refuted: the formula holds with the dual representation the sentence names.
* The Remark's printed proof (« équivalente à la définition de Δ, quand W est un point ou un
  hémisphère ») is not followed: the formula is proved for every closed convex `W` from
  `D(h W) = ᵗh⁻¹ D(W)` and `D ∘ D = id` on `C(S(n))` (`dotPairing_prop1`).
* Prop. 7's first equality and second identity need `W` closed: for an open hemisphere `W`,
  `D(W)` is a point and `D(noyau W) = D(∅) = S(n)` is not its support (argued, not formalized;
  the paper assumes `W ∈ C(S(n))`).
* `dimS`, `sigma`, `nu`, `linearSubvariety_bot`, `linearSubvariety_injective`,
  `span_eq_top_iff_affineSpan`, `linearSubvariety_subset_noyau` are general (any `E`) and may move
  upstream at graduation; `orth_orth`, `transp`, `dualRep` are specific to the dot product.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Module
open scoped Pointwise Matrix

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Dimensions of linear subvarieties, `∅` of dimension `−1` -/

/-- The dimension of the support of a part `A` of `S(E)`: `dim span F(A) − 1`, an integer, so that
`∅` has dimension `−1`. On a linear subvariety `s(L − {O})` it is `dim L − 1`
(`dimS_linearSubvariety`). -/
def dimS (A : Set (Sphere E)) : ℤ := (finrank ℝ (Submodule.span ℝ (F A)) : ℤ) - 1

theorem span_F_linearSubvariety (L : Submodule ℝ E) :
    Submodule.span ℝ (F (linearSubvariety L)) = L := by
  rw [F_linearSubvariety, Submodule.span_sdiff_singleton_zero, Submodule.span_eq]

theorem dimS_linearSubvariety (L : Submodule ℝ E) :
    dimS (linearSubvariety L) = (finrank ℝ L : ℤ) - 1 := by
  rw [dimS, span_F_linearSubvariety]

theorem linearSubvariety_injective :
    Function.Injective (linearSubvariety : Submodule ℝ E → Set (Sphere E)) := fun L M h => by
  rw [← span_F_linearSubvariety L, h, span_F_linearSubvariety]

theorem dimS_supportK (A : Set (Sphere E)) : dimS (supportK A) = dimS A := by
  rw [supportK, dimS_linearSubvariety, dimS]

theorem dimS_empty : dimS (∅ : Set (Sphere E)) = -1 := by
  rw [dimS, F_empty, Submodule.span_empty, finrank_bot]
  simp

theorem linearSubvariety_bot : linearSubvariety (⊥ : Submodule ℝ E) = ∅ := by
  apply F_injective
  rw [F_linearSubvariety, F_empty]
  ext v; simp

/-- **`σ(W)`**, the dimension of the support of `W` (« la plus petite variété linéaire contenant
`W` », `supportK`). -/
def sigma (W : Set (Sphere E)) : ℤ := dimS (supportK W)

/-- **`ν(W)`**, the dimension of the noyau of `W` (Déf. 5, `noyau`). -/
def nu (W : Set (Sphere E)) : ℤ := dimS (noyau W)

theorem sigma_eq (W : Set (Sphere E)) : sigma W = dimS W := dimS_supportK W

/-- A linear subvariety contained in a convex part lies in its noyau. -/
theorem linearSubvariety_subset_noyau {k : Set (Sphere E)} (hk : IsConvexPart k)
    {L : Submodule ℝ E} (h : linearSubvariety L ⊆ k) : linearSubvariety L ⊆ noyau k := by
  intro x hx
  rw [noyau_eq hk]
  exact ⟨h hx, h (neg_mem_linearSubvariety hx)⟩

/-- The span of a part containing `O` is everything iff its affine span is. -/
theorem span_eq_top_iff_affineSpan {s : Set E} (h0 : (0 : E) ∈ s) :
    Submodule.span ℝ s = ⊤ ↔ affineSpan ℝ s = ⊤ := by
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E ⟨0, h0⟩,
    vectorSpan_eq_span_vsub_set_right ℝ h0]
  simp

end Sphere

/-! ### `S(n)` with the dot product -/

namespace Sphere

variable {n : ℕ}

theorem dotPairing_swap (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    dotPairing n x y = dotPairing n y x := by
  rw [dotPairing_apply, dotPairing_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dotPairing_injective (n : ℕ) : Function.Injective (dotPairing n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h := LinearMap.congr_fun hv v
  rw [dotPairing_apply, LinearMap.zero_apply] at h
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (v j))).1 h i
    (Finset.mem_univ i)
  simpa using mul_self_eq_zero.1 hi

/-- `dim L + dim L^⊥ = n + 1`. -/
theorem finrank_add_finrank_orth (L : Submodule ℝ (Fin (n + 1) → ℝ)) :
    finrank ℝ L + finrank ℝ (orth (dotPairing n) L) = n + 1 := by
  set e := (dotPairing n).linearEquivOfInjective (dotPairing_injective n) (by simp)
  have h : orth (dotPairing n) L = L.dualAnnihilator.comap (e : _ →ₗ[ℝ] _) := by
    rw [orth, dotPairing_flip]; rfl
  rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, finrank_fin_fun]

theorem orth_orth (L : Submodule ℝ (Fin (n + 1) → ℝ)) :
    orth (dotPairing n) (orth (dotPairing n) L) = L := by
  have hle : L ≤ orth (dotPairing n) (orth (dotPairing n) L) := by
    intro v hv
    rw [mem_orth]
    intro m hm
    rw [dotPairing_swap]
    exact (mem_orth _ _).1 hm v hv
  have h1 := finrank_add_finrank_orth L
  have h2 := finrank_add_finrank_orth (orth (dotPairing n) L)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem D_D_linearSubvariety (L : Submodule ℝ (Fin (n + 1) → ℝ)) :
    D (dotPairing n) (D (dotPairing n) (linearSubvariety L)) = linearSubvariety L := by
  rw [D_linearSubvariety, D_linearSubvariety, orth_orth]

/-- The dimension of a part of `S(n)` lies between `−1` and `n`. -/
theorem dimS_mem_Icc (A : Set (S n)) : dimS A ∈ Icc (-1 : ℤ) n := by
  have h := Submodule.finrank_le (Submodule.span ℝ (F A))
  rw [finrank_fin_fun] at h
  rw [dimS, mem_Icc]
  omega

/-! ### Prop. 6 -/

/-- **Prop. 6** (`bzprop:c3s3p6_dual_sous_variete`): the dual of a linear subvariety `L` of
`S(n)` of dimension `p` (`−1 ≤ p ≤ n`) is a linear subvariety of dimension `n − p − 1`. -/
theorem prop6 (L : Set (S n)) (hL : ∃ M : Submodule ℝ (Fin (n + 1) → ℝ), L = linearSubvariety M) :
    (∃ M' : Submodule ℝ (Fin (n + 1) → ℝ), D (dotPairing n) L = linearSubvariety M') ∧
      dimS (D (dotPairing n) L) = n - dimS L - 1 := by
  obtain ⟨M, rfl⟩ := hL
  refine ⟨⟨_, D_linearSubvariety _ M⟩, ?_⟩
  rw [D_linearSubvariety, dimS_linearSubvariety, dimS_linearSubvariety]
  have h := finrank_add_finrank_orth M
  omega

/-! ### Prop. 7 -/

/-- Prop. 7, « D transforme le support de W dans le noyau de D(W) », for every convex part. -/
theorem D_supportK (W : Set (S n)) : D (dotPairing n) (supportK W) = noyau (D (dotPairing n) W) := by
  have hDW : IsConvexPart (D (dotPairing n) W) := claim_a_convexPart _ W
  apply Subset.antisymm
  · rw [supportK, D_linearSubvariety]
    apply linearSubvariety_subset_noyau hDW
    rw [← D_linearSubvariety]
    exact claim_a_antitone _ (subset_supportK W)
  · rw [noyau_eq_linearSubvariety hDW]
    have hN : linearSubvariety (noyauSub hDW) ⊆ D (dotPairing n) W := by
      rw [← noyau_eq_linearSubvariety hDW]; exact noyau_subset
    have h1 : W ⊆ linearSubvariety (orth (dotPairing n) (noyauSub hDW)) := by
      rw [← D_linearSubvariety]
      have := subset_D'_D (dotPairing n) W
      rw [D'_dotPairing] at this
      exact this.trans (claim_a_antitone _ hN)
    have h3 := claim_a_antitone (dotPairing n) (supportK_subset h1)
    rwa [D_linearSubvariety, orth_orth] at h3

/-- Prop. 7, « D transforme le noyau de W dans le support de D(W) », for `W ∈ C(S(n))`. -/
theorem D_noyau {W : Set (S n)} (hW : W ∈ CS (Fin (n + 1) → ℝ)) :
    D (dotPairing n) (noyau W) = supportK (D (dotPairing n) W) := by
  have hDD : D (dotPairing n) (D (dotPairing n) W) = W := (dotPairing_prop1 n).2 W hW
  have h := D_supportK (D (dotPairing n) W)
  rw [hDD] at h
  rw [← h, supportK, D_D_linearSubvariety]

/-- `σ(W) + ν(D(W)) = n − 1`, for every part `W` of `S(n)`. -/
theorem sigma_add_nu_D (W : Set (S n)) : sigma W + nu (D (dotPairing n) W) = n - 1 := by
  rw [nu, ← D_supportK, (prop6 (supportK W) ⟨_, rfl⟩).2, sigma]
  ring

/-- `ν(W) + σ(D(W)) = n − 1`, for `W ∈ C(S(n))`. -/
theorem nu_add_sigma_D {W : Set (S n)} (hW : W ∈ CS (Fin (n + 1) → ℝ)) :
    nu W + sigma (D (dotPairing n) W) = n - 1 := by
  rw [sigma, ← D_noyau hW, (prop6 (noyau W) ⟨_, noyau_eq_linearSubvariety hW.1⟩).2, nu]
  ring

/-- **Prop. 7** (`bzprop:c3s3p7_noyau_support`). -/
theorem prop7 {W : Set (S n)} (hW : W ∈ CS (Fin (n + 1) → ℝ)) :
    D (dotPairing n) (noyau W) = supportK (D (dotPairing n) W) ∧
      D (dotPairing n) (supportK W) = noyau (D (dotPairing n) W) ∧
      sigma W + nu (D (dotPairing n) W) = n - 1 ∧
      nu W + sigma (D (dotPairing n) W) = n - 1 :=
  ⟨D_noyau hW, D_supportK W, sigma_add_nu_D W, nu_add_sigma_D hW⟩

/-! ### Prop. 8 -/

/-- **Prop. 8, the stronger reading** (OQ-160 (a)): the dual of a convex body of `S(n)` is a
convex body. -/
theorem isCorpsConvexeS_D {K : Set (S n)} (hK : IsCorpsConvexeS n K) :
    IsCorpsConvexeS n (D (dotPairing n) K) := by
  have hKCS : K ∈ CS (Fin (n + 1) → ℝ) := ⟨hK.1.1, hK.2.1.isClosed⟩
  have hspanK : Submodule.span ℝ (F K) = ⊤ := by
    obtain ⟨x, hx⟩ := hK.2.2
    have hU : IsOpen (F (interior K)) := isOpen_iff_F.1 isOpen_interior
    induction x using ind with
    | h v hv =>
    have hvU : v ∈ F (interior K) := (mk_mem_iff_mem_F hv).1 hx
    have hA : affineSpan ℝ (F (interior K)) = ⊤ := hU.affineSpan_eq_top ⟨v, hvU⟩
    have hA' : affineSpan ℝ (insert 0 (F K)) = ⊤ := top_unique
      (hA ▸ affineSpan_mono ℝ ((F_mono interior_subset).trans (subset_insert _ _)))
    rw [← Submodule.span_insert_zero]
    exact (span_eq_top_iff_affineSpan (mem_insert _ _)).2 hA'
  have hσK : sigma K = n := by
    rw [sigma_eq, dimS, hspanK, finrank_top, finrank_fin_fun]; push_cast; ring
  have hνK : nu K = -1 := by
    rw [nu, (isStrictConvexPart_iff_noyau_eq_empty.1 hK.1).2, dimS_empty]
  have h1 := sigma_add_nu_D (n := n) K
  have h2 := nu_add_sigma_D hKCS
  have hDconv : IsConvexPart (D (dotPairing n) K) := claim_a_convexPart _ K
  have hnoy : noyau (D (dotPairing n) K) = ∅ := by
    have h3 : nu (D (dotPairing n) K) = -1 := by linarith
    rw [nu, noyau_eq_linearSubvariety hDconv, dimS_linearSubvariety] at h3
    have h0 : finrank ℝ (noyauSub hDconv) = 0 := by omega
    rw [noyau_eq_linearSubvariety hDconv, Submodule.finrank_eq_zero.1 h0, linearSubvariety_bot]
  have hspanD : Submodule.span ℝ (F (D (dotPairing n) K)) = ⊤ := by
    have h3 : sigma (D (dotPairing n) K) = n := by linarith
    rw [sigma_eq, dimS] at h3
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_fin_fun]
    omega
  refine ⟨isStrictConvexPart_iff_noyau_eq_empty.2 ⟨hDconv, hnoy⟩,
    (isClosed_D _ (fun m => (dotPairing n m).continuous_of_finiteDimensional) K).isCompact, ?_⟩
  set C := insert 0 (F (D (dotPairing n) K)) with hC
  have hCconv : Convex ℝ C := hDconv
  have hCpos : IsPosCone C := (claim_a_cone _ K).2.2
  have hCaff : affineSpan ℝ C = ⊤ := (span_eq_top_iff_affineSpan (mem_insert _ _)).1
    (by rw [Submodule.span_insert_zero]; exact hspanD)
  have hint : (interior C).Nonempty := hCconv.interior_nonempty_iff_affineSpan_eq_top.2 hCaff
  obtain ⟨v, hvint, hv0⟩ :=
    (dense_compl_singleton (0 : Fin (n + 1) → ℝ)).inter_open_nonempty _ isOpen_interior hint
  have hv0' : v ≠ 0 := hv0
  have hintpos : IsPosCone (interior C) := fun c hc w hw => by
    have hsub : c • interior C ⊆ interior C := by
      rw [← interior_smul₀ hc.ne']
      exact interior_mono fun _ ⟨u, hu, e⟩ => e ▸ hCpos c hc u hu
    exact hsub ⟨w, hw, rfl⟩
  have hopen : IsOpen (ofCone (interior C)) := isOpen_ofCone hintpos isOpen_interior
  have hsub : ofCone (interior C) ⊆ D (dotPairing n) K := by
    have hCD : ofCone C = D (dotPairing n) K := by rw [hC, (claim_a_cone _ K).1]; rfl
    rw [← hCD]
    exact ofCone_subset_ofCone interior_subset
  exact ⟨mk v hv0', interior_maximal hsub hopen (mk_mem_ofCone hv0' hvint)⟩

/-- **Prop. 8** (`bzprop:c3s3p8_dual_corps_convexe`), both readings. -/
theorem prop8 {K : Set (S n)} (hK : IsCorpsConvexeS n K) :
    IsConvexPart (D (dotPairing n) K) ∧ D (dotPairing n) K ∈ CS (Fin (n + 1) → ℝ) ∧
      IsCorpsConvexeS n (D (dotPairing n) K) :=
  ⟨claim_a_convexPart _ K, ⟨claim_a_convexPart _ K,
    isClosed_D _ (fun m => (dotPairing n m).continuous_of_finiteDimensional) K⟩,
    isCorpsConvexeS_D hK⟩

/-! ### The Remark: the transposition `Δ` -/

/-- Two vectors with the same pairings are equal (the dot product is nondegenerate). -/
theorem eq_of_forall_dotPairing {a b : Fin (n + 1) → ℝ}
    (h : ∀ x, dotPairing n x a = dotPairing n x b) : a = b := by
  apply dotPairing_injective n
  refine LinearMap.ext fun x => ?_
  rw [dotPairing_swap, h, dotPairing_swap]

/-- The transpose `ᵗf` of an endomorphism of `ℝⁿ⁺¹`, through its matrix. -/
def transp (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  Matrix.toLin' (LinearMap.toMatrix' f).transpose

/-- `⟨f x, y⟩ = ⟨x, ᵗf y⟩`. -/
theorem dotPairing_transp (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
    (x y : Fin (n + 1) → ℝ) : dotPairing n (f x) y = dotPairing n x (transp f y) := by
  have h1 : dotPairing n (f x) y = y ⬝ᵥ (LinearMap.toMatrix' f *ᵥ x) := by
    rw [LinearMap.toMatrix'_mulVec, dotPairing_swap, dotPairing_apply]; rfl
  have h2 : dotPairing n x (transp f y) = x ⬝ᵥ ((LinearMap.toMatrix' f).transpose *ᵥ y) := by
    rw [dotPairing_apply, transp, Matrix.toLin'_apply]; rfl
  rw [h1, h2, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- `ᵗf` is characterized by `⟨f x, y⟩ = ⟨x, ᵗf y⟩`. -/
theorem transp_eq_of {f f' : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)}
    (h : ∀ x y, dotPairing n (f x) y = dotPairing n x (f' y)) : transp f = f' := by
  refine LinearMap.ext fun y => ?_
  exact eq_of_forall_dotPairing fun x => (dotPairing_transp f x y).symm.trans (h x y)

theorem transp_comp (f g : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) :
    transp (f ∘ₗ g) = transp g ∘ₗ transp f :=
  transp_eq_of fun x y => by
    rw [LinearMap.comp_apply, dotPairing_transp, dotPairing_transp, LinearMap.comp_apply]

theorem transp_id : transp (LinearMap.id : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) =
    LinearMap.id :=
  transp_eq_of fun _ _ => rfl

theorem transp_transp (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) :
    transp (transp f) = f :=
  transp_eq_of fun x y => by rw [dotPairing_swap, ← dotPairing_transp, dotPairing_swap]

theorem symm_comp_self (g : GLR (n + 1)) :
    (g.symm : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) ∘ₗ (g : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) = LinearMap.id := by
  ext1 v; simp

theorem self_comp_symm (g : GLR (n + 1)) :
    (g : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) ∘ₗ (g.symm : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) = LinearMap.id := by
  ext1 v; simp

/-- The linear equivalence `ᵗg`, of inverse `ᵗ(g⁻¹)`. -/
def transpEquiv (g : GLR (n + 1)) : GLR (n + 1) :=
  LinearEquiv.ofLinear (transp (g : _ →ₗ[ℝ] _)) (transp (g.symm : _ →ₗ[ℝ] _))
    (by rw [← transp_comp, symm_comp_self, transp_id])
    (by rw [← transp_comp, self_comp_symm, transp_id])

theorem transpEquiv_apply (g : GLR (n + 1)) (v : Fin (n + 1) → ℝ) :
    transpEquiv g v = transp (g : _ →ₗ[ℝ] _) v := rfl

theorem inv_apply' (g : GLR (n + 1)) (v : Fin (n + 1) → ℝ) : (g⁻¹ : GLR (n + 1)) v = g.symm v :=
  rfl

/-- **The dual representation** of `GL(n+1, ℝ)` (« la représentation duale de $GL(n, \R)$ »),
`g ↦ ᵗ(g⁻¹)`, the contragredient of the dot product. -/
def dualRep : GLR (n + 1) →* GLR (n + 1) where
  toFun g := transpEquiv g⁻¹
  map_one' := by
    ext1 v
    rw [inv_one, transpEquiv_apply]
    exact LinearMap.congr_fun transp_id v
  map_mul' g h := by
    ext1 v
    rw [mul_inv_rev, transpEquiv_apply, LinearEquiv.mul_apply, transpEquiv_apply,
      transpEquiv_apply]
    exact LinearMap.congr_fun (transp_comp _ _) v

theorem dualRep_apply (g : GLR (n + 1)) (v : Fin (n + 1) → ℝ) :
    dualRep g v = transp (g.symm : _ →ₗ[ℝ] _) v := rfl

theorem dualRep_inv_apply (g : GLR (n + 1)) (v : Fin (n + 1) → ℝ) :
    (dualRep g)⁻¹ v = transp (g : _ →ₗ[ℝ] _) v := by
  rw [← map_inv]; rfl

theorem dualRep_dualRep (g : GLR (n + 1)) : dualRep (dualRep g) = g := by
  ext1 v
  rw [dualRep_apply]
  have h : ((dualRep g).symm : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) = transp (g : _ →ₗ[ℝ] _) := by
    exact LinearMap.ext fun w => dualRep_inv_apply g w
  rw [h, transp_transp]; rfl

/-- `ᵗg⁻¹` is the contragredient of `g` for the dot product: `⟨g x, ᵗg⁻¹ y⟩ = ⟨x, y⟩`. -/
theorem dotPairing_dualRep (g : GLR (n + 1)) (x y : Fin (n + 1) → ℝ) :
    dotPairing n (g x) (dualRep g y) = dotPairing n x y := by
  have h := dotPairing_transp (g : _ →ₗ[ℝ] _) x (dualRep g y)
  rw [LinearEquiv.coe_coe] at h
  rw [h, dualRep_apply, ← LinearMap.comp_apply (transp _) (transp _), ← transp_comp,
    symm_comp_self, transp_id, LinearMap.id_apply]

/-- « la représentation duale de $GL(n, \R)$ est un automorphisme de $GL(n, \R)$ »: `g ↦ ᵗg⁻¹`
is an (involutive) automorphism of `GL(n+1, ℝ)`. -/
def dualRepEquiv : GLR (n + 1) ≃* GLR (n + 1) :=
  { Function.Involutive.toPerm _ dualRep_dualRep with map_mul' := dualRep.map_mul }

theorem dualRep_mem_posHomotheties {g : GLR (n + 1)} (hg : g ∈ posHomotheties _) :
    dualRep g ∈ posHomotheties _ := by
  obtain ⟨c, hc, h⟩ := mem_posHomotheties.1 hg
  refine mem_posHomotheties.2 ⟨c⁻¹, inv_pos.2 hc, fun v => ?_⟩
  rw [dualRep_apply]
  have hs : ∀ w, g.symm w = c⁻¹ • w := fun w => by
    apply g.injective
    rw [LinearEquiv.apply_symm_apply, h, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have ht : transp ((g.symm : GLR (n + 1)) : (Fin (n + 1) → ℝ) →ₗ[ℝ] _) =
      c⁻¹ • LinearMap.id := transp_eq_of (n := n) fun x y => by
    simp only [LinearEquiv.coe_coe, hs, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  rw [ht]; rfl

/-- `Δ` as a hom of `GS(n, ℝ) = GL(n+1, ℝ)/ℝ₊*`, induced by the dual representation. -/
def deltaHom : GSR n →* GSR n :=
  QuotientGroup.map _ _ dualRep fun _ hg => dualRep_mem_posHomotheties hg

theorem deltaHom_mk (g : GLR (n + 1)) :
    deltaHom (QuotientGroup.mk g : GSR n) = QuotientGroup.mk (dualRep g) := rfl

theorem deltaHom_involutive : Function.Involutive (deltaHom (n := n)) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H g => rw [deltaHom_mk, deltaHom_mk, dualRep_dualRep]

/-- **`Δ`** (« Cet automorphisme induit un automorphisme de $GS(n-1, \R)$, que nous noterons
$\Delta$ »): the automorphism of `GS(n, ℝ)` induced by the dual representation; an involution. -/
def Delta : GSR n ≃* GSR n :=
  { Function.Involutive.toPerm _ deltaHom_involutive with map_mul' := deltaHom.map_mul }

theorem Delta_mk (g : GLR (n + 1)) :
    Delta (QuotientGroup.mk g : GSR n) = QuotientGroup.mk (dualRep g) := rfl

theorem Delta_Delta (g : GSR n) : Delta (Delta g) = g := deltaHom_involutive g

/-- `D(h W) = ᵗh⁻¹ D(W)`, for every `h ∈ GL(n+1, ℝ)` and every part `W` of `S(n)`. -/
theorem D_smul (h : GLR (n + 1)) (V : Set (S n)) :
    D (dotPairing n) (h • V) = dualRep h • D (dotPairing n) V := by
  ext x
  induction x using ind with
  | h v hv =>
  rw [mk_mem_D, Set.mem_smul_set_iff_inv_smul_mem, smul_mk, mk_mem_D]
  have key : ∀ z, dotPairing n (h z) v = dotPairing n z ((dualRep h)⁻¹ v) := fun z => by
    rw [dualRep_inv_apply, ← dotPairing_transp]; rfl
  constructor
  · intro H z hz
    have hz0 : z ≠ 0 := hz.1
    have hmem : h z ∈ F (h • V) := by
      refine ⟨h.map_ne_zero_iff.2 hz0, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_mk]
      convert hz.2 using 2
      exact h.symm_apply_apply z
    have := H _ hmem
    rwa [key] at this
  · intro H m hm
    have hm0 : m ≠ 0 := hm.1
    have hmem : h.symm m ∈ F V := by
      refine ⟨h.symm.map_ne_zero_iff.2 hm0, ?_⟩
      have := hm.2
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_mk] at this
      exact this
    have := H _ hmem
    rwa [← key, LinearEquiv.apply_symm_apply] at this

/-- **The Remark** (`bzrem:c3s3r1_transposition`): for `g ∈ GS(n, ℝ)` and `W ∈ C(S(n))`,
`Δ(g) W = D(g(D W))`. -/
theorem remark_transposition (g : GSR n) {W : Set (S n)} (hW : W ∈ CS (Fin (n + 1) → ℝ)) :
    Delta g • W = D (dotPairing n) (g • D (dotPairing n) W) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
  rw [Delta_mk]
  change dualRep g • W = D (dotPairing n) (g • D (dotPairing n) W)
  rw [D_smul, (dotPairing_prop1 n).2 W hW]


/-! ### Instances: the dimension conventions at `W = ∅`, `W = S(n)` and `W` a point -/

theorem linearSubvariety_top :
    linearSubvariety (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) = (univ : Set (S n)) := by
  apply F_injective
  rw [F_linearSubvariety, F_univ]
  ext v; simp

theorem empty_mem_CS : (∅ : Set (S n)) ∈ CS (Fin (n + 1) → ℝ) :=
  ⟨by rw [← linearSubvariety_bot]; exact isConvexPart_linearSubvariety _, isClosed_empty⟩

theorem univ_mem_CS : (univ : Set (S n)) ∈ CS (Fin (n + 1) → ℝ) :=
  ⟨by rw [← linearSubvariety_top]; exact isConvexPart_linearSubvariety _, isClosed_univ⟩

theorem D_empty : D (dotPairing n) (∅ : Set (S n)) = univ := by
  rw [← linearSubvariety_bot, D_linearSubvariety, ← linearSubvariety_top]
  congr 1
  apply Submodule.eq_top_of_finrank_eq
  have h := finrank_add_finrank_orth (n := n) ⊥
  rw [finrank_bot] at h
  rw [finrank_fin_fun]; omega

theorem D_univ : D (dotPairing n) (univ : Set (S n)) = ∅ := by
  rw [← linearSubvariety_top, D_linearSubvariety, ← linearSubvariety_bot (E := Fin (n + 1) → ℝ)]
  congr 1
  apply Submodule.finrank_eq_zero.1
  have h := finrank_add_finrank_orth (n := n) ⊤
  rw [finrank_top, finrank_fin_fun] at h
  omega

theorem sigma_empty : sigma (∅ : Set (S n)) = -1 := by rw [sigma_eq, dimS_empty]

theorem nu_empty : nu (∅ : Set (S n)) = -1 := by
  rw [nu, subset_empty_iff.1 (noyau_subset (k := (∅ : Set (S n)))), dimS_empty]

theorem dimS_univ : dimS (univ : Set (S n)) = n := by
  rw [← linearSubvariety_top, dimS_linearSubvariety, finrank_top, finrank_fin_fun]; push_cast; ring

theorem sigma_univ : sigma (univ : Set (S n)) = n := by rw [sigma_eq, dimS_univ]

theorem nu_univ : nu (univ : Set (S n)) = n := by
  have h : noyau (univ : Set (S n)) = univ := by
    rw [noyau_eq univ_mem_CS.1]; ext; simp
  rw [nu, h, dimS_univ]

/-- **Instance, `W = ∅` and `W = S(n)`**: `σ(∅) = −1`, `D(∅) = S(n)`, `ν(S(n)) = n`, and
`σ(S(n)) = n`, `D(S(n)) = ∅`, `ν(∅) = −1`: both identities of Prop. 7 read `−1 + n = n − 1`
and `n + (−1) = n − 1`, and Prop. 7 applies to both parts. -/
theorem prop7_empty_univ :
    (sigma (∅ : Set (S n)) = -1 ∧ D (dotPairing n) ∅ = univ ∧ nu (univ : Set (S n)) = n) ∧
      (sigma (univ : Set (S n)) = n ∧ D (dotPairing n) univ = ∅ ∧ nu (∅ : Set (S n)) = -1) ∧
      (sigma (∅ : Set (S n)) + nu (D (dotPairing n) ∅) = n - 1 ∧
        sigma (univ : Set (S n)) + nu (D (dotPairing n) univ) = n - 1) :=
  ⟨⟨sigma_empty, D_empty, nu_univ⟩, ⟨sigma_univ, D_univ, nu_empty⟩,
    (prop7 empty_mem_CS).2.2.1, (prop7 univ_mem_CS).2.2.1⟩

theorem span_F_singleton {v : Fin (n + 1) → ℝ} (hv : v ≠ 0) :
    Submodule.span ℝ (F ({mk v hv} : Set (S n))) = ℝ ∙ v := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨hw, hwv⟩
    obtain ⟨c, -, hc⟩ := (mk_eq_mk_iff_exists_pos hv hw).1 (mem_singleton_iff.1 hwv).symm
    rw [SetLike.mem_coe, ← hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨hv, rfl⟩

theorem sigma_point (x : S n) : sigma ({x} : Set (S n)) = 0 := by
  induction x using ind with
  | h v hv =>
  rw [sigma_eq, dimS, span_F_singleton hv, finrank_span_singleton hv]; simp

theorem nu_point (x : S n) : nu ({x} : Set (S n)) = -1 := by
  induction x using ind with
  | h v hv =>
  have h : noyau ({mk v hv} : Set (S n)) = ∅ := by
    rw [noyau_eq (isConvexPart_singleton hv), eq_empty_iff_forall_notMem]
    rintro m ⟨hm, hm'⟩
    rw [mem_singleton_iff] at hm hm'
    subst hm
    exact mk_ne_neg_mk hv hm'.symm
  rw [nu, h, dimS_empty]

theorem point_mem_CS (x : S n) : ({x} : Set (S n)) ∈ CS (Fin (n + 1) → ℝ) := by
  induction x using ind with
  | h v hv => exact ⟨isConvexPart_singleton hv, isClosed_singleton⟩

/-- **Instance, `W` a point**: `σ({x}) = 0`, `ν({x}) = −1`; `D({x})` is a closed hemisphere, with
`ν(D{x}) = n − 1` (its boundary great sphere) and `σ(D{x}) = n`. -/
theorem prop7_point (x : S n) :
    sigma ({x} : Set (S n)) = 0 ∧ nu ({x} : Set (S n)) = -1 ∧
      IsClosedHemisphere (D (dotPairing n) {x}) ∧
      nu (D (dotPairing n) {x}) = n - 1 ∧ sigma (D (dotPairing n) {x}) = n := by
  have h := prop7 (point_mem_CS x)
  refine ⟨sigma_point x, nu_point x, dotPairing_D_point n x, ?_, ?_⟩
  · have := h.2.2.1; rw [sigma_point] at this; linarith
  · have := h.2.2.2; rw [nu_point] at this; linarith

/-! ### The literal transposition `g ↦ ᵗg` does not satisfy the Remark's formula -/

/-- `diag(2, 1)` on `ℝ²`. -/
def diag21 : GLR (1 + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (1 + 1) =>
    LinearEquiv.smulOfUnit (Units.mk0 (if i = 0 then (2 : ℝ) else 1) (by split_ifs <;> norm_num))

theorem diag21_apply (v : Fin (1 + 1) → ℝ) (i : Fin (1 + 1)) :
    diag21 v i = (if i = 0 then (2 : ℝ) else 1) * v i := rfl

theorem diag21_symm_apply (v : Fin (1 + 1) → ℝ) (i : Fin (1 + 1)) :
    diag21.symm v i = (if i = 0 then (2 : ℝ) else 1)⁻¹ * v i := rfl

theorem transp_diag21 : transp (diag21 : (Fin (1 + 1) → ℝ) →ₗ[ℝ] _) = diag21 :=
  transp_eq_of (n := 1) fun x y => by
    simp only [dotPairing_apply, LinearEquiv.coe_coe, diag21_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem transp_diag21_symm :
    transp ((diag21.symm : GLR (1 + 1)) : (Fin (1 + 1) → ℝ) →ₗ[ℝ] _) = (diag21.symm : GLR (1 + 1)) :=
  transp_eq_of (n := 1) fun x y => by
    simp only [dotPairing_apply, LinearEquiv.coe_coe, diag21_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Remark's « la transposition », read literally, fails the formula** (`n = 1`): for
`g = diag(2, 1)` and `W` the point `s(1, 1)` of `S(1)`, `ᵗg W = {s(2, 1)}` while
`D(g(D W)) = ᵗg⁻¹ W = {s(1/2, 1)}`. The automorphism of the Remark is the dual representation
`g ↦ ᵗg⁻¹` (`dualRep`, `Delta`), not `g ↦ ᵗg` (an anti-automorphism). -/
theorem transpose_literal_differs :
    ∃ (g : GLR (1 + 1)) (W : Set (S 1)), W ∈ CS (Fin (1 + 1) → ℝ) ∧
      (QuotientGroup.mk (transpEquiv g) : GSR 1) • W ≠
        D (dotPairing 1) ((QuotientGroup.mk g : GSR 1) • D (dotPairing 1) W) := by
  set e : Fin (1 + 1) → ℝ := fun _ => 1
  have he : e ≠ 0 := fun h => by simpa [e] using congrFun h 0
  refine ⟨diag21, {mk e he}, point_mem_CS _, ?_⟩
  rw [← remark_transposition _ (point_mem_CS _), Delta_mk]
  change transpEquiv diag21 • ({mk e he} : Set (S 1)) ≠ dualRep diag21 • {mk e he}
  rw [Set.smul_set_singleton, Set.smul_set_singleton, smul_mk, smul_mk, Ne,
    Set.singleton_eq_singleton_iff, mk_eq_mk_iff_exists_pos]
  rintro ⟨c, hc, hce⟩
  have h0 := congrFun hce 0
  have h1 := congrFun hce 1
  rw [transpEquiv_apply, transp_diag21] at h0 h1
  rw [dualRep_apply, transp_diag21_symm] at h0 h1
  simp only [LinearEquiv.coe_coe, diag21_apply, diag21_symm_apply, Pi.smul_apply,
    smul_eq_mul, e] at h0 h1
  norm_num at h0 h1
  rw [h1] at h0
  norm_num at h0

end Sphere

end Benzecri
