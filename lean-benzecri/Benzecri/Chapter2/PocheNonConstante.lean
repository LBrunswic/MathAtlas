import Benzecri.Chapter2.Lignes
import Benzecri.Chapter2.PremierAffine

/-!
# Chapter 2 § 1, Déf. 1 and 1′ in corrected form (DEC-178): pockets whose cote is non-constant, with non-degenerate witnesses; Prop. 6 as printed over them

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 1 « Coques et poches » (journal pp. 246–247) and § 2, Prop. 6
(p. 252); transcription `papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target
T-bz-poche-nonconstant. The author's ruling DEC-178 (OQ-61 (a)) adds « z non-constant » to
Déf. 1/1′ (a finding against the definition); 7° and Prop. 6 then hold as printed. All three
labels are marked **in corrected form, under DEC-178**; the printed definitions stay in
`Chapter2/Poches.lean` (`IsPocheAff`, `IsPocheProj`) and are strictly broader (SCOPE).

* **`bzdef:c2s1d1_poche_affine`** — `benzecri1960_ch2.tex:95` (Déf. 1, l.95–117), corrected:
  `Benzecri.IsPocheAffNC`, the printed `IsPocheAff` plus `nonConstant : ∃ x y, z x ≠ z y`. The
  readings of « non-constant » agree on a pocket (`IsPocheAff.nonConstant_tfae`,
  `isPocheAffNC_iff_ne_zero`). Witness with a non-constant cote: the half-space
  (`exists_isPocheAffNC_demiEspace`); over the paper's manifolds, `pocheAffNCNonVide_iff`
  (non-empty iff `n ≥ 1`).
* **`bzdef:c2s1d1prime_poche_projective`** — `benzecri1960_ch2.tex:119` (Déf. 1′, l.119–145),
  corrected: `Benzecri.IsPocheProjNC`, the printed `IsPocheProj` plus `nonConstant`
  (`IsPocheProj.nonConstant_tfae`, `isPocheProjNC_iff_ne_zero`). Witness:
  `exists_isPocheProjNC_demiEspace`, through the Remarque (`IsPocheAffNC.toPocheProjNC`);
  `pocheProjNCNonVide_iff`.
* **`bzprop:c2s2p6_ligne_brisee_poche`** — `benzecri1960_ch2.tex:437` (Prop. 6, l.437–443, proof
  l.445–449), as printed over the corrected Déf. 1′: `Benzecri.IsPocheProjNC.ligne_brisee_poche`;
  over the paper's manifolds, `ligneBriseePocheNCPrinted n` for every `n`. Its hypotheses are
  satisfiable on every pocket of dimension `≥ 1` (`IsPocheProj.exists_hypotheses_ligne_brisee`),
  in particular on the half-space (`ligneBriseePocheNC_hypotheses_demiEspace`).

Also, unmarked: 7° over the corrected Déf. 1′ (`IsPocheProjNC.septieme_propriete`, a lemma for
the row of T-bz-c2-proprietes), the Remarque after Déf. 1′ for corrected pockets
(`IsPocheAffNC.toPocheProjNC`, `_transport`), and the printed pockets that the correction
excludes (`not_isPocheAffNC_model`, `exists_isPocheProj_not_isPocheProjNC`).

> **Déf. 1 (cas affin).** Soit $V$ une variété localement affine de dimension $n$ : on définit une
> *poche* de $V$ par la donnée : — d'un ouvert connexe $P$ de $V$; — d'une carte $\varphi$ de $P$
> dans $\R^n$ compatible avec la structure affine de $P$; — d'une fonction linéaire $z$ sur $\R^n$
> appelée cote. Le triple $(P, \varphi, z)$ doit satisfaire aux deux conditions suivantes :
> *a*. Sur l'image $\varphi(P)$ la cote $z$ a pour borne inférieure $0$ et est majorée par $1$;
> *b*. Soit $(M, N)$ un segment de $V$ dont l'extrémité $M$ appartienne à $P$. Soit
> $\tilde{\varphi}$ une carte compatible d'un voisinage de $(M, N)$ dans $\R^n$ ayant en $M$ même
> germe que $\varphi$. Alors, si $z(\tilde{\varphi}(N))$ est inférieur à $1$, $N$ appartient à $P$.
>
> **Déf. 1′ (cas projectif).** Soit $V$ une variété localement projective de dimension $n$ : on
> définit une *poche* de $V$ par la donnée : — d'un ouvert connexe $P$ de $V$; — d'un hémisphère
> ouvert $\mathring{H}$ de $S(n)$; — d'une carte $\varphi$ de $P$ dans $S(n)$ compatible avec la
> structure projective, et telle que $\varphi(P)\subset\mathring{H}$; — d'une fonction linéaire
> $z$, appelée cote, sur $\mathring{H}$ considéré comme espace affin. (Le système
> $P, \mathring{H}, \varphi, z)$ doit satisfaire aux deux conditions suivantes : *a*. Sur l'image
> $\varphi(P)$, la cote $z$ a pour borne inférieure $0$ et est majorée par $1$; *b*. Soit
> $(M, N)$ un segment de $V$ dont l'extrémité $M$ appartienne à $P$. Soit $\tilde{\varphi}$ une
> carte compatible d'un voisinage de $(M, N)$ dans $S(n)$ ayant en $M$ même germe que
> $\varphi$. Alors, $\tilde{\varphi}(M, N)\subset\mathring{H}$ et, si
> $z(\tilde{\varphi}(N))$ est inférieur à $1$, $N$ appartient à $P$.
>
> **Proposition 6.** Soit $V$ une variété localement projective, possédant une poche
> $(P, \mathring{H}, \varphi, z)$. Soient $A$ et $B$ deux points de $V$, $L$ une ligne brisée
> joignant $A$ à $B$, et formée de $p$ segments tous majorés dans $V$ par $k=\log K$. Supposons
> que $A\in P$; $z(\varphi(A))<1/K^p$ : alors $B$ est aussi dans $P$, ainsi que $L$, et l'on a
> $z(\varphi(B))<K^p\,z(\varphi(A))$.
> La proposition se démontre par récurrence sur $p$ : pour $p=1$, c'est la septième propriété de
> la pseudo-longueur, le passage de $p$ à $p+1$ est immédiat.

The correction (DEC-178, recorded in `registers/DECISIONS.md`): « z non-constant » is added to the
data of Déf. 1 and Déf. 1′.

## The proofs formalized

**The readings agree.** For a printed pocket, five conditions are equivalent (`List.TFAE`):
`z` non-constant on its domain (`ℝⁿ`, resp. `H̊`; the literal reading, the definition here);
`z ≢ 0` (the hypothesis `∃ y, z y ≠ 0` that `Lignes.lean` carries); `z.linear ≠ 0`; `z`
non-constant on `φ(P)`; `z > 0` on `φ(P)` (the infimum `0` of condition *a* is not attained).
From non-constant to `≢ 0` is immediate; from `≢ 0` to `> 0 on φ(P)` is the interior-minimum
argument (`IsPocheProj.cote_pos_of_ne_zero`, strict, and its affine twin
`IsPocheAff.cote_pos_of_ne_zero`, here: `φ(P)` is open and `z ≥ 0` on it, so an interior zero of
`z` forces `z.linear = 0` and `z ≡ 0`); from `> 0` to non-constant on `φ(P)`, the infimum `0` is
approached (`IsGLB.exists_between`). **Witnesses**: the half-space `{x₀ > 0}` of `ℝⁿ⁺¹` with the
pocket `({x₀ < 1}, inclusion, x₀)` of `exists_isPocheAff_demiEspace` (`Chapter2/CasAffin.lean`,
built by the affine example with `p` the inclusion, injective: DEC-180), and its image by the
Remarque after Déf. 1′ for the projective case. **Prop. 6** is the strict
`IsPocheProj.ligne_brisee_poche_of_ne_zero` (the printed induction on `p` through 7°), fed by
`z ≢ 0` from the corrected definition.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 1/1′: the data and conditions *a*, *b* | ✓ carried: the printed `IsPocheAff` / `IsPocheProj` (strict, marked; their own checklist in `Chapter2/Poches.lean`), as the parent structure |
| DEC-178: « z non-constant » | ✓ carried: `nonConstant : ∃ x y, z x ≠ z y`, on `ℝⁿ` (resp. on the affine space `H̊`); equivalent on a pocket to every other reading (`nonConstant_tfae`) |
| `V` « une variété » of dimension `n` (Hausdorff, connected, second countable) | ⚠ weakened in the lemmas: any `ChartedSpace` over `ℝⁿ` (resp. `S(n)`), `HasGroupoid` where used; carried in the printed forms `PocheAffNCNonVide`, `PocheProjNCNonVide`, `LigneBriseePocheNCPrinted` |
| the dimension (DEC-177: `n ≥ 1` implied) | ✓ every `n`; in dimension `0` no corrected pocket exists (`not_isPocheAffNC_dim_zero`, `not_isPocheProjNC_dim_zero`), so the corrected definitions are non-vacuous exactly for `n ≥ 1` |
| Prop. 6: « une poche $(P, \mathring{H}, \varphi, z)$ » | ✓ carried, corrected: `IsPocheProjNC P l φ z` |
| Prop. 6: « $L$ une ligne brisée … $p$ segments tous majorés dans $V$ par $k=\log K$ » | ✓ carried: `IsLigneBrisee n (Real.log K) p A B L` (strict, `Chapter2/Lignes.lean`) |
| Prop. 6: `K` | ⚠ weakened: any real `K` (the hypotheses force `K > 1`, or `K < −1` with `p` even) |
| Prop. 6: `A ∈ P`, `z(φ(A)) < 1/K^p` | ✓ carried |
| Prop. 6: `B ∈ P`, `L ⊆ P`, `z(φ(B)) < K^p z(φ(A))` | ✓ carried, as printed (the strict `<`) |

## SCOPE (disclosed)

* **The correction is a genuine restriction**, in every dimension: the printed model pocket
  `(ℝⁿ, id, 0)` is not a corrected pocket (`not_isPocheAffNC_model`), nor is its projective image
  `(ℝⁿ, H₀, j, 0)`, the counterexample to the printed 7° and Prop. 6
  (`exists_isPocheProj_not_isPocheProjNC`, from the strict `exists_isPocheProj_cote_zero`). The
  printed `IsPocheAff` / `IsPocheProj` are therefore strictly broader than the corrected
  definitions; every theorem of the strict library proved for a printed pocket applies to a
  corrected one through `.toIsPocheAff` / `.toIsPocheProj`.
* **The textual evidence for the tacit hypothesis** (the finding behind DEC-178, already recorded
  on these rows): the examples and the § 3 forward reference build `P` from « le demi-espace
  ouvert : $z<1$ » (l.158, 165–166, 174, 186), which is a half-space only when `z` is
  non-constant; the proof of 7° uses `0 < z(f)` (l.343, l.351).
* **Dimension 0** (DEC-177): every affine function on `ℝ⁰`, or on the one-point open hemisphere of
  `S(0)`, is constant, so the corrected definitions are empty there
  (`pocheAffNCNonVide_iff`, `pocheProjNCNonVide_iff`: non-empty iff `0 < n`).
* **Déf. 2 and 3** (shells, strict shells) are defined over pockets; under DEC-178 they inherit
  the condition. They are not re-stated here (not this target's labels); the strict witnesses
  `exists_isCoqueStricteAff_demiDroite`, `exists_isCoqueStricteProj_demiDroite` already have the
  non-constant cote `x₀`.
* **7°** is the row of T-bz-c2-proprietes; `IsPocheProjNC.septieme_propriete` is given here as
  an unmarked lemma for its assembly.
* The scan (journal pp. 246–247, PDF pp. 19–20) agrees with the transcription of l.95–145.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Déf. 1, corrected -/

section PocheAffNC

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]

/-- **Déf. 1, corrected under DEC-178** (`bzdef:c2s1d1_poche_affine`): a *pocket* `(P, φ, z)` of
the locally affine `n`-manifold `V` is a pocket of the printed Déf. 1 (`IsPocheAff`: `P` open
connected, `φ` a compatible chart with source `P`, `z` an affine « fonction linéaire » on `ℝⁿ`,
conditions *a* and *b*) **whose cote `z` is non-constant** on `ℝⁿ` (the ruling's « z
non-constant »). Every other reading of « non-constant » is equivalent on a pocket
(`IsPocheAff.nonConstant_tfae`). -/
structure IsPocheAffNC (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ))
    (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : Prop extends IsPocheAff P φ z where
  nonConstant : ∃ x y, z x ≠ z y

variable {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}

/-- The cote is `≥ 0` on an affine pocket (condition *a*). -/
theorem IsPocheAff.cote_nonneg (hP : IsPocheAff P φ z) {M : V} (hM : M ∈ P) : 0 ≤ z (φ M) :=
  hP.isGLB.1 (mem_image_of_mem z (mem_image_of_mem φ hM))

/-- **The cote of an affine pocket is either identically `0` or `> 0` on `φ(P)`** (the affine
twin of the strict `IsPocheProj.cote_pos_of_ne_zero`): `φ(P)` is open and `z ≥ 0` on it, and an
affine function with an interior minimum `0` vanishes identically. -/
theorem IsPocheAff.cote_pos_of_ne_zero (hP : IsPocheAff P φ z) (hz : ∃ y, z y ≠ 0) {M : V}
    (hM : M ∈ P) : 0 < z (φ M) := by
  rcases (hP.cote_nonneg hM).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨y, hy⟩ := hz
  apply hy
  have hopen : IsOpen (φ '' P) := by
    rw [← hP.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  -- an affine function with a local minimum at an interior point has a zero linear part
  have hlin : ∀ u : Fin n → ℝ, z.linear u = 0 := by
    intro u
    have hc : Continuous fun t : ℝ => t • u + φ M :=
      (continuous_id.smul continuous_const).add continuous_const
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • u + φ M ∈ φ '' P :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [zero_smul, zero_add]
        exact hopen.mem_nhds ⟨M, hM, rfl⟩)
    have hge : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * z.linear u := hev.mono fun t ht => by
      have h1 := hP.isGLB.1 (mem_image_of_mem z ht)
      rwa [← vadd_eq_add, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, ← h,
        add_zero] at h1
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hge
    have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h2 := @hball (-(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith)
    nlinarith
  rw [← vsub_vadd y (φ M), AffineMap.map_vadd, hlin, zero_vadd]
  exact h.symm

/-- **On an affine pocket the readings of « z non-constant » agree**: `z` non-constant on `ℝⁿ`
(the definition of `IsPocheAffNC`); `z ≢ 0`; `z.linear ≠ 0`; `z` non-constant on `φ(P)`; `z > 0`
on `φ(P)` (the infimum `0` of condition *a* is not attained). -/
theorem IsPocheAff.nonConstant_tfae (hP : IsPocheAff P φ z) :
    List.TFAE [∃ x y, z x ≠ z y, ∃ y, z y ≠ 0, z.linear ≠ 0,
      ∃ x ∈ φ '' P, ∃ y ∈ φ '' P, z x ≠ z y, ∀ x ∈ φ '' P, 0 < z x] := by
  obtain ⟨M, hM⟩ := hP.isConnected.nonempty
  tfae_have 1 → 3 := by
    rintro ⟨x, y, hxy⟩ h0
    apply hxy
    rw [← vsub_vadd x y, AffineMap.map_vadd, h0, LinearMap.zero_apply, zero_vadd]
  tfae_have 3 → 1 := by
    intro h0
    obtain ⟨u, hu⟩ : ∃ u, z.linear u ≠ 0 := by
      by_contra hc
      exact h0 (LinearMap.ext fun u => Classical.byContradiction fun h => hc ⟨u, h⟩)
    refine ⟨u +ᵥ φ M, φ M, ?_⟩
    rw [AffineMap.map_vadd, vadd_eq_add]
    intro h
    apply hu
    linarith
  tfae_have 1 → 2 := by
    rintro ⟨x, y, hxy⟩
    by_contra hc
    have hc' : ∀ w, z w = 0 := fun w => Classical.byContradiction fun h => hc ⟨w, h⟩
    exact hxy (by rw [hc' x, hc' y])
  tfae_have 2 → 5 := by
    rintro hz _ ⟨N, hN, rfl⟩
    exact hP.cote_pos_of_ne_zero hz hN
  tfae_have 5 → 4 := by
    intro hpos
    have h0 := hpos _ ⟨M, hM, rfl⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, -, hlt⟩ := hP.isGLB.exists_between h0
    exact ⟨y, hy, φ M, ⟨M, hM, rfl⟩, hlt.ne⟩
  tfae_have 4 → 1 := by
    rintro ⟨x, -, y, -, hxy⟩
    exact ⟨x, y, hxy⟩
  tfae_finish

/-- **The corrected Déf. 1 is the printed one plus `z ≢ 0`**, the hypothesis `∃ y, z y ≠ 0`
under which the strict library proves 7° and Prop. 6 as printed. -/
theorem isPocheAffNC_iff_ne_zero :
    IsPocheAffNC P φ z ↔ IsPocheAff P φ z ∧ ∃ y, z y ≠ 0 :=
  ⟨fun h => ⟨h.toIsPocheAff, (h.toIsPocheAff.nonConstant_tfae.out 0 1).1 h.nonConstant⟩,
    fun h => ⟨h.1, (h.1.nonConstant_tfae.out 0 1).2 h.2⟩⟩

/-- The cote of a corrected affine pocket is not identically `0`. -/
theorem IsPocheAffNC.exists_ne_zero (hP : IsPocheAffNC P φ z) : ∃ y, z y ≠ 0 :=
  (isPocheAffNC_iff_ne_zero.1 hP).2

/-- **The cote of a corrected affine pocket is `> 0` on `φ(P)`.** -/
theorem IsPocheAffNC.cote_pos (hP : IsPocheAffNC P φ z) {M : V} (hM : M ∈ P) : 0 < z (φ M) :=
  hP.toIsPocheAff.cote_pos_of_ne_zero hP.exists_ne_zero hM

/-- **In dimension `0` there is no corrected affine pocket**: every affine function on `ℝ⁰` (a
point) is constant. Consistent with DEC-177 (`n ≥ 1` is implied in Chapter 2). -/
theorem not_isPocheAffNC_dim_zero {V : Type u} [TopologicalSpace V]
    [ChartedSpace (Fin 0 → ℝ) V] {P : Set V} {φ : OpenPartialHomeomorph V (Fin 0 → ℝ)}
    {z : (Fin 0 → ℝ) →ᵃ[ℝ] ℝ} : ¬ IsPocheAffNC P φ z := fun h => by
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  exact hxy (by rw [Subsingleton.elim x y])

/-- **The correction is a genuine restriction**: the printed model pocket `(ℝⁿ, id, 0)` of the
strict library (`isPocheAff_model`, a pocket of Déf. 1 as printed) is not a corrected pocket. -/
theorem not_isPocheAffNC_model (n : ℕ) :
    ¬ IsPocheAffNC (univ : Set (Fin n → ℝ)) (OpenPartialHomeomorph.refl _) 0 := fun h => by
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  exact hxy rfl

end PocheAffNC

/-! ### Déf. 1′, corrected -/

section PocheProjNC

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **Déf. 1′, corrected under DEC-178** (`bzdef:c2s1d1prime_poche_projective`): a *pocket*
`(P, H̊, φ, z)` of the locally projective `n`-manifold `V` is a pocket of the printed Déf. 1′
(`IsPocheProj`: `H̊` the open hemisphere of equation `l ≠ 0`, `P` open connected, `φ` a compatible
chart with source `P` and `φ(P) ⊆ H̊`, `z` an affine « fonction linéaire » on the affine space `H̊`,
conditions *a* and *b*) **whose cote `z` is non-constant** on `H̊`. Every other reading of
« non-constant » is equivalent on a pocket (`IsPocheProj.nonConstant_tfae`). -/
structure IsPocheProjNC (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
    (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : Prop
    extends IsPocheProj P l φ z where
  nonConstant : ∃ x y, z x ≠ z y

variable {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **On a projective pocket the readings of « z non-constant » agree**: `z` non-constant on `H̊`
(the definition of `IsPocheProjNC`); `z ≢ 0` (the hypothesis of the strict
`ligne_brisee_poche_of_ne_zero`, `septieme_propriete_of_ne_zero`); `z.linear ≠ 0`; `z`
non-constant on `φ(P)` read in `H̊`; `z > 0` on `φ(P)` (the infimum `0` is not attained). -/
theorem IsPocheProj.nonConstant_tfae (hP : IsPocheProj P l φ z) :
    List.TFAE [∃ x y, z x ≠ z y, ∃ y, z y ≠ 0, z.linear ≠ 0,
      ∃ x ∈ ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)),
        ∃ y ∈ ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)), z x ≠ z y,
      ∀ x ∈ ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)), 0 < z x] := by
  obtain ⟨M, hM⟩ := hP.isConnected.nonempty
  set m : Sphere.openHemisphere l := ⟨φ M, hP.mapsTo_hemi hM⟩ with hm
  have hmP : m ∈ ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)) := ⟨M, hM, rfl⟩
  tfae_have 1 → 3 := by
    rintro ⟨x, y, hxy⟩ h0
    apply hxy
    rw [← vsub_vadd x y, AffineMap.map_vadd, h0, LinearMap.zero_apply, zero_vadd]
  tfae_have 3 → 1 := by
    intro h0
    obtain ⟨u, hu⟩ : ∃ u, z.linear u ≠ 0 := by
      by_contra hc
      exact h0 (LinearMap.ext fun u => Classical.byContradiction fun h => hc ⟨u, h⟩)
    refine ⟨u +ᵥ m, m, ?_⟩
    rw [AffineMap.map_vadd, vadd_eq_add]
    intro h
    apply hu
    linarith
  tfae_have 1 → 2 := by
    rintro ⟨x, y, hxy⟩
    by_contra hc
    have hc' : ∀ w, z w = 0 := fun w => Classical.byContradiction fun h => hc ⟨w, h⟩
    exact hxy (by rw [hc' x, hc' y])
  tfae_have 2 → 5 := by
    rintro hz y ⟨N, hN, hNy⟩
    have : y = ⟨φ N, hP.mapsTo_hemi hN⟩ := Subtype.ext hNy.symm
    rw [this]
    exact hP.cote_pos_of_ne_zero hz hN
  tfae_have 5 → 4 := by
    intro hpos
    have h0 := hpos m hmP
    obtain ⟨_, ⟨y, hy, rfl⟩, -, hlt⟩ := hP.isGLB.exists_between h0
    exact ⟨y, hy, m, hmP, hlt.ne⟩
  tfae_have 4 → 1 := by
    rintro ⟨x, -, y, -, hxy⟩
    exact ⟨x, y, hxy⟩
  tfae_finish

/-- **The corrected Déf. 1′ is the printed one plus `z ≢ 0`.** -/
theorem isPocheProjNC_iff_ne_zero :
    IsPocheProjNC P l φ z ↔ IsPocheProj P l φ z ∧ ∃ y, z y ≠ 0 :=
  ⟨fun h => ⟨h.toIsPocheProj, (h.toIsPocheProj.nonConstant_tfae.out 0 1).1 h.nonConstant⟩,
    fun h => ⟨h.1, (h.1.nonConstant_tfae.out 0 1).2 h.2⟩⟩

/-- The cote of a corrected projective pocket is not identically `0`. -/
theorem IsPocheProjNC.exists_ne_zero (hP : IsPocheProjNC P l φ z) : ∃ y, z y ≠ 0 :=
  (isPocheProjNC_iff_ne_zero.1 hP).2

/-- **The cote of a corrected projective pocket is `> 0` on `φ(P)`.** -/
theorem IsPocheProjNC.cote_pos (hP : IsPocheProjNC P l φ z) {M : V} (hM : M ∈ P) :
    0 < z ⟨φ M, hP.toIsPocheProj.mapsTo_hemi hM⟩ :=
  hP.toIsPocheProj.cote_pos_of_ne_zero hP.exists_ne_zero hM

/-- **In dimension `0` there is no corrected projective pocket**: an open hemisphere of `S(0)` is
affinely `ℝ⁰`, a point (`Sphere.nonempty_hemi_affineEquiv`), so every cote is constant. -/
theorem not_isPocheProjNC_dim_zero {V : Type u} [TopologicalSpace V] [ChartedSpace (S 0) V]
    {P : Set V} {l : Module.Dual ℝ (Fin (0 + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph V (S 0)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ} :
    ¬ IsPocheProjNC P l φ z := fun h => by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := l) (Module.finrank_fin_fun ℝ)
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  exact hxy (by rw [e.injective (Subsingleton.elim (e x) (e y))])

/-- **The correction is a genuine restriction**: the printed pocket `(ℝⁿ, H₀, j, 0)` of cote `0`
(`exists_isPocheProj_cote_zero`, the strict counterexample to the printed 7° and Prop. 6) is a
pocket of Déf. 1′ as printed and not a corrected pocket, in every dimension. -/
theorem exists_isPocheProj_not_isPocheProjNC (n : ℕ) :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (S n))
      (z : Sphere.openHemisphere (Sphere.lastForm n) →ᵃ[ℝ] ℝ),
      @IsPocheProj n (Fin n → ℝ) _ (projOfAff n (Fin n → ℝ)) univ (Sphere.lastForm n) _ φ z ∧
        ¬ @IsPocheProjNC n (Fin n → ℝ) _ (projOfAff n (Fin n → ℝ)) univ (Sphere.lastForm n) _
          φ z := by
  letI : ChartedSpace (S n) (Fin n → ℝ) := projOfAff n (Fin n → ℝ)
  obtain ⟨φ, z, hP, hz⟩ := exists_isPocheProj_cote_zero n
  refine ⟨φ, z, hP, fun h => ?_⟩
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  exact hxy (by rw [hz x, hz y])

end PocheProjNC

/-! ### The Remarque after Déf. 1′ for corrected pockets -/

section Remarque0NC

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]
  {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}

section Local

attribute [local instance] projOfAff

/-- **The Remarque after Déf. 1′ for corrected pockets**
(`bzrem:c2s1r0_poche_affine_vers_projective`, not a label of this target): `(P, H̊, j ∘ φ, z ∘ j⁻¹)`
is a corrected pocket of `V` with its canonical projective structure `projOfAff`, for every affine
isomorphism `j : ℝⁿ ≃ H̊`. -/
theorem IsPocheAffNC.toPocheProjNC (h : IsPocheAffNC P φ z)
    {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsPocheProjNC n V _ (projOfAff n V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  refine ⟨h.toIsPocheAff.toPocheProj j, ?_⟩
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  refine ⟨j x, j y, ?_⟩
  simpa using hxy

end Local

/-- The Remarque for corrected pockets, with the projective structure built from `j` itself. -/
theorem IsPocheAffNC.toPocheProjNC_transport (h : IsPocheAffNC P φ z)
    {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsPocheProjNC n V _ (transportChartedSpace (isOpenEmbedding_coe_affineEquiv j) V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  letI := transportChartedSpace (isOpenEmbedding_coe_affineEquiv j) V
  refine ⟨h.toIsPocheAff.toPocheProj_transport j, ?_⟩
  obtain ⟨x, y, hxy⟩ := h.nonConstant
  refine ⟨j x, j y, ?_⟩
  simpa using hxy

end Remarque0NC

/-! ### Witnesses with a non-constant cote: the half-space `{x₀ > 0}` of `ℝⁿ⁺¹` -/

section Witnesses

variable (n : ℕ)

/-- **Non-vacuity of the corrected Déf. 1, with a non-constant cote, in every dimension
`n + 1 ≥ 1`**: in the open half-space `{x₀ > 0}` of `ℝⁿ⁺¹` (connected, Hausdorff, second
countable, locally affine), `P = {x₀ < 1}`, `φ` the inclusion, `z = x₀` (the strict
`exists_isPocheAff_demiEspace`, through the affine example with `p` the inclusion, injective:
DEC-180); `φ(P) = {0 < x₀ < 1}` and `P ≠ V`. -/
theorem exists_isPocheAffNC_demiEspace :
    ∃ φ : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
      IsPocheAffNC {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      EqOn φ Subtype.val {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
      φ '' {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} = {x | 0 < x 0 ∧ x 0 < 1} ∧
      {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ≠ univ := by
  obtain ⟨φ, hP, hφeq, hφimg⟩ := exists_isPocheAff_demiEspace n
  refine ⟨φ, ⟨hP, 0, fun _ => 1, ?_⟩, hφeq, hφimg, ?_⟩
  · simp
  · intro h
    have h2 : (⟨fun _ => 2, show (0 : ℝ) < 2 by norm_num⟩ : demiEspaceOuvert n) ∈
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} := h ▸ mem_univ _
    exact absurd (show (2 : ℝ) < 1 from h2) (by norm_num)

/-- **Non-vacuity of the corrected Déf. 1′, with a non-constant cote, in every dimension
`n + 1 ≥ 1`**: the half-space with its canonical projective structure (`projOfAff`), over the
hemisphere `H₀ = {x_{n+2} > 0}`, the image by the Remarque of `exists_isPocheAffNC_demiEspace`. -/
theorem exists_isPocheProjNC_demiEspace :
    ∃ (φ : OpenPartialHomeomorph (demiEspaceOuvert n) (S (n + 1)))
      (z : Sphere.openHemisphere (Sphere.lastForm (n + 1)) →ᵃ[ℝ] ℝ),
      @IsPocheProjNC (n + 1) (demiEspaceOuvert n) _ (projOfAff (n + 1) (demiEspaceOuvert n))
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} (Sphere.lastForm (n + 1)) _ φ z := by
  obtain ⟨φ, hP, -, -, -⟩ := exists_isPocheAffNC_demiEspace n
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm (n + 1))
    (Module.finrank_fin_fun ℝ)
  exact ⟨_, _, hP.toPocheProjNC e.symm⟩

/-- **The corrected Déf. 1 is non-vacuous over the paper's manifolds of dimension `n`**: some
Hausdorff, connected, second countable locally affine `n`-manifold has a corrected pocket
`P ≠ V`. -/
def PocheAffNCNonVide : Prop :=
  ∃ (V : Type) (_ : TopologicalSpace V) (_ : ChartedSpace (Fin n → ℝ) V),
    HasGroupoid V (affGroupoid n) ∧ T2Space V ∧ ConnectedSpace V ∧ SecondCountableTopology V ∧
      ∃ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
        IsPocheAffNC P φ z ∧ P ≠ univ

/-- **The corrected Déf. 1′ is non-vacuous over the paper's manifolds of dimension `n`**. -/
def PocheProjNCNonVide : Prop :=
  ∃ (V : Type) (_ : TopologicalSpace V) (_ : ChartedSpace (S n) V),
    HasGroupoid V (projGroupoid n) ∧ T2Space V ∧ ConnectedSpace V ∧ SecondCountableTopology V ∧
      ∃ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) (_ : Fact (l ≠ 0))
        (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
        IsPocheProjNC P l φ z ∧ P ≠ univ

/-- **The corrected Déf. 1 is non-vacuous exactly in dimension `n ≥ 1`** (DEC-177). -/
theorem pocheAffNCNonVide_iff : PocheAffNCNonVide n ↔ 0 < n := by
  constructor
  · rintro ⟨V, _, _, -, -, -, -, P, φ, z, hP, -⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd hP not_isPocheAffNC_dim_zero
    · exact hn
  · intro hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨φ, hP, -, -, hne⟩ := exists_isPocheAffNC_demiEspace m
    exact ⟨demiEspaceOuvert m, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, _, φ, _, hP, hne⟩

/-- **The corrected Déf. 1′ is non-vacuous exactly in dimension `n ≥ 1`** (DEC-177). -/
theorem pocheProjNCNonVide_iff : PocheProjNCNonVide n ↔ 0 < n := by
  constructor
  · rintro ⟨V, _, _, -, -, -, -, P, l, _, φ, z, hP, -⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd hP not_isPocheProjNC_dim_zero
    · exact hn
  · intro hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨φ, z, hP⟩ := exists_isPocheProjNC_demiEspace m
    obtain ⟨-, -, -, -, hne⟩ := exists_isPocheAffNC_demiEspace m
    exact ⟨demiEspaceOuvert m, inferInstance, projOfAff (m + 1) _, hasGroupoid_projOfAff,
      inferInstance, inferInstance, inferInstance, _, Sphere.lastForm (m + 1), inferInstance, φ, z,
      hP, hne⟩

end Witnesses

/-! ### Prop. 6 as printed over the corrected Déf. 1′ (and 7°, a lemma) -/

section Prop6NC

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **Prop. 6, as printed, over the corrected Déf. 1′** (`bzprop:c2s2p6_ligne_brisee_poche`,
DEC-178): a broken line `L` of `p` segments majorised by `k = log K`, from `A ∈ P` with
`z(φ(A)) < 1/K^p` to `B`, lies in `P`, `B ∈ P`, and `z(φ(B)) < K^p z(φ(A))`. Any real `K`. -/
theorem IsPocheProjNC.ligne_brisee_poche (hP : IsPocheProjNC P l φ z) {A B : V} {L : Set V}
    {p : ℕ} {K : ℝ} (hL : IsLigneBrisee n (Real.log K) p A B L) (hA : A ∈ P)
    (hAK : z ⟨φ A, hP.toIsPocheProj.mapsTo_hemi hA⟩ < 1 / K ^ p) :
    L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.toIsPocheProj.mapsTo_hemi hB⟩ <
      K ^ p * z ⟨φ A, hP.toIsPocheProj.mapsTo_hemi hA⟩ :=
  hP.toIsPocheProj.ligne_brisee_poche_of_ne_zero hP.exists_ne_zero hL hA hAK

/-- **The hypotheses of Prop. 6 are satisfiable on every pocket, in dimension `n ≥ 1`**: for every
`K > 1` and `p ≥ 1` there is `A ∈ P` with `z(φ(A)) < 1/K^p` (condition *a*: the infimum is `0`)
and a broken line of `p` segments majorised by `log K` from `A` (the point segment `{A}`, `p`
times). So `IsPocheProjNC.ligne_brisee_poche` is not vacuous on a corrected pocket. -/
theorem IsPocheProj.exists_hypotheses_ligne_brisee (hP : IsPocheProj P l φ z) (hn : 1 ≤ n)
    {K : ℝ} (hK : 1 < K) {p : ℕ} (hp : 1 ≤ p) :
    ∃ (A : V) (hA : A ∈ P) (L : Set V), IsLigneBrisee n (Real.log K) p A A L ∧
      z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p := by
  have hpos : (0 : ℝ) < 1 / K ^ p := one_div_pos.2 (pow_pos (zero_lt_one.trans hK) p)
  obtain ⟨_, ⟨y, ⟨A, hA, hAy⟩, rfl⟩, -, hlt⟩ := hP.isGLB.exists_between hpos
  have hy : y = ⟨φ A, hP.mapsTo_hemi hA⟩ := Subtype.ext hAy.symm
  subst hy
  have hk : 0 < Real.log K := Real.log_pos hK
  have hline : ∀ q : ℕ, ∃ L : Set V, IsLigneBrisee n (Real.log K) (q + 1) A A L := by
    intro q
    induction q with
    | zero => exact ⟨{A}, IsLigneBrisee.segment (isMajoreSeg_singleton hn A hk)⟩
    | succ q ih =>
      obtain ⟨L, hL⟩ := ih
      exact ⟨{A} ∪ L, IsLigneBrisee.cons (isMajoreSeg_singleton hn A hk) hL⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨L, hL⟩ := hline q
  exact ⟨A, hA, L, hL, hlt⟩

/-- **7°, as printed, over the corrected Déf. 1′** (an unmarked lemma for the row
`bzthm:c2s2_proprietes_pseudo_longueur`, T-bz-c2-proprietes): `M ∈ P`, `z(φ(M)) < 1/K`,
`l_V(M, N) < log K` give `N ∈ P` and `z(φ(N)) < K z(φ(M))`. -/
theorem IsPocheProjNC.septieme_propriete (hP : IsPocheProjNC P l φ z) {Sg : Set V} {M N : V}
    (hM : M ∈ P) {K : ℝ} (hMK : z ⟨φ M, hP.toIsPocheProj.mapsTo_hemi hM⟩ < 1 / K)
    (hl : pseudoLength n Sg M N < (Real.log K : EReal)) :
    ∃ hN : N ∈ P, z ⟨φ N, hP.toIsPocheProj.mapsTo_hemi hN⟩ <
      K * z ⟨φ M, hP.toIsPocheProj.mapsTo_hemi hM⟩ :=
  hP.toIsPocheProj.septieme_propriete_of_ne_zero hP.exists_ne_zero hM hMK hl

end Prop6NC

/-- **Prop. 6 as printed, over the corrected Déf. 1′**, for the manifolds of dimension `n`
(Hausdorff, connected, second countable): the twin of the strict `LigneBriseePochePrinted`, which
is false for `n ≥ 1` (`ligneBriseePochePrinted_iff`), with `IsPocheProjNC` for `IsPocheProj`. -/
def LigneBriseePocheNCPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] (P : Set V)
    (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)] (φ : OpenPartialHomeomorph V (S n))
    (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) (hP : IsPocheProjNC P l φ z) (A B : V) (L : Set V)
    (p : ℕ) (K : ℝ), IsLigneBrisee n (Real.log K) p A B L → ∀ hA : A ∈ P,
      z ⟨φ A, hP.toIsPocheProj.mapsTo_hemi hA⟩ < 1 / K ^ p →
        L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.toIsPocheProj.mapsTo_hemi hB⟩ <
          K ^ p * z ⟨φ A, hP.toIsPocheProj.mapsTo_hemi hA⟩

/-- **Prop. 6 holds as printed over the corrected Déf. 1′, in every dimension.** -/
theorem ligneBriseePocheNCPrinted (n : ℕ) : LigneBriseePocheNCPrinted n :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hP _ _ _ _ _ hL hA hAK => hP.ligne_brisee_poche hL hA hAK

section NonVacuite

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- **Prop. 6 over the corrected Déf. 1′ is not vacuous, in every dimension `n + 1 ≥ 1`**: on the
half-space `{x₀ > 0}` of `ℝⁿ⁺¹` with its canonical projective structure, for every `K > 1` and
`p ≥ 1`, a corrected pocket, a point `A ∈ P` with `z(φ(A)) < 1/K^p` and a broken line of `p`
segments majorised by `log K` from `A` exist. -/
theorem ligneBriseePocheNC_hypotheses_demiEspace (n : ℕ) {K : ℝ} (hK : 1 < K) {p : ℕ}
    (hp : 1 ≤ p) :
    ∃ (φ : OpenPartialHomeomorph (demiEspaceOuvert n) (S (n + 1)))
      (z : Sphere.openHemisphere (Sphere.lastForm (n + 1)) →ᵃ[ℝ] ℝ)
      (hP : IsPocheProjNC {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1}
        (Sphere.lastForm (n + 1)) φ z)
      (A : demiEspaceOuvert n) (hA : A ∈ {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1})
      (L : Set (demiEspaceOuvert n)),
      IsLigneBrisee (n + 1) (Real.log K) p A A L ∧
        z ⟨φ A, hP.toIsPocheProj.mapsTo_hemi hA⟩ < 1 / K ^ p := by
  obtain ⟨φ, z, hP⟩ := exists_isPocheProjNC_demiEspace n
  obtain ⟨A, hA, L, hL, hz⟩ :=
    hP.toIsPocheProj.exists_hypotheses_ligne_brisee (Nat.le_add_left 1 n) hK hp
  exact ⟨φ, z, hP, A, hA, L, hL, hz⟩

end NonVacuite

end Benzecri
