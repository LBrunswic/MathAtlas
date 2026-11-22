import Benzecri.Chapter2.Lignes

/-!
# Chapter 2 § 2 — the properties 1°–7° of the pseudo-length, assembled (the editorial enonce of p. 249)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 249–251; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-proprietes (DEC-137,
DEC-206).

* **`bzthm:c2s2_proprietes_pseudo_longueur`** — `benzecri1960_ch2.tex:229` (the editorial
  enonce, l.229–258, statement l.230–256; proof l.293–304 and l.321–357):
  `Benzecri.proprietes_pseudo_longueur`, the seven properties as one statement (DEC-206), for
  `n ≥ 1` (DEC-177: `n ≥ 1` is implied throughout Ch. 2) and, in 7°, for a pocket whose cote is
  non-constant (DEC-178: « z non-constant » is part of Déf. 1/1′), carried as `∃ y, z y ≠ 0`,
  which for a pocket is the same (`IsPocheProj.exists_ne_zero_iff_nonconstant`). Sorry-free.
  The enonce as printed, with Déf. 1′ as printed and no dimension excluded, holds in no dimension
  (`Benzecri.not_proprietesPseudoLongueurPrinted`; the findings of OQ-45 and OQ-61, ruled).

> $l_V(M, N)$ possède les propriétés suivantes :
>
> 1° $l_V(M, N)\geqq 0$; $l_V(M, M)=0$;
>
> 2° Soit $g$ un automorphisme projectif de $V$, on a $l_V(gM, gN)=l_V(M, N)$;
>
> 3° Soit $(M, N)\subset(M', N')$, on a $l_V(M, N)\leqq l_V(M', N')$;
>
> 4° Soit $V'$ un ouvert de $V$ considéré comme variété localement projective, on a
> $l_V(M, N)\leqq l_{V'}(M, N)$ pour tout segment $(M, N)$ inclus dans $V'$;
>
> 5° La pseudo-longueur est une fonction semi-continue supérieurement du segment, c'est-à-dire
> que, si un segment $(M_i, N_i)$ tend vers $(M, N)$, on a
> $\overline{\lim}\, l_V(M_i, N_i)\leqq l_V(M, N)$;
>
> 6° Si $V$ est l'intérieur d'un corps convexe, $l_V(M, N)$ est une fonction continue en $M$ et
> $N$ sur le produit $V\times V$; $l_V(M, N)$ est nulle si et seulement si $M=N$;
>
> 7° Soit $(P, \mathring{H}, \varphi, z)$ une poche de $V$; soit $M\in P$ un point de $V$ tel que
> $z(\varphi(M))<\dfrac{1}{K}$ (où $K$ désigne un nombre réel supérieur à $1$); soit $(M, N)$ un
> segment de $V$ dont la pseudo-longueur $l_V(M, N)$ soit inférieure à $\log K$; alors,
> $N\in P$ et $z\,\varphi(N)<K\,z(\varphi(M))$.

> Les propriétés 1° et 2° résultent trivialement de la définition. Les propriétés 3° et 4°
> résultent de la proposition 1. La propriété 6° résulte de la [proposition 2]. […] Pour démontrer
> 5°, nous démontrerons que, si $MN$ est un segment borné par $k$ dans $V$, il en est de même de
> tout segment assez voisin de $MN$. […] Pour démontrer 7°, nous calculerons en considérant la
> structure affine de $\mathring{H}$. […]

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a « variété localement projective » | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]`; Hausdorff, connected, second countable never used |
| the dimension `n` (never printed) | ✓ carried as ruled: `[NeZero n]`, DEC-177 (`n ≥ 1` implied throughout Ch. 2). For `n = 0`, 1° fails (`l_V(M, M) = +∞`, OQ-45) |
| `l_V(M, N)` of « un segment $(M, N)$ » | ✓ carried: `pseudoLength n Sg M N` of a segment `(Sg, M, N)` (Déf. 3, a function of the segment: the reading of T-bz-c2-mesure) |
| 1°: `l_V(M, N) ≥ 0` | ⚠ weakened: for every `(Sg, M, N)`, a segment or not |
| 1°: `l_V(M, M) = 0` | ✓ carried, for every segment from `M` to `M` (it is `{M}`, `IsProjSegment.eq_singleton`; it exists, `isProjSegment_singleton`) |
| 2°: `g` « un automorphisme projectif de $V$ » | ✓ carried: `g : GXAut (GSR n) (S n) V` (Déf. 15); the segment `(gM, gN)` is `g(Sg)`; no segment hypothesis needed |
| 3°: `(M, N) ⊂ (M', N')` | ⚠ weakened: `(Sg, M, N)` a segment and `Sg ⊆ Sg'`; `(Sg', M', N')` need not be one |
| 4°: `V'` an open set of `V` « considéré comme variété localement projective » | ✓ carried: `W : TopologicalSpace.Opens V` with Mathlib's induced charted structure |
| 4°: « pour tout segment $(M, N)$ inclus dans $V'$ » | ⚠ weakened: any `Sg ⊆ W` with `M, N ∈ W`; `l_{V'}(M, N)` is the pseudo-length of `Sg` read in `W` |
| 5°: « fonction semi-continue supérieurement du segment » | ✓ carried, a reading (question): for `c > l_V(M, N)` there are an open `U ⊇ (M, N)` and a neighbourhood of `(M, N)` in `V × V` such that every segment inside `U` with endpoints in it has `l_V < c` (the printed proof's « tout segment assez voisin de $MN$ ») |
| 5°: « si un segment $(M_i, N_i)$ tend vers $(M, N)$ » | ✓ carried, a reading (question): along any filter (sequences included), the endpoints converge and the segments eventually lie in every open `U ⊇ (M, N)`; `limsup` in `EReal` |
| 6°: « $V$ est l'intérieur d'un corps convexe » | ✓ carried, literally: `V = corpsInterior K`, `IsCorpsConvexeS n K` (Déf. 11), with Mathlib's induced structure, as in Prop. 2 |
| 6°: « $l_V(M, N)$ est une fonction continue en $M$ et $N$ sur le produit $V\times V$ » | ✓ carried: the segment of `V` from `M` to `N` is unique (`isProjSegment_corpsInterior_iff`), so `l_V` is `hilbertLength K`, continuous into `EReal` and, being finite, into `ℝ` |
| 6°: « $l_V(M, N)$ est nulle si et seulement si $M=N$ » | ✓ carried |
| 7°: « $(P, \mathring{H}, \varphi, z)$ une poche de $V$ » | ✓ carried as ruled: `IsPocheProj P l φ z` (Déf. 1′, `H̊ = openHemisphere l`) and `∃ y, z y ≠ 0`, DEC-178's « z non-constant » (`IsPocheProj.exists_ne_zero_iff_nonconstant`) |
| 7°: « $K$ désigne un nombre réel supérieur à $1$ » | ⚠ weakened: dropped (any real `K`; the other hypotheses force `K > 0`) |
| 7°: `M ∈ P`, `z(φ(M)) < 1/K` | ✓ carried |
| 7°: « $(M, N)$ un segment de $V$ » with `l_V(M, N) < log K` | ⚠ weakened: the segment hypothesis is dropped (`l_V < log K < ⊤` forces it) |
| 7°: `N ∈ P` and `z φ(N) < K z(φ(M))` | ✓ carried (« $z\,\varphi(N)$ » read `z(φ(N))`, flagged in the transcription) |

## SCOPE (disclosed)

* **An assembly.** The seven properties were proved as lemmas of the strict library by the
  targets of Ch. 2 § 2, and this file assembles them into the one statement DEC-206 makes of the
  enonce: 1°–4° in `Benzecri.Chapter2.Mesure` (`pseudoLength_nonneg`, `pseudoLength_self`,
  `pseudoLength_smul`, `pseudoLength_mono`, `pseudoLength_le_opens'`), 5° and 6° in
  `Benzecri.Chapter2.Hilbert` (`propriete_cinq`, `propriete_cinq_limsup`,
  `isProjSegment_corpsInterior_iff`, `pseudoLength_eq_hilbertLength`, `continuous_hilbertLength`,
  `continuous_hilbertLength_toReal`, `hilbertLength_eq_zero_iff`), 7° in
  `Benzecri.Chapter2.Lignes` (`IsPocheProj.septieme_propriete_of_ne_zero`). Where the
  formalized proofs depart from the printed ones (5° in one chart rather than through 4° and
  Prop. 2; the implicit steps of the proof of 7°), the departure is disclosed in those modules
  and recorded on the rows of Props. 2, 3 and 6.
* **The rulings.** DEC-177 excludes dimension `0`, where 1° fails because Déf. 1 gives
  coincident points no measure (`pseudoLength_self_eq_top_dim_zero`). DEC-178 adds « z
  non-constant » to Déf. 1/1′; the strict library keeps the printed, broader, `IsPocheProj` and
  carries the hypothesis where it is used, as `∃ y, z y ≠ 0`. For a pocket the two are
  equivalent (`IsPocheProj.exists_ne_zero_iff_nonconstant`: a constant cote is `0`, its
  infimum on the nonempty `φ(P)` being `0`). Without the rulings the enonce fails in every
  dimension: `ProprietesPseudoLongueurPrinted n` (the enonce with the definitions as printed,
  on Hausdorff, connected, second countable `V`) is false for every `n`
  (`not_proprietesPseudoLongueurPrinted`): for `n = 0` by 1° on the one-point open set of
  `S(0)`, for `n ≥ 1` by 7° on the pocket `(ℝⁿ, H₀, j, 0)` of cote `0`
  (`septiemeProprietePrinted_iff`). These are the findings of OQ-45 and OQ-61, already ruled.
* **5° is a reading** (question). The paper does not say when « un segment $(M_i, N_i)$ tend
  vers $(M, N)$ ». The convergence assumed here (endpoints converge, and the segments eventually
  lie in every open set containing `(M, N)`) is implied by every usual one: Hausdorff or
  Vietoris convergence of the segments with their endpoints, or convergence of parametrisations.
  Convergence of the endpoints alone does not suffice, because two points of a manifold may be
  joined by several segments of different pseudo-lengths (argued in the REPORT, not formalized:
  a flat annulus). The neighbourhood form is the semicontinuity for the coarsest of these
  topologies on segments, so it implies the others.
* **6° is read literally**: `V` is the interior of a convex body of `S(n)`. A `V` only
  projectively isomorphic to one would need the invariance of `l_V` under projective isomorphisms
  between two manifolds, not formalized (2° is formalized for automorphisms, as printed).
* **Non-vacuity.** Every hypothesis is satisfiable: `V = S(n)`; for `n ≥ 1`, a convex body with
  two distinct interior points (`exists_ne_corpsInterior_iff`, `Benzecri.Chapter2.Prop2Literal`);
  a pocket of non-constant cote (`exists_isPocheProj_cote_ne_zero`, `n = 1`: the projective image
  of the strict shell `]0, 1[ ⊂ ]0, ∞[`).
* `exists_isPocheProj_cote_ne_zero` and `IsPocheProj.exists_ne_zero_iff_nonconstant` were written
  in parallel with T-bz-poche-nonconstant (`PocheNonConstante.lean`), which may prove the same
  facts: to be deduplicated at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v

/-! ### DEC-178: « z non-constant » is « z not identically `0` » for a pocket -/

section Cote

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **The cote of a pocket is non-constant iff it is not identically `0`**: a constant cote is `0`,
because its infimum on the nonempty `φ(P)` is `0` (condition *a*). So the hypothesis `∃ y, z y ≠ 0`
of 7° is DEC-178's « z non-constant ». -/
theorem IsPocheProj.exists_ne_zero_iff_nonconstant (hP : IsPocheProj P l φ z) :
    (∃ y, z y ≠ 0) ↔ ∃ y y', z y ≠ z y' := by
  constructor
  · rintro ⟨y, hy⟩
    by_contra h
    push Not at h
    apply hy
    obtain ⟨M, hM⟩ := hP.isConnected.nonempty
    have hS : z '' ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)) = {z y} := by
      ext t
      constructor
      · rintro ⟨y', -, rfl⟩
        exact h y' y
      · rintro rfl
        exact ⟨⟨φ M, hP.mapsTo_hemi hM⟩, ⟨M, hM, rfl⟩, h _ y⟩
    have hglb := hP.isGLB
    rw [hS] at hglb
    exact isGLB_singleton.unique hglb
  · rintro ⟨y, y', h⟩
    by_contra h0
    push Not at h0
    exact h (by rw [h0 y, h0 y'])

end Cote

section Proprietes

variable {n : ℕ} [NeZero n] (V : Type u) [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- **The properties 1°–7° of the pseudo-length** (`bzthm:c2s2_proprietes_pseudo_longueur`,
l.229–257), one statement (DEC-206), for `n ≥ 1` (DEC-177), 7° for a pocket whose cote is not
identically `0` (DEC-178). -/
theorem proprietes_pseudo_longueur :
    -- 1° `l_V(M, N) ≥ 0`, `l_V(M, M) = 0`
    ((∀ (Sg : Set V) (M N : V), 0 ≤ pseudoLength n Sg M N) ∧
      ∀ (Sg : Set V) (M : V), IsProjSegment n Sg M M → pseudoLength n Sg M M = 0) ∧
    -- 2° `l_V(gM, gN) = l_V(M, N)` for a projective automorphism `g`
    (∀ (g : GXAut (GSR n) (S n) V) (Sg : Set V) (M N : V),
      pseudoLength n ((g • ·) '' Sg) (g • M) (g • N) = pseudoLength n Sg M N) ∧
    -- 3° `(M, N) ⊂ (M', N')` implies `l_V(M, N) ≤ l_V(M', N')`
    (∀ (Sg Sg' : Set V) (M N M' N' : V), IsProjSegment n Sg M N → Sg ⊆ Sg' →
      pseudoLength n Sg M N ≤ pseudoLength n Sg' M' N') ∧
    -- 4° `l_V(M, N) ≤ l_{V'}(M, N)` for a segment included in the open `V'`
    (∀ (W : TopologicalSpace.Opens V) (Sg : Set V) (M N : V) (hM : M ∈ W) (hN : N ∈ W),
      Sg ⊆ W →
        pseudoLength n Sg M N ≤ pseudoLength n (Subtype.val ⁻¹' Sg : Set W) ⟨M, hM⟩ ⟨N, hN⟩) ∧
    -- 5° upper semicontinuity, in neighbourhoods and along a convergent family of segments
    (∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N →
      (∀ k : EReal, pseudoLength n Sg M N < k → ∃ U : Set V, IsOpen U ∧ Sg ⊆ U ∧
        ∀ᶠ p : V × V in 𝓝 (M, N), ∀ Sg' : Set V, IsProjSegment n Sg' p.1 p.2 → Sg' ⊆ U →
          pseudoLength n Sg' p.1 p.2 < k) ∧
      ∀ (ι : Type v) (F : Filter ι) (Sgs : ι → Set V) (Ms Ns : ι → V),
        (∀ i, IsProjSegment n (Sgs i) (Ms i) (Ns i)) → Tendsto Ms F (𝓝 M) →
        Tendsto Ns F (𝓝 N) → (∀ U : Set V, IsOpen U → Sg ⊆ U → ∀ᶠ i in F, Sgs i ⊆ U) →
          limsup (fun i => pseudoLength n (Sgs i) (Ms i) (Ns i)) F ≤ pseudoLength n Sg M N) ∧
    -- 6° on the interior of a convex body `K` of `S(n)`
    (∀ K : Set (S n), IsCorpsConvexeS n K →
      (∀ (M N : corpsInterior K) (Sg : Set (corpsInterior K)),
        IsProjSegment n Sg M N ↔ Sg = Subtype.val ⁻¹' Sphere.closedSeg (M : S n) N) ∧
      (∀ (M N : corpsInterior K) (Sg : Set (corpsInterior K)),
        IsProjSegment n Sg M N → pseudoLength n Sg M N = hilbertLength K M N) ∧
      Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
      Continuous (fun p : corpsInterior K × corpsInterior K => (hilbertLength K p.1 p.2).toReal) ∧
      (∀ M N : corpsInterior K, ((hilbertLength K M N).toReal : EReal) = hilbertLength K M N) ∧
      ∀ M N : corpsInterior K, hilbertLength K M N = 0 ↔ M = N) ∧
    -- 7° a pocket `(P, H̊, φ, z)` of non-constant cote
    (∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ)
      (hP : IsPocheProj P l φ z), (∃ y, z y ≠ 0) →
      ∀ (M : V) (hM : M ∈ P) (K : ℝ), z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K →
      ∀ (Sg : Set V) (N : V), pseudoLength n Sg M N < (Real.log K : EReal) →
        ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine ⟨⟨fun Sg M N => pseudoLength_nonneg Sg M N, fun Sg M h => pseudoLength_self hn h⟩,
    fun g Sg M N => pseudoLength_smul g Sg M N,
    fun Sg Sg' M N M' N' h hS => pseudoLength_mono hS h,
    fun W Sg M N hM hN hS => pseudoLength_le_opens' W hS hM hN,
    fun Sg M N h => ⟨fun k hk => propriete_cinq h hk,
      fun ι F Sgs Ms Ns hseg hM hN hS => propriete_cinq_limsup h hseg hM hN hS⟩,
    fun K hK => ⟨fun M N Sg => isProjSegment_corpsInterior_iff hK,
      fun M N Sg h => pseudoLength_eq_hilbertLength hK h, continuous_hilbertLength hK,
      (continuous_hilbertLength_toReal hK).1, (continuous_hilbertLength_toReal hK).2,
      hilbertLength_eq_zero_iff hK⟩,
    fun P l _ φ z hP hz M hM K hMK Sg N hl => hP.septieme_propriete_of_ne_zero hz hM hMK hl⟩

end Proprietes

/-! ### The enonce as printed -/

/-- **The enonce 1°–7° as printed** (l.229–257), with Déf. 1′ as printed (a cote may vanish
identically), in every dimension `n`, for the manifolds of dimension `n` (Hausdorff, connected,
second countable): each `l_V` is the pseudo-length of a segment of `V`, `(M_i, N_i)` a sequence. -/
def ProprietesPseudoLongueurPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    -- 1°
    ((∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N → 0 ≤ pseudoLength n Sg M N) ∧
      ∀ (Sg : Set V) (M : V), IsProjSegment n Sg M M → pseudoLength n Sg M M = 0) ∧
    -- 2°
    (∀ (g : GXAut (GSR n) (S n) V) (Sg : Set V) (M N : V), IsProjSegment n Sg M N →
      pseudoLength n ((g • ·) '' Sg) (g • M) (g • N) = pseudoLength n Sg M N) ∧
    -- 3°
    (∀ (Sg Sg' : Set V) (M N M' N' : V), IsProjSegment n Sg M N → IsProjSegment n Sg' M' N' →
      Sg ⊆ Sg' → pseudoLength n Sg M N ≤ pseudoLength n Sg' M' N') ∧
    -- 4°
    (∀ (W : TopologicalSpace.Opens V) (Sg : Set V) (M N : V) (hM : M ∈ W) (hN : N ∈ W),
      IsProjSegment n Sg M N → Sg ⊆ W →
        pseudoLength n Sg M N ≤ pseudoLength n (Subtype.val ⁻¹' Sg : Set W) ⟨M, hM⟩ ⟨N, hN⟩) ∧
    -- 5°
    (∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N → ∀ (Sgs : ℕ → Set V) (Ms Ns : ℕ → V),
      (∀ i, IsProjSegment n (Sgs i) (Ms i) (Ns i)) → Tendsto Ms atTop (𝓝 M) →
      Tendsto Ns atTop (𝓝 N) → (∀ U : Set V, IsOpen U → Sg ⊆ U → ∀ᶠ i in atTop, Sgs i ⊆ U) →
        limsup (fun i => pseudoLength n (Sgs i) (Ms i) (Ns i)) atTop ≤ pseudoLength n Sg M N) ∧
    -- 6°
    (∀ K : Set (S n), IsCorpsConvexeS n K →
      Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
      ∀ M N : corpsInterior K, hilbertLength K M N = 0 ↔ M = N) ∧
    -- 7°
    (∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ)
      (hP : IsPocheProj P l φ z) (M : V) (hM : M ∈ P) (K : ℝ), 1 < K →
      z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K → ∀ (Sg : Set V) (N : V),
      IsProjSegment n Sg M N → pseudoLength n Sg M N < (Real.log K : EReal) →
        ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩)

/-- **The enonce as printed holds in no dimension.** For `n = 0`, 1° fails on the one-point open
set of `S(0)` (`l(M, M) = +∞`, OQ-45); for `n ≥ 1`, 7° fails for the pocket of cote `0` on `ℝⁿ`
(OQ-61, `septiemeProprietePrinted_iff`). -/
theorem not_proprietesPseudoLongueurPrinted (n : ℕ) : ¬ ProprietesPseudoLongueurPrinted n := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨x⟩ : Nonempty (S 0) := inferInstance
    let U : TopologicalSpace.Opens (S 0) := ⟨{x}, isOpen_singleton_S0 x⟩
    haveI : ConnectedSpace U := isConnected_iff_connectedSpace.1 isConnected_singleton
    haveI : Subsingleton U := ⟨fun a b => Subtype.ext
      ((show (a : S 0) = x from a.2).trans (show (b : S 0) = x from b.2).symm)⟩
    let M : U := ⟨x, rfl⟩
    have h1 := (h U).1.2 {M} M (isProjSegment_singleton M)
    rw [pseudoLength_eq_top_dim_zero] at h1
    exact EReal.top_ne_zero h1
  · have h7 : SeptiemeProprietePrinted n :=
      fun V _ _ _ _ _ _ P l _ φ z hP M hM K hK hMK Sg N hSg hl =>
        (h V).2.2.2.2.2.2 P l φ z hP M hM K hK hMK Sg N hSg hl
    exact hn.ne' (septiemeProprietePrinted_iff.1 h7)

/-- **The hypotheses of 7° are satisfiable**: a pocket whose cote is not identically `0`, the
projective image of the strict shell `]0, 1[ ⊂ ]0, ∞[` (`exists_isCoqueStricteProj_demiDroite`). -/
theorem exists_isPocheProj_cote_ne_zero :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      @IsPocheProj 1 demiDroiteOuverte _ (projOfAff 1 demiDroiteOuverte) P
        (Sphere.lastForm 1) _ φ z ∧ ∃ y, z y ≠ 0 := by
  obtain ⟨P, φ, h, -⟩ := exists_isCoqueStricteAff_demiDroite
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm 1) (Module.finrank_fin_fun ℝ)
  refine ⟨P, _, _, h.1.1.toPocheProj e.symm, e.symm (fun _ => 1), ?_⟩
  simp

end Benzecri
