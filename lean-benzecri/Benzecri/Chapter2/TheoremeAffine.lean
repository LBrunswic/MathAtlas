import Benzecri.Chapter2.PremierAffine
import Benzecri.Chapter2.Theoreme

/-!
# Chapter 2 § 3, the affine Theorem — 2°–4° and the assembly: `P` simply connected ⇒ `V` simply connected; a shell gives a convex `φ̃(V)`; a strict shell gives a `φ̃(V)` with no line

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 255–256; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-theoreme-affine.

* `bzthm:c2s3t2_poche_balayable_affine` — `benzecri1960_ch2.tex:627` (statement l.627–641, proof
  l.643–646). Not marked: OQ-75 is open (1°'s second sentence, SCOPE). Assembled in both forms:
  `theoremeComposanteAffinePrinted` (1° in component form, with 2°–4°, every dimension) and
  `theoremeAffinePrinted_iff` (1° in the printed full form, with 2°–4°, equivalent to
  `ConnexeAffinePrinted`). Under the component-form answer to OQ-75 the row is marked with no Lean
  change; under the full-form answer the mark waits only on a proof of `ConnexeAffinePrinted`.

> Dans le cas affin, on a le
>
> **Théorème.** Soit $V$ une variété localement affine connexe balayable. Soit $(P, \varphi, z)$
> une poche de $V$.
>
> 1° Il existe une carte compatible $\tilde{\varphi}$ de $V$ sur un ouvert de $\R^n$. $P$ n'est
> autre que l'image réciproque par $\tilde{\varphi}$ de l'ensemble des points où $z<1$.
>
> 2° Si $P$ est simplement connexe, il en est de même de $V$.
>
> 3° Si $(P, \varphi, z)$ est une coque, $\tilde{\varphi}(V)$ est un convexe.
>
> 4° Si $(P, \varphi, z)$ est une coque stricte, $\tilde{\varphi}(V)$ ne contient pas de droite.
>
> *Démonstration.* Le théorème se démontre comme le précédent : il suffit de remplacer projectif
> par affin, et $S(n)$ ou $\mathring{H}$ par $\R^n$.

The proofs it points to (the projective Theorem, l.596–619), with « affin » for « projectif »:

> *Démontrons* 2°. — Soit $L$ un lacet de $V$ : il faut montrer que $L$ est homotope à un point.
> Or il existe un automorphisme de $V$ qui envoie le compact $L$ dans $P$ : comme $P$ est
> simplement connexe, $L$ est homotope à un point.
>
> *Démontrons* 3°. — Soit $M$ et $N$ deux points de $V$ : il faut montrer que, dans $V$, il existe
> un segment fermé d'extrémités $M$, $N$. Or, soit $g$ un automorphisme projectif tel que
> $gM\in P$, $gN\in P$ : il existe un segment $(gM, gN)$ puisque $\varphi(P)$ est convexe; donc il
> existe un segment $(M, N)$.
>
> *Démontrons* 4°. — […] Soit $g$ un automorphisme projectif de $V$ qui envoie dans $P$ un point
> $M$ de $L$ : […] En effet (§ 1, déf. 1′, *b*), tout point de $gL$ de cote $z$ inférieure à $1$
> appartient à $P$ : donc tous les points de $gL$ ont une cote supérieure ou égale à $0$, puisque
> la borne inférieure de $z$ sur $P$ est $0$. Mais alors, $gL$ est une droite (pour la géométrie
> affine de $\mathring{H}$) de cote constante égale à $z(M)$ et $gL$ est incluse dans $P$, ce qui
> contredit l'hypothèse faite sur $P$.

## What is proved

* 2°: `theoreme_deuxieme_affine`. 3°: `theoreme_troisieme_affine` (`φ̃(V)` convex in `ℝⁿ`), with
  the paper's segment form `exists_isAffSegment_of_coque_affine`. 4°:
  `theoreme_quatrieme_affine` (`φ̃(V)` contains no line of `ℝⁿ`). Every affine shell has a simply
  connected pocket (`simplyConnectedSpace_of_coque_affine`), so 2° applies to it.
* 3° and 4° are characterisations, for every pocket: `φ̃(V)` contains a line iff `φ(P)` does
  (`containsAffLine_range_iff_affine`, the paper's 4° argument, which never uses that `φ(P)` is
  convex); the pocket is a shell iff `φ̃(V)` is convex (`isCoqueAff_iff_convex_range_affine`), a
  strict shell iff `φ̃(V)` is convex with no line (`isCoqueStricteAff_iff_range_affine`).
* 1°'s full form for every shell: `poche_eq_preimage_of_coque_affine` and
  `isPreconnected_inter_range_of_coque_affine` (3° and `poche_eq_preimage_of_convex_affine`), so
  OQ-75 bears only on pockets that are not shells.
* The assembly: `theoreme_poche_balayable_affine` (general `V`); over the paper's manifolds,
  `TheoremeComposanteAffinePrinted`, `theoremeComposanteAffinePrinted`, `TheoremeAffinePrinted`,
  `theoremeAffinePrinted_iff`, and the literal reading `TheoremeAffineLiteralPrinted`,
  `TheoremeAffinePrinted.literal`.
* Non-vacuity: `theoreme_poche_balayable_affine_demiEspace` (the half-space of `ℝⁿ⁺¹`, the shell
  `{0 < x₀ < 1} ≠ V`, a non-constant cote, every hypothesis of 1°–3° met) and
  `theoreme_poche_balayable_affine_demiDroite` (`]0, ∞[` with the strict shell `]0, 1[ ≠ V`, every
  hypothesis of 1°–4° met).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement affine » | ⚠ weakened: `[ChartedSpace (Fin n → ℝ) V]`, `[HasGroupoid V (affGroupoid n)]`; Hausdorff and second countable never used (the printed forms carry them) |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the pocket makes `V` nonempty) |
| `V` balayable | ✓ carried: `IsBalayable (GAR n) (Fin n → ℝ) V` (Ch. 1 Déf. 15, all affine automorphisms) |
| `(P, φ, z)` une poche de `V` | ✓ carried: `IsPocheAff P φ z` (Déf. 1) |
| the dimension | ✓ every `n`, `n = 0` included |
| 2°: « $P$ est simplement connexe » | ✓ carried: `SimplyConnectedSpace P` (Mathlib) |
| 3°: « $(P, \varphi, z)$ est une coque » | ✓ carried: `IsCoqueAff P φ z` (Déf. 2) |
| 4°: « une coque stricte » | ✓ carried: `IsCoqueStricteAff P φ z` (Déf. 3); ⚠ weakened in `containsAffLine_range_iff_affine`: any pocket with no line in `φ(P)` |
| 2°: « il en est de même de $V$ » | ✓ carried: `SimplyConnectedSpace V` |
| 3°: « $\tilde\varphi(V)$ est un convexe » | ✓ carried: `Convex ℝ (range φ̃)` (Mathlib; `isAffConvex_iff_convex`) |
| 4°: « $\tilde\varphi(V)$ ne contient pas de droite » | ✓ carried: `¬ ContainsAffLine (Fin n → ℝ) (range φ̃)` (the notion of Déf. 3) |

## SCOPE (disclosed)

* **1°'s second sentence** is carried in component form (`theoreme_premier_affine`,
  T-bz-c2-premier-affine); the printed full form is equivalent to `ConnexeAffinePrinted`, proved
  for `z ≡ 0`, for `φ̃(V)` star-shaped about a point of cote `< 1`, for `n ≤ 1` and, here, for every
  shell; open otherwise
  (OQ-75, the twin of OQ-71). 2°–4° do not use it: after 1°c the paper sets `φ̃ = id` and argues by
  Prop. 7′ and condition *b* only.
* **« induisant $\varphi$ sur $P$ »** is not printed in the affine 1°; it is read as present, as in
  `Benzecri.Chapter2.PremierAffine` (SCOPE there: l.184–185 and l.644–645 settle it). The literal
  form follows (`TheoremeAffinePrinted.literal`).
* **The route.** « comme le précédent » is re-run over `GA(n, ℝ)` directly, not derived from the
  projective Theorem through `GXAut.affToProj`: the projective `φ̃` of `projOfAff` need not land in
  the hemisphere `j(ℝⁿ)` before the affine 1° is known. Prop. 7′ (`compact_dans_poche_affine`,
  `deux_points_dans_poche_affine`) replaces Prop. 7, and the rigidity of `GA(n, ℝ)`
  (`IsDeveloping.existsUnique_smul_eq`) gives `φ̃ ∘ g = A ∘ φ̃`.
* **4°, affine.** « remplacer $S(n)$ ou $\mathring{H}$ par $\R^n$ » turns the projective 4° into its
  second step only: the demi-droite lemma (l.605–607) has no affine counterpart to prove, since the
  hypothesis to refute is a line `L ⊆ φ̃(V)` itself. As printed: `g` moves a point `M` of `L` into
  `P`, `A(L)` is a line of `φ̃(V)` through `φ(gM)`; condition *b* along its sub-segments from `gM`
  (segments of `V` through the chart `φ̃`, `isAffSegment_of_chart`), the cote bounded below by `0`
  where `< 1`, so constant, and `A(L) ⊆ φ(P)`, against Déf. 3. Neither the convexity of `φ(P)`
  nor that of `φ̃(V)` is used, so the argument is stated for every pocket
  (`containsAffLine_range_iff_affine`) and 4° is its instance at a strict shell.
* The converses of 3° and 4° (`isCoqueAff_iff_convex_range_affine`,
  `isCoqueStricteAff_iff_range_affine`) are not in the paper; they are proved here as extras.
* **`[sic]`, not a finding**: « $z(M)$ » (l.618) is read « $z(gM)$ » (the transcription's comment
  l.620), inherited by « comme le précédent ».

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology unitInterval
open scoped Pointwise

namespace Benzecri

universe u

/-! ### 2°–4°, affine -/

section TheoremeAffine

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]
  {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}

/-- **2°, affine** (`bzthm:c2s3t2_poche_balayable_affine`, l.635, proof « comme le précédent »,
l.596–598): in a connected sweepable locally affine `V` with a pocket `(P, φ, z)`, if `P` is simply
connected, so is `V`. -/
theorem theoreme_deuxieme_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) (hsc : SimplyConnectedSpace P) : SimplyConnectedSpace V := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : ConnectedSpace V := { toNonempty := ⟨x₀⟩ }
  haveI : LocPathConnectedSpace V := locPathConnectedSpace_of_aff (n := n)
  haveI : PathConnectedSpace V := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  -- Prop. 7′: an affine automorphism `g` moves the compact `L = γ(I)` into `P`
  obtain ⟨g, -, hg⟩ := compact_dans_poche_affine (G := ⊤) hbal hP (isCompact_range γ.continuous)
  have hgγ : ∀ t, g • γ t ∈ P := fun t => hg (smul_mem_smul_set (mem_range_self t))
  -- the loop `g L` is null-homotopic in `P`, hence in `V`
  have hPsc : IsSimplyConnected P := hsc
  obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.1 hPsc).2 (g • x)
    (γ.map (continuous_const_smul g)) hgγ
  have h1 : (γ.map (continuous_const_smul g)).Homotopic (Path.refl (g • x)) := ⟨F⟩
  -- and `g⁻¹` carries the null-homotopy back to `L`
  have h2 := h1.map ⟨fun y => g⁻¹ • y, continuous_const_smul _⟩
  exact path_homotopic_refl_of_eq (inv_smul_smul g x) γ _ _
    (fun t => inv_smul_smul g (γ t)) (fun _ => rfl) h2

/-- **3°, affine** (l.637, proof « comme le précédent », l.600–603): if the pocket is a shell
(`φ(P)` convex), then `φ̃(V)` is convex, for the chart `φ̃` of 1° (every developing map equal to
`φ` on `P`). -/
theorem theoreme_troisieme_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hC : IsCoqueAff P φ z) {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p)
    (hpφ : EqOn p φ P) : Convex ℝ (range p) := by
  have hP := hC.1
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  rw [convex_iff_segment_subset]
  rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩ y hy
  -- `g` with `gM, gN ∈ P` (Prop. 7′, second assertion), `A` with `φ̃ ∘ g = A ∘ φ̃`
  obtain ⟨g, -, hgM, hgN⟩ := deux_points_dans_poche_affine (G := ⊤) hbal hP M N
  have hpg : IsDeveloping (GAR n) (fun y => p (g • y)) :=
    isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
  obtain ⟨A, hA, -⟩ := hp.existsUnique_smul_eq hpg
  -- the segment `(gM, gN)` lies in the convex `φ(P)`
  have hseg : segment ℝ (A • p M) (A • p N) ⊆ φ '' P := by
    rw [← hA M, ← hA N, hpφ hgM, hpφ hgN]
    exact hC.2.segment_subset (mem_image_of_mem φ hgM) (mem_image_of_mem φ hgN)
  have hAy : A • y ∈ φ '' P := by
    apply hseg
    have h := mem_image_of_mem A.toAffineMap hy
    rw [image_segment] at h
    exact h
  -- so `(M, N) = A⁻¹ (gM, gN) ⊆ φ̃(g⁻¹ P)`
  obtain ⟨Q, hQ, hQy⟩ := hAy
  refine ⟨g⁻¹ • Q, ?_⟩
  apply MulAction.injective A
  show A • p (g⁻¹ • Q) = A • y
  rw [← hA, smul_inv_smul, hpφ hQ, hQy]

/-- **3°, affine, in the form its proof states** (l.600–601, « il faut montrer que, dans $V$, il
existe un segment fermé d'extrémités $M$, $N$ »): if the pocket is a shell, any two points of `V`
are the ends of a segment of `V` (Ch. 1, Déf. 14). -/
theorem exists_isAffSegment_of_coque_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hC : IsCoqueAff P φ z) (M N : V) :
    ∃ Sg : Set V, IsAffSegment n Sg M N := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche_affine hbal hC.1
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have ht : φ'.target = range φ' := by rw [← φ'.image_source_eq_target, hs, image_univ]
  have hsub : segment ℝ (φ' M) (φ' N) ⊆ φ'.target := by
    rw [ht]
    exact (theoreme_troisieme_affine hbal hC hp hφ'φ).segment_subset (mem_range_self M)
      (mem_range_self N)
  have hseg := isAffSegment_of_chart hφ' hsub
  rw [φ'.left_inv (hs.symm ▸ mem_univ M), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
  exact ⟨_, hseg⟩

/-- **4°'s argument, for every pocket** (l.609–619 with « affin » for « projectif »): `φ̃(V)`
contains a line of `ℝⁿ` iff `φ(P)` does. One way `φ(P) ⊆ φ̃(V)`; the other is the paper's
argument: `g` moves a point `M` of the line `L` into `P`, `A(L)` is a line of `φ̃(V)` through
`φ(gM)` (`φ̃ ∘ g = A ∘ φ̃`), condition *b* along its sub-segments puts its points of cote `< 1` in
`φ(P)`, where `z ≥ 0`, so `z` is constant `< 1` on `A(L)` and `A(L) ⊆ φ(P)`. The convexity of
`φ(P)` is not used. -/
theorem containsAffLine_range_iff_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    ContainsAffLine (Fin n → ℝ) (range p) ↔ ContainsAffLine (Fin n → ℝ) (φ '' P) := by
  refine ⟨?_, fun ⟨L, hL, hLP⟩ => ⟨L, hL, hLP.trans ?_⟩⟩
  swap
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hpφ hx⟩
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  -- `φ̃` is a chart with source `V` (1°b)
  obtain ⟨φ', hφ', hs, ht, he⟩ := PremierGX.exists_chart_of_injective hp
    (injective_of_isDeveloping_of_poche_affine hbal hP hp)
  subst he
  -- a line `L = q₀ + ℝ w` of `φ̃(V)`, and a point `M` of `V` over `q₀`
  rintro ⟨L, ⟨q₀, w, hw, rfl⟩, hL⟩
  obtain ⟨M, hM⟩ : q₀ ∈ range φ' := hL ⟨0, by simp⟩
  -- `g` moving `M` into `P` (Prop. 7′), `A` with `φ̃ ∘ g = A ∘ φ̃`
  obtain ⟨g, -, hgM, -⟩ := deux_points_dans_poche_affine (G := ⊤) hbal hP M M
  have hpg : IsDeveloping (GAR n) (fun y => φ' (g • y)) :=
    isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
  obtain ⟨A, hA, -⟩ := hp.existsUnique_smul_eq hpg
  -- `A(L)` is the line `φ(gM) + ℝ u` of `φ̃(V)`, `u = A w ≠ 0`
  set u : Fin n → ℝ := A.linear w with hu
  have hu0 : u ≠ 0 := fun h => hw (A.linear.injective (h.trans (map_zero _).symm))
  have hAL : ∀ t : ℝ, t • u + φ' (g • M) ∈ range φ' := by
    intro t
    obtain ⟨N, hN⟩ := hL ⟨t, rfl⟩
    refine ⟨g • N, ?_⟩
    rw [hA N, hN, hA M, hM, affineEquiv_smul_def, affineEquiv_smul_def, A.map_vadd, map_smul,
      vadd_eq_add]
  -- condition `b` along the segment `(gM, N_t)` of `V`: its points of cote `< 1` are in `φ(P)`
  have hgerm : (φ' : V → Fin n → ℝ) =ᶠ[𝓝 (g • M)] φ :=
    Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hgM) hpφ
  have hb : ∀ t : ℝ, z (t • u + φ' (g • M)) < 1 → t • u + φ' (g • M) ∈ φ '' P := by
    intro t hzt
    obtain ⟨N, hN⟩ := hAL t
    have hsub : segment ℝ (φ' (g • M)) (φ' N) ⊆ φ'.target := by
      rw [ht, hN, segment_eq_image']
      rintro _ ⟨θ, -, rfl⟩
      convert hAL (θ * t) using 1
      show φ' (g • M) + θ • (t • u + φ' (g • M) - φ' (g • M)) = (θ * t) • u + φ' (g • M)
      rw [add_sub_cancel_right, smul_smul, add_comm]
    have hseg := isAffSegment_of_chart hφ' hsub
    rw [φ'.left_inv (hs.symm ▸ mem_univ _), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
    have hNP : N ∈ P := hP.mem_of_segment _ (g • M) N hseg hgM φ' hφ'
      (hs.symm ▸ subset_univ _) hgerm (by rw [hN]; exact hzt)
    exact ⟨N, hNP, by rw [← hpφ hNP, hN]⟩
  -- there `z ≥ 0` (condition `a`), so the affine `z` is constant on `A(L)`, `= z(φ(gM)) < 1`
  have hz0 : ∀ t : ℝ, z (t • u + φ' (g • M)) < 1 → 0 ≤ z (t • u + φ' (g • M)) := fun t hzt =>
    hP.isGLB.1 ⟨_, hb t hzt, rfl⟩
  have hzq : z (φ' (g • M)) < 1 := by
    rw [hpφ hgM]
    exact hP.cote_lt_one hgM
  have hcz : ∀ t : ℝ, z (t • u + φ' (g • M)) = t * z.linear u + z (φ' (g • M)) := fun t => by
    rw [← vadd_eq_add, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
  have hc : z.linear u = 0 := by
    by_contra hne
    have h1 := hz0 (-(z (φ' (g • M)) + 1) / z.linear u)
      (by rw [hcz, div_mul_cancel₀ _ hne]; linarith)
    rw [hcz, div_mul_cancel₀ _ hne] at h1
    linarith
  -- so the whole line `A(L)` is in `φ(P)`
  refine ⟨range fun t : ℝ => t • u +ᵥ φ' (g • M), ⟨φ' (g • M), u, hu0, rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hb t (by rw [hcz, hc, mul_zero, zero_add]; exact hzq)

/-- **4°, affine** (l.639–640, proof « comme le précédent », l.609–619): if the pocket is a strict
shell, then `φ̃(V)` contains no line of `ℝⁿ`, for the chart `φ̃` of 1° (every developing map equal
to `φ` on `P`). -/
theorem theoreme_quatrieme_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hC : IsCoqueStricteAff P φ z) {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p)
    (hpφ : EqOn p φ P) : ¬ ContainsAffLine (Fin n → ℝ) (range p) := fun h =>
  hC.2 ((containsAffLine_range_iff_affine hbal hC.1.1 hp hpφ).1 h)

/-- **3° is a characterisation**: the pocket is a shell iff `φ̃(V)` is convex. The converse: for a
convex `φ̃(V)`, `φ(P) = {z < 1} ∩ φ̃(V)` (1°'s full form, `poche_eq_preimage_of_convex_affine`),
which is convex. -/
theorem isCoqueAff_iff_convex_range_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    IsCoqueAff P φ z ↔ Convex ℝ (range p) := by
  refine ⟨fun hC => theoreme_troisieme_affine hbal hC hp hpφ, fun hconv => ⟨hP, ?_⟩⟩
  have hfull := poche_eq_preimage_of_convex_affine hbal hP hp hpφ hconv
  have h1 : φ '' P = {y | z y < 1} ∩ range p :=
    calc φ '' P = p '' P := (image_congr hpφ).symm
      _ = p '' (p ⁻¹' ({y | z y < 1} ∩ range p)) := by rw [← hfull]
      _ = {y | z y < 1} ∩ range p := image_preimage_eq_of_subset inter_subset_right
  rw [h1]
  exact ((convex_Iio (1 : ℝ)).affine_preimage z).inter hconv

/-- **3° and 4° together are a characterisation**: the pocket is a strict shell iff `φ̃(V)` is a
convex part of `ℝⁿ` containing no line. -/
theorem isCoqueStricteAff_iff_range_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    IsCoqueStricteAff P φ z ↔
      Convex ℝ (range p) ∧ ¬ ContainsAffLine (Fin n → ℝ) (range p) := by
  rw [IsCoqueStricteAff, isCoqueAff_iff_convex_range_affine hbal hP hp hpφ,
    containsAffLine_range_iff_affine hbal hP hp hpφ]

omit [HasGroupoid V (affGroupoid n)] in
/-- **The pocket of an affine shell is simply connected**: `P` is homeomorphic through `φ` to the
nonempty convex `φ(P)` of `ℝⁿ`. So 2° applies to every shell. -/
theorem simplyConnectedSpace_of_coque_affine (hC : IsCoqueAff P φ z) : SimplyConnectedSpace P := by
  have hP := hC.1
  have htgt : φ '' P = φ.target := by rw [← hP.source_eq, φ.image_source_eq_target]
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : ContractibleSpace φ.target :=
    (htgt ▸ hC.2 : Convex ℝ φ.target).contractibleSpace ⟨φ x₀, htgt ▸ mem_image_of_mem φ hx₀⟩
  let e : P ≃ₜ φ.target := (Homeomorph.setCongr hP.source_eq.symm).trans φ.toHomeomorphSourceTarget
  exact e.symm.toHomotopyEquiv.symm.simplyConnectedSpace

/-- **1°'s full form for every shell**: `{z < 1} ∩ φ̃(V)` is preconnected, since `φ̃(V)` is convex
(3°). -/
theorem isPreconnected_inter_range_of_coque_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hC : IsCoqueAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    IsPreconnected ({y | z y < 1} ∩ range p) := by
  exact (((convex_Iio (1 : ℝ)).affine_preimage z).inter
    (theoreme_troisieme_affine hbal hC hp hpφ)).isPreconnected

/-- **1°'s full form for every shell**: `P = φ̃⁻¹({z < 1} ∩ φ̃(V))` (3° and
`poche_eq_preimage_of_convex_affine`). -/
theorem poche_eq_preimage_of_coque_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hC : IsCoqueAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    P = p ⁻¹' ({y | z y < 1} ∩ range p) := by
  exact poche_eq_preimage_of_convex_affine hbal hC.1 hp hpφ
    (theoreme_troisieme_affine hbal hC hp hpφ)

/-- **The affine Theorem** (`bzthm:c2s3t2_poche_balayable_affine`, l.627–641), 1° in component
form with 2°–4°: a connected sweepable locally affine `V` with a pocket `(P, φ, z)` has a
compatible chart `φ̃` with source `V`, inducing `φ` on `P`; `P` is the connected component of each
of its points in `φ̃⁻¹(z < 1)`, `P = φ̃⁻¹({z < 1} ∩ φ̃(V))` iff `{z < 1} ∩ φ̃(V)` is preconnected,
and it holds when the pocket is a shell (1°); if `P` is simply connected so is `V` (2°); if the
pocket is a shell, `φ̃(V)` is convex (3°); if it is a strict shell, `φ̃(V)` contains no line
(4°). -/
theorem theoreme_poche_balayable_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) :
    ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P ∧
      (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' {y | z y < 1}) x) ∧
      (P = φ' ⁻¹' ({y | z y < 1} ∩ range φ') ↔ IsPreconnected ({y | z y < 1} ∩ range φ')) ∧
      (IsCoqueAff P φ z → P = φ' ⁻¹' ({y | z y < 1} ∩ range φ')) ∧
      (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
      (IsCoqueAff P φ z → Convex ℝ (range φ')) ∧
      (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) (range φ')) := by
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, hiff⟩ := theoreme_premier_affine hbal hP
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact ⟨φ', hφ', hs, hφ'φ, hcomp, hiff,
    fun hC => poche_eq_preimage_of_coque_affine hbal hC hp hφ'φ, theoreme_deuxieme_affine hbal hP,
    fun hC => theoreme_troisieme_affine hbal hC hp hφ'φ,
    fun hC => theoreme_quatrieme_affine hbal hC hp hφ'φ⟩

end TheoremeAffine

/-! ### The printed statements, over the paper's manifolds -/

/-- **The affine Theorem with 1° in component form** (« $P$ n'est autre que » read as a connected
component, the forward reference l.181–186, « resp. affine »), 2°–4° as printed, over the paper's
manifolds (Hausdorff, connected, second countable; `V : Type`), the chart inducing `φ` on `P`. -/
def TheoremeComposanteAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
        (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' {y | z y < 1}) x) ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
        (IsCoqueAff P φ z → Convex ℝ (range φ')) ∧
        (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) (range φ'))

/-- **The affine Theorem as printed** (1° with « $P=\tilde{\varphi}^{-1}(\{z<1\}\cap
\tilde{\varphi}(V))$ », l.632–633 and the projective l.586; 2°–4°), over the paper's manifolds, the
chart inducing `φ` on `P`. Equivalent to `ConnexeAffinePrinted n` (`theoremeAffinePrinted_iff`),
open only for a pocket that is not a shell, with a non-constant cote, in dimension `n ≥ 2`
(`poche_eq_preimage_of_coque_affine`; OQ-75). -/
def TheoremeAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
        P = φ' ⁻¹' ({y | z y < 1} ∩ range φ') ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
        (IsCoqueAff P φ z → Convex ℝ (range φ')) ∧
        (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) (range φ'))

/-- **The affine Theorem literally as printed**: no « induisant $\varphi$ sur $P$ », so only SOME
compatible chart `φ̃` with source `V`, the full form of 1° and 2°–4° for it. Weaker than
`TheoremeAffinePrinted` (`TheoremeAffinePrinted.literal`). -/
def TheoremeAffineLiteralPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧
        P = φ' ⁻¹' ({y | z y < 1} ∩ range φ') ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
        (IsCoqueAff P φ z → Convex ℝ (range φ')) ∧
        (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) (range φ'))

/-- **The affine Theorem with 1° in component form holds in every dimension**, `n = 0`
included. -/
theorem theoremeComposanteAffinePrinted (n : ℕ) : TheoremeComposanteAffinePrinted n := by
  intro V _ _ _ _ _ _ hbal P φ z hP
  obtain ⟨φ', h1, h2, h3, h4, -, -, h5, h6, h7⟩ := theoreme_poche_balayable_affine hbal hP
  exact ⟨φ', h1, h2, h3, h4, h5, h6, h7⟩

/-- **The affine Theorem as printed is exactly the connectedness the proof of 1°c presumes**:
`TheoremeAffinePrinted n ↔ ConnexeAffinePrinted n` (2°–4° hold unconditionally). -/
theorem theoremeAffinePrinted_iff (n : ℕ) : TheoremeAffinePrinted n ↔ ConnexeAffinePrinted n := by
  constructor
  · intro h
    rw [← premierAffinePrinted_iff]
    intro V _ _ _ _ _ _ hbal P φ z hP
    obtain ⟨φ', h1, h2, h3, h4, -⟩ := h V hbal P φ z hP
    exact ⟨φ', h1, h2, h3, h4⟩
  · intro h V _ _ _ _ _ _ hbal P φ z hP
    obtain ⟨φ', h1, h2, h3, -, hiff, -, h5, h6, h7⟩ := theoreme_poche_balayable_affine hbal hP
    exact ⟨φ', h1, h2, h3, hiff.2 (h V hbal P φ z hP φ' h1 h2 h3), h5, h6, h7⟩

/-- The reading with « induisant $\varphi$ sur $P$ » implies the literal one. -/
theorem TheoremeAffinePrinted.literal {n : ℕ} (h : TheoremeAffinePrinted n) :
    TheoremeAffineLiteralPrinted n := by
  intro V _ _ _ _ _ _ hbal P φ z hP
  obtain ⟨φ', h1, h2, -, h4, h5, h6, h7⟩ := h V hbal P φ z hP
  exact ⟨φ', h1, h2, h4, h5, h6, h7⟩

/-! ### Non-vacuity -/

/-- **The affine Theorem on a shell with a non-constant cote and `P ≠ V`, in every dimension
`n + 1 ≥ 1`**: the open half-space `{x₀ > 0}` of `ℝⁿ⁺¹`, sweepable by its affine automorphisms,
with the shell `P = {0 < x₀ < 1}` (cote `z = x₀`); `P` is simply connected; the chart `φ̃` of 1°
exists, `P` is the connected component of each of its points in `φ̃⁻¹(z < 1)` and
`P = φ̃⁻¹({z < 1} ∩ φ̃(V))`, `V` is simply connected (2°) and `φ̃(V)` is convex (3°). -/
theorem theoreme_poche_balayable_affine_demiEspace (n : ℕ) :
    ∃ φ : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
      IsCoqueAff {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ≠ univ ∧
      (∃ y, (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y ≠ 0) ∧
      SimplyConnectedSpace {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
      ∃ φ' : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
        IsCompatibleChart (GAR (n + 1)) φ' ∧ φ'.source = univ ∧
        EqOn φ' φ {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
        (∀ x ∈ {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1},
          {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} = connectedComponentIn
            (φ' ⁻¹' {y | (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1}) x) ∧
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} = φ' ⁻¹'
          ({y | (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1} ∩ range φ') ∧
        SimplyConnectedSpace (demiEspaceOuvert n) ∧ Convex ℝ (range φ') := by
  obtain ⟨φ, hP, -, himg⟩ := exists_isPocheAff_demiEspace n
  have hC : IsCoqueAff {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
      (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap :=
    ⟨hP, by
      rw [himg]
      exact (convex_Ioo (0 : ℝ) 1).linear_preimage
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)⟩
  have hsc := simplyConnectedSpace_of_coque_affine hC
  obtain ⟨φ', h1, h2, h3, h4, -, h4', h5, h6, -⟩ :=
    theoreme_poche_balayable_affine (isBalayable_demiEspaceOuvert n) hP
  refine ⟨φ, hC, ?_, ⟨fun _ => 1, ?_⟩, hsc, φ', h1, h2, h3, h4, h4' hC, h5 hsc, h6 hC⟩
  · intro h
    have h2 : (⟨fun _ => 2, show (0 : ℝ) < 2 by norm_num⟩ : demiEspaceOuvert n) ∈
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} := h ▸ mem_univ _
    exact absurd (show (2 : ℝ) < 1 from h2) (by norm_num)
  · show (1 : ℝ) ≠ 0
    exact one_ne_zero

/-- **The affine Theorem on a strict shell with `P ≠ V`** (`n = 1`): the half-line `]0, ∞[`,
sweepable by its affine automorphisms (the half-space `demiEspaceOuvert 0`), with the strict shell
`P = ]0, 1[` of `exists_isCoqueStricteAff_demiDroite_ne_univ`; `P` is simply connected; the chart
`φ̃` of 1° exists, `V` is simply connected (2°), `φ̃(V)` is convex (3°) and contains no line
(4°). -/
theorem theoreme_poche_balayable_affine_demiDroite :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ)),
      IsCoqueStricteAff P φ (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧ P ≠ univ ∧
      SimplyConnectedSpace P ∧
      ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ), IsCompatibleChart (GAR 1) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧
        P = φ' ⁻¹' ({y | (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1} ∩
          range φ') ∧
        SimplyConnectedSpace demiDroiteOuverte ∧ Convex ℝ (range φ') ∧
        ¬ ContainsAffLine (Fin 1 → ℝ) (range φ') := by
  obtain ⟨P, φ, hC, hne⟩ := exists_isCoqueStricteAff_demiDroite_ne_univ
  -- `]0, ∞[` is the half-space `demiEspaceOuvert 0`, sweepable by its affine automorphisms
  have hbal : IsBalayable (GAR 1) (Fin 1 → ℝ) demiDroiteOuverte := isBalayable_demiEspaceOuvert 0
  have hconv : IsPreconnected ((demiDroiteOuverte : Set (Fin 1 → ℝ))) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).isPreconnected
  haveI : PreconnectedSpace demiDroiteOuverte := Subtype.preconnectedSpace hconv
  have hsc := simplyConnectedSpace_of_coque_affine hC.1
  obtain ⟨φ', h1, h2, h3, -, -, h4, h5, h6, h7⟩ := theoreme_poche_balayable_affine hbal hC.1.1
  exact ⟨P, φ, hC, hne, hsc, φ', h1, h2, h3, h4 hC.1, h5 hsc, h6 hC.1, h7 hC⟩

end Benzecri
