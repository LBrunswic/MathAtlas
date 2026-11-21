import Benzecri.Chapter2.Compact
import Benzecri.Chapter2.Hemisphere

/-!
# Chapter 2 § 3, the Theorem's 1° (projective) — a connected sweepable locally projective manifold with a pocket has a compatible chart onto an open set of `S(n)` extending the pocket's chart, and the pocket is a connected component of the preimage of `z < 1`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 253–255; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-developpement (DEC-137).

* `bzthm:c2s3t1_poche_balayable` — `benzecri1960_ch2.tex:517`, its 1° only (statement l.522–524,
  proof l.535–590). Not marked: the row is assembled by T-bz-c2-theoreme, and the second sentence
  of 1° is proved here in its component form only (SCOPE).

> **Théorème.** Soit $V$ une variété localement projective connexe balayable. Soit
> $(P, \mathring{H}, \varphi, z)$ une poche de $V$.
>
> 1° Il existe une carte compatible $\tilde{\varphi}$ de $V$ sur un ouvert de $S(n)$, induisant
> $\varphi$ sur $P$. $P$ n'est autre que l'image réciproque par $\tilde{\varphi}$ de l'ensemble des
> points de $\mathring{H}$ où $z<1$.
>
> […] La démonstration du 1° va se décomposer en trois points.
>
> *a*. Il existe une application $\tilde{\varphi}$ de $V$ sur $S(n)$, coïncidant avec $\varphi$
> sur $P$, et dont le germe en tout point de $V$ appartient à $J(V)$ (cf. chap. 1, § 1, déf. 12).
>
> Il faut montrer que le revêtement $J(V)$ de $V$ est isomorphe à un produit : $\tilde{\varphi}$ a
> pour germes la composante connexe dans $J(V)$ des germes de $\varphi$.
>
> Soit $[j, j']$ un chemin de $J(V)$, dont la projection sur $V$ par l'application source soit un
> lacet $[M, M]$. Nous allons montrer que $j=j'$. D'après la proposition 7 du paragraphe 2, il
> existe un automorphisme projectif $g$ de $V$, tel que l'image par $g$ du lacet $[M, M]$ soit dans
> $P$, $g[M, M]\subset P$. Considérons maintenant le lacet de $J(V)$ obtenu à partir du lacet
> $[j, j']$ et composant chaque jet avec l'automorphisme $g^{-1}$ : on obtient un lacet de $J(V)$
> se projetant par l'application source sur le lacet $g[M, M]$, inclus dans $P$. Mais $P$ est
> isomorphe par $\varphi$ à un ouvert de $S(n)$ : donc la restriction à $P$ de $J(V)$ est un
> produit, et tout chemin de $J(V)$ se projetant sur le lacet $g[M, M]\subset P$ est fermé. Le
> chemin $[j, j']$ dont l'image par l'automorphisme $g^{-1}$ de $J(V)$ est fermé est donc fermé.
> L'assertation $a$ en résulte immédiatement.
>
> *b*. L'application définie en $a$ de $V$ sur $S(n)$ est une carte compatible.
>
> $\tilde{\varphi}$ est un homéomorphisme local : il faut montrer que $\tilde{\varphi}$ est un
> homéomorphisme global, c'est-à-dire que deux points distincts $M$ et $N$ de $V$ ont par
> $\tilde{\varphi}$ des images distinctes.
>
> Soit $g$ un automorphisme projectif de $V$ : nous désignerons par $\gamma$ l'automorphisme de
> $S(n)$ ($\gamma\in GS(n, \R)$) tel que $\tilde{\varphi}\circ g=\gamma\circ\tilde{\varphi}$ […].
> Choisissons $g$ tel que $gM\in P$; $gN\in P$. Puisque $M\neq N$, on a $gM\neq gN$; et, puisque
> la restriction de $\tilde{\varphi}$ à $P$ est un homéomorphisme, on a
> $\tilde{\varphi}\circ gM\neq\tilde{\varphi}\circ gN$. Mais il en résulte que
> $\gamma\circ\tilde{\varphi}M\neq\gamma\circ\tilde{\varphi}N$ et donc que
> $\tilde{\varphi}M\neq\tilde{\varphi}N$. ce que nous voulions démontrer.
>
> *c*. $P$ est l'image réciproque par $\tilde{\varphi}$ de l'ensemble $D$ des points de
> $\mathring{H}$, où $z<1$. Montrons que $P=\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$. Soit
> $M\in\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$ nous : allons montrer que $M\in P$. Soit
> $N\in P$; on peut construire dans $D\cap\tilde{\varphi}(V)$ une ligne brisée allant de
> $\tilde{\varphi}(M)$ à $\tilde{\varphi}(N)$. De la condition $b$ de la définition des poches, il
> résulte que $M$ appartient à $P$.

And the forward reference after the examples of § 1 (l.181–186): « Nous verrons (§ 3, théorème)
que, si $V$ est une variété localement projective (resp. affine) connexe balayable, possédant une
poche $(P, \mathring{H}, \varphi, z)$ [resp. $(P, \varphi, z)$], on est toujours dans la situation
considérée en exemple. $\varphi$ se prolonge en une application projective (resp. affine) de $V$
sur $S(n)$ (resp. $\R^n$) et $P$ n'est autre qu'une composante connexe de l'image réciproque par
$\varphi$ du demi-espace ouvert de $\mathring{H}$ (resp. $\R^n$) d'équation $z<1$. »

## What is proved (no `sorry`)

* 1°a: `exists_isDeveloping_eqOn_poche` (a map `φ̃` all of whose jets lie in `J(V)`, equal to `φ`
  on `P`); the paper's key step, a path of `J(V)` over a loop is closed: `chemin_jets_ferme`; the
  product, as a bijection: `jets_produit`.
* 1°b: `injective_of_isDeveloping_of_poche`, for EVERY developing map of `V`; the chart:
  `exists_chart_poche`; it is unique: `IsDeveloping.eq_of_eqOn_poche`.
* 1°c, component form: `poche_eq_connectedComponentIn`. The full form: `poche_eq_preimage_iff`
  (it holds iff `D ∩ φ̃(V)` is preconnected), `poche_eq_preimage_of_cote_eq_zero` (it holds for the
  constant cote). Not proved for a non-constant cote.
* 1° in one piece: `theoreme_premier`. Printed forms: `premierComposantePrinted n` for every `n`;
  `premierPrinted_iff n` (the printed full form `PremierPrinted n` is equivalent to
  `ConnexePrinted n`, the connectedness the proof presumes).
* The forward reference l.181–186: `situation_exemple`. OQ-46's alternative reading:
  `exemple_poche_projective_of_poche`.
* Non-vacuity: `theoreme_premier_model` (`ℝⁿ`, every `n`, cote `0`, `P = V`) and
  `theoreme_premier_demiDroite` (`]0, ∞[`, its homotheties, `P = ]0, 1[ ≠ V`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement projective » | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]`; Hausdorff and second countable never used (the printed forms carry them) |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the pocket makes `V` nonempty) |
| `V` balayable | ✓ carried: `IsBalayable (GSR n) (S n) V` (Ch. 1, Déf. 15: for the group of all projective automorphisms) |
| `(P, H̊, φ, z)` une poche de `V` | ✓ carried: `IsPocheProj P l φ z` (Déf. 1′, strict), `H̊` given by its equation `l ≠ 0` |
| the dimension | ✓ every `n`, `n = 0` included (no `NeZero n`) |
| 1°: « une carte compatible $\tilde\varphi$ de $V$ sur un ouvert de $S(n)$, induisant $\varphi$ sur $P$ » | ✓ carried: `OpenPartialHomeomorph` (open target), `IsCompatibleChart`, `source = univ`, `EqOn φ̃ φ P` |
| 1°: « $P$ n'est autre que l'image réciproque par $\tilde\varphi$ de … $z<1$ » | component form; full form open for a non-constant cote (SCOPE) |

## SCOPE (disclosed)

* **1°c, the full form `P = φ̃⁻¹(D ∩ φ̃(V))` is not proved for a non-constant cote.** The proof
  (l.587–590) builds « dans $D\cap\tilde{\varphi}(V)$ une ligne brisée » from $\tilde\varphi(M)$
  to $\tilde\varphi(N)$, which presumes $D\cap\tilde\varphi(V)$ connected; the paper does not prove
  it, and the forward reference (l.184–186) claims only « une composante connexe ». Proved: the
  component form, and the full form iff `D ∩ φ̃(V)` is preconnected; the full form for `z ≡ 0`.
  Later proved for every shell and for every pocket when `n ≤ 1`, open only for
  `ConnexeOuvertPrinted` (`Benzecri.Chapter2.PremierFull`, T-bz-c2-premier-full-proj).
* The inclusion `P ⊆ φ̃⁻¹(D)`, which the paper does not argue, needs `z < 1` on `φ(P)` where
  condition *a* gives `z ≤ 1` (`IsPocheProj.cote_lt_one`).
* 1°a goes through Mathlib's lifting criterion (`IsLocalHomeomorph.existsUnique_continuousMap_lifts`):
  two paths from a point of `P` with the same end lift with the same end, because Prop. 7 moves
  both into `P`, i.e. into the source of the one chart `φ ∘ g`, over which a lift is a fixed
  translate of the chart's jets (`jetSMul_eq_of_path`). This is the paper's argument, with « composant
  chaque jet avec l'automorphisme $g^{-1}$ » replaced by the chart `φ ∘ g`; its loop form is
  `chemin_jets_ferme`. « isomorphe à un produit » is given as a bijection, not a homeomorphism.
* « application de $V$ sur $S(n)$ » (l.538, l.559) is read « dans » (into), Benzécri's usage of
  « sur » here and at l.156, l.171, l.184–185 (1° itself says « sur un ouvert »); onto is false
  already in the model, where `φ̃(V)` lies in the open hemisphere `H₀ ≠ S(n)`. A usage note, not a
  question.
* `[sic]`, not findings: « assertation » (l.555), « nous : allons » (l.587).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology unitInterval
open scoped Pointwise

namespace Benzecri

universe u

/-! ### Paths of `J(V)` over the source of one chart -/

section Paths

variable {M : Type u} [TopologicalSpace M] {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
  [MulAction G X] [ContinuousConstSMul G X] [IsAnalyticAction G X] [ChartedSpace X M]
  [HasGroupoid M (gxGroupoid G X)]

/-- Over the source of one chart `ψ` of the maximal atlas, a path `Γ` of `J(V)` is the translate of
the jets of `ψ` by the sheet of `Γ 0` (uniqueness of lifts through the covering `J(V) → V`). -/
theorem jetSMul_eq_of_path {ψ : OpenPartialHomeomorph M X}
    (hψ : ψ ∈ (gxGroupoid G X).maximalAtlas M) (Γ : C(I, jets G X M))
    (hΓ : ∀ t, (Γ t).1.1 ∈ ψ.source) (t : I) :
    (Γ t).1 = jetSMul (sheetIndex hψ (Γ 0)) (jet (Γ t).1.1 ψ) := by
  set c := sheetIndex hψ (Γ 0) with hc
  let Λ : I → jets G X M := fun t => ⟨jet (Γ t).1.1 (fun y => c • ψ y), by
    rw [← jetSMul_jet]
    exact jetSMul_jet_mem_jets hψ (hΓ t) c⟩
  have hΛ : Continuous Λ :=
    ((continuous_jet _).comp
      (continuous_jetSource.comp (continuous_subtype_val.comp Γ.continuous))).subtype_mk _
  have hcomp : (fun j : jets G X M => j.1.1) ∘ Γ = (fun j : jets G X M => j.1.1) ∘ Λ :=
    funext fun _ => rfl
  have h0 : Γ 0 = Λ 0 := by
    apply Subtype.ext
    show (Γ 0).1 = jet (Γ 0).1.1 (fun y => c • ψ y)
    rw [← jetSMul_jet]
    exact val_eq_jetSMul_sheetIndex hψ (hΓ 0)
  have heq := (isCoveringMap_jets M X G).eq_of_comp_eq Γ.continuous hΛ hcomp 0 h0
  have ht : (Γ t).1 = (Λ t).1 := congrArg Subtype.val (congrFun heq t)
  rw [ht]
  show jet (Γ t).1.1 (fun y => c • ψ y) = jetSMul c (jet (Γ t).1.1 ψ)
  rw [jetSMul_jet]

/-- **Over the source of one chart `ψ` of the maximal atlas, a path of `J(V)` is a fixed translate
of the jets of `ψ`**: there is `c ∈ G` with `Γ t = c • jet (Γ t) ψ` for every `t` (« la restriction
à $P$ de $J(V)$ est un produit »). -/
theorem exists_jetSMul_eq_of_path {ψ : OpenPartialHomeomorph M X}
    (hψ : ψ ∈ (gxGroupoid G X).maximalAtlas M) (Γ : C(I, jets G X M))
    (hΓ : ∀ t, (Γ t).1.1 ∈ ψ.source) :
    ∃ c : G, ∀ t, (Γ t).1 = jetSMul c (jet (Γ t).1.1 ψ) :=
  ⟨_, jetSMul_eq_of_path hψ Γ hΓ⟩

end Paths

/-! ### The cote is `< 1` on a pocket; convex neighbourhoods in an open hemisphere -/

section Cote

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **The cote is `< 1` on a pocket** (condition *a* gives `≤ 1`; `φ(P)` is open and an affine
function reaching its supremum at an interior point is constant, against `inf = 0`). -/
theorem IsPocheProj.cote_lt_one (hP : IsPocheProj P l φ z) {M : V} (hM : M ∈ P) :
    z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 := by
  rcases (hP.le_one ⟨φ M, hP.mapsTo_hemi hM⟩ (mem_image_of_mem φ hM)).lt_or_eq with h | h
  · exact h
  exfalso
  set m : Sphere.openHemisphere l := ⟨φ M, hP.mapsTo_hemi hM⟩ with hm
  have hopen : IsOpen (φ '' P) := by
    rw [← hP.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  -- an affine function with a local maximum at an interior point has a zero linear part
  have hlin : ∀ u : Sphere.HemiTrans l, z.linear u = 0 := by
    intro u
    have hM₀ : l (Sphere.nrep l (m : S n)) = 1 := Sphere.l_nrep m.2
    set M₀ := Sphere.nrep l (m : S n) with hM₀def
    set w : Fin (n + 1) → ℝ := (u (Sphere.hq l M₀) : Fin (n + 1) → ℝ) with hwdef
    have hw : l w = 0 := (u (Sphere.hq l M₀)).2
    have hne : ∀ t : ℝ, M₀ + t • w ≠ 0 := fun t h0 => by
      have := congrArg l h0
      simp [hM₀, hw] at this
    have hfun : (fun t : ℝ => ((t • u +ᵥ m : Sphere.openHemisphere l) : S n)) =
        fun t => Sphere.mk (M₀ + t • w) (hne t) := by
      funext t
      rw [Sphere.coe_vadd_eq (t • u) m (Sphere.nrep_ne_zero m.2) (Sphere.mk_nrep m.2)]
      congr 1
    have hc : Continuous fun t : ℝ => ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) := by
      rw [hfun]
      exact Sphere.continuous_mk_comp (continuous_const.add (continuous_id.smul continuous_const))
        hne
    have h0 : ((0 : ℝ) • u +ᵥ m : Sphere.openHemisphere l) = m := by rw [zero_smul, zero_vadd]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) ∈ φ '' P :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [h0]
        exact hopen.mem_nhds ⟨M, hM, rfl⟩)
    have hle : ∀ᶠ t in 𝓝 (0 : ℝ), t * z.linear u ≤ 0 := hev.mono fun t ht => by
      have := hP.le_one (t • u +ᵥ m) ht
      rwa [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, h,
        add_le_iff_nonpos_left] at this
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hle
    have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h2 := @hball (-(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith)
    nlinarith
  -- so `z ≡ 1`, against `inf z = 0`
  have hconst : ∀ y, z y = 1 := fun y => by
    rw [← vsub_vadd y m, AffineMap.map_vadd, hlin, zero_vadd]
    exact h
  have h10 : (1 : ℝ) ≤ 0 := hP.isGLB.2 (by
    rintro _ ⟨y, -, rfl⟩
    rw [hconst])
  linarith

/-- `φ` maps the pocket into the half-space `D = {z < 1}` of `H̊`. -/
theorem IsPocheProj.mapsTo_demiEspace (hP : IsPocheProj P l φ z) {M : V} (hM : M ∈ P) :
    φ M ∈ demiEspace z :=
  ⟨⟨φ M, hP.mapsTo_hemi hM⟩, hP.cote_lt_one hM, rfl⟩

/-- **Convex neighbourhoods in an open hemisphere**: every point `a` of `H̊` and of an open set `O`
of `S(n)` has an open neighbourhood `U ⊆ O ∩ H̊` containing the segment of any two of its points. -/
theorem exists_isOpen_closedSeg_subset {O : Set (S n)} (hO : IsOpen O) {a : S n} (ha : a ∈ O)
    (haH : a ∈ Sphere.openHemisphere l) :
    ∃ U : Set (S n), IsOpen U ∧ a ∈ U ∧ U ⊆ O ∧ U ⊆ Sphere.openHemisphere l ∧
      ∀ b ∈ U, ∀ c ∈ U, Sphere.closedSeg b c ⊆ U := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := l) (Module.finrank_fin_fun ℝ)
  have hj := isOpenEmbedding_coe_affineEquiv e.symm
  have ha' : (e.symm (e ⟨a, haH⟩) : S n) = a := by rw [e.symm_apply_apply]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hO.preimage hj.continuous) (e ⟨a, haH⟩)
    (by rw [mem_preimage, ha']; exact ha)
  refine ⟨(fun y => (e.symm y : S n)) '' Metric.ball (e ⟨a, haH⟩) ε,
    hj.isOpenMap _ Metric.isOpen_ball, ⟨_, Metric.mem_ball_self hε, ha'⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hball hy
  · rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  · rintro _ ⟨β, hβ, rfl⟩ _ ⟨γ, hγ, rfl⟩
    have hseg : affineSegment ℝ (e.symm β) (e.symm γ) = e.symm '' segment ℝ β γ := by
      rw [← affineSegment_eq_segment]
      exact (affineSegment_image e.symm.toAffineMap β γ).symm
    dsimp only
    rw [← Sphere.coe_image_affineSegment, hseg, image_image]
    exact image_mono ((convex_ball _ _).segment_subset hβ hγ)

/-- Every point of `S(n)` lies in an open hemisphere. -/
theorem exists_mem_openHemisphere (a : S n) :
    ∃ l' : Module.Dual ℝ (Fin (n + 1) → ℝ), l' ≠ 0 ∧ a ∈ Sphere.openHemisphere l' := by
  obtain ⟨v, hv0, rfl⟩ := Sphere.exists_isRep a
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℝ (Fin (n + 1) → ℝ), f v ≠ 0 := by
    by_contra h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℝ v).1 fun f => not_not.1 (not_exists.1 h f))
  rcases hf.lt_or_gt with h | h
  · refine ⟨-f, fun h0 => hf ?_, (Sphere.mk_mem_openHemisphere hv0).2 ?_⟩
    · rw [← neg_neg f, h0, neg_zero, LinearMap.zero_apply]
    · rw [LinearMap.neg_apply]
      linarith
  · exact ⟨f, fun h0 => hf (by rw [h0, LinearMap.zero_apply]), (Sphere.mk_mem_openHemisphere hv0).2 h⟩

end Cote

/-! ### The Theorem's 1° -/

section Premier

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **1°a, the paper's key step** (l.545–557): in a connected sweepable `V` with a pocket, a path
`[j, j']` of `J(V)` whose projection is a loop `[M, M]` is closed, `j = j'`. -/
theorem chemin_jets_ferme [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) (Γ : C(I, jets (GSR n) (S n) V)) (hΓ : (Γ 0).1.1 = (Γ 1).1.1) :
    Γ 0 = Γ 1 := by
  have hK : IsCompact (range fun t => (Γ t).1.1) :=
    isCompact_range (continuous_jetSource.comp (continuous_subtype_val.comp Γ.continuous))
  obtain ⟨g, -, hg⟩ := compact_dans_poche (G := ⊤) hbal hP hK
  have hψ := isCompatibleChart_iff.1 (hP.compatible.trans_aut g)
  have hsrc : ∀ t, (Γ t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
    intro t
    have : g • (Γ t).1.1 ∈ P := hg (smul_mem_smul_set (mem_range_self t))
    simpa [GXAut.smul_def, hP.source_eq] using this
  apply Subtype.ext
  rw [jetSMul_eq_of_path hψ Γ hsrc 0, jetSMul_eq_of_path hψ Γ hsrc 1, hΓ]

/-- **1°a** (l.538–557): a connected sweepable `V` with a pocket `(P, H̊, φ, z)` has a map
`φ̃ : V → S(n)` all of whose jets lie in `J(V)` (a developing map, Ch. 1, Prop. 2) and which
coincides with `φ` on `P`. -/
theorem exists_isDeveloping_eqOn_poche [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) : ∃ p : V → S n, IsDeveloping (GSR n) p ∧ EqOn p φ P := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : ConnectedSpace V := { toNonempty := ⟨x₀⟩ }
  haveI : LocPathConnectedSpace V := locPathConnectedSpace_of_proj (n := n)
  haveI : PathConnectedSpace V := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hx₀φ : x₀ ∈ φ.source := hP.source_eq ▸ hx₀
  let e₀ : jets (GSR n) (S n) V := ⟨jet x₀ φ, hP.compatible x₀ hx₀φ⟩
  have cov := isCoveringMap_jets_proj (n := n) (V := V)
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ := cov.isLocalHomeomorph.existsUnique_continuousMap_lifts
    (ContinuousMap.id V) x₀ e₀ rfl (fun γ hγ => by
      simpa [and_comm] using cov.exists_path_lifts ((ContinuousMap.id V).comp γ) e₀
        (by rw [ContinuousMap.comp_apply, ContinuousMap.id_apply, hγ]; rfl))
    (fun γ γ' Γ Γ' hγ hγ' hΓ hΓ' hlift hlift' h1 => by
      -- Prop. 7 moves both paths into `P`, the source of the chart `φ ∘ g`
      have hK : IsCompact (range γ ∪ range γ') :=
        (isCompact_range γ.continuous).union (isCompact_range γ'.continuous)
      obtain ⟨g, -, hg⟩ := compact_dans_poche (G := ⊤) hbal hP hK
      have hψ := isCompatibleChart_iff.1 (hP.compatible.trans_aut g)
      have hl : ∀ t, (Γ t).1.1 = γ t := fun t => congrFun hlift t
      have hl' : ∀ t, (Γ' t).1.1 = γ' t := fun t => congrFun hlift' t
      have hsrc : ∀ t, (Γ t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
        intro t
        have : g • γ t ∈ P := hg (smul_mem_smul_set (Or.inl (mem_range_self t)))
        rw [hl t]
        simpa [GXAut.smul_def, hP.source_eq] using this
      have hsrc' : ∀ t, (Γ' t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
        intro t
        have : g • γ' t ∈ P := hg (smul_mem_smul_set (Or.inr (mem_range_self t)))
        rw [hl' t]
        simpa [GXAut.smul_def, hP.source_eq] using this
      apply Subtype.ext
      rw [jetSMul_eq_of_path hψ Γ hsrc 1, jetSMul_eq_of_path hψ Γ' hsrc' 1, hΓ, hΓ', hl 1, hl' 1,
        h1])
  have hsec : ∀ x, (F x).1.1 = x := fun x => congrFun hF x
  have hp := isDeveloping_developingOfSection F.continuous hsec
  have hgerm : (φ : V → S n) =ᶠ[𝓝 x₀] developingOfSection F := by
    have h := jet_developingOfSection F.continuous hsec x₀
    rw [hF₀] at h
    exact (jet_eq_jet_iff.1 h).symm
  refine ⟨developingOfSection F, hp, fun x hx => ?_⟩
  exact (eqOn_of_germ_eq_isDeveloping hP.compatible hp hP.isConnected.isPreconnected
    hP.source_eq.symm.subset hx₀ hgerm hx).symm

/-- **1°a, « le revêtement $J(V)$ de $V$ est isomorphe à un produit »**, set-theoretically: with
the developing map `φ̃` of 1°a, every jet of `J(V)` at `x` is `g • jet x φ̃` for a unique
`g ∈ GS(n, ℝ)`. -/
theorem jets_produit [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) :
    ∃ p : V → S n, IsDeveloping (GSR n) p ∧ EqOn p φ P ∧
      ∀ (x : V) (γ : Germ (𝓝 x) (S n)), (⟨x, γ⟩ : Jet V (S n)) ∈ jets (GSR n) (S n) V ↔
        ∃! g : GSR n, (⟨x, γ⟩ : Jet V (S n)) = jetSMul g (jet x p) := by
  obtain ⟨p, hp, hpφ⟩ := exists_isDeveloping_eqOn_poche hbal hP
  exact ⟨p, hp, hpφ, fun x γ => hp.existsUnique_jetSMul_eq x γ⟩

/-- **1°b** (l.559–580), for EVERY developing map: in a connected sweepable `V` with a pocket,
a map `p : V → S(n)` all of whose jets lie in `J(V)` is injective. (So the developing map of 1°a
is a global homeomorphism onto its image; and the projection of an « ouvert étalé » `V` of this
kind is one-to-one, which is OQ-46's alternative reading.) -/
theorem injective_of_isDeveloping_of_poche [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) : Function.Injective p := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  -- `p = c • φ̃` and `φ̃ = φ` on `P`
  obtain ⟨p₀, hp₀, hp₀φ⟩ := exists_isDeveloping_eqOn_poche hbal hP
  obtain ⟨c, hc, -⟩ := hp₀.existsUnique_smul_eq hp
  intro M N hMN
  -- `g` with `gM, gN ∈ P` (Prop. 7, corollary), and `γ` with `p ∘ g = γ ∘ p`
  obtain ⟨g, -, hgM, hgN⟩ := deux_points_dans_poche (G := ⊤) hbal hP M N
  have hpg : IsDeveloping (GSR n) (fun y => p (g • y)) :=
    isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
  obtain ⟨γ, hγ, -⟩ := hp.existsUnique_smul_eq hpg
  have h1 : p (g • M) = p (g • N) := by rw [hγ M, hγ N, hMN]
  have h2 : φ (g • M) = φ (g • N) := by
    rw [hc, hc] at h1
    rw [← hp₀φ hgM, ← hp₀φ hgN]
    exact MulAction.injective c h1
  have h3 : g • M = g • N :=
    φ.injOn (hP.source_eq.symm ▸ hgM) (hP.source_eq.symm ▸ hgN) h2
  exact MulAction.injective g h3

/-- **1°, first sentence** (l.522–523, proof *a*, *b*): there is a compatible chart `φ̃` of `V`
(source `V`) onto an open set of `S(n)`, inducing `φ` on `P`. -/
theorem exists_chart_poche [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  obtain ⟨p, hp, hpφ⟩ := exists_isDeveloping_eqOn_poche hbal hP
  obtain ⟨φ', hφ', hs, -, he⟩ :=
    exists_chart_of_injective hp (injective_of_isDeveloping_of_poche hbal hP hp)
  exact ⟨φ', hφ', hs, fun x hx => by rw [he]; exact hpφ hx⟩

/-- **The chart of 1° is unique**: two developing maps equal to `φ` on `P` are equal (rigidity:
they differ by one `γ ∈ GS(n, ℝ)`, which is `1` on the open set `φ(P)`). -/
theorem IsDeveloping.eq_of_eqOn_poche [PreconnectedSpace V] (hP : IsPocheProj P l φ z)
    {p p' : V → S n} (hp : IsDeveloping (GSR n) p) (hp' : IsDeveloping (GSR n) p')
    (hpφ : EqOn p φ P) (hp'φ : EqOn p' φ P) : p = p' := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  obtain ⟨c, hc, -⟩ := hp.existsUnique_smul_eq hp'
  have hc1 : c = 1 := hp.eq_of_eventuallyEq (x := x₀) (by
    filter_upwards [hP.isOpen.mem_nhds hx₀] with y hy
    rw [← hc y, hp'φ hy, ← hpφ hy, one_smul])
  funext y
  rw [hc y, hc1, one_smul]

/-- **1°c, the closure step**: a point of `φ̃⁻¹(D)` adherent to `P` lies in `P` (a segment from a
point of `P`, inside a convex neighbourhood, and condition *b*). -/
theorem closure_inter_preimage_subset_poche [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    closure P ∩ p ⁻¹' demiEspace z ⊆ P := by
  rintro N ⟨hNcl, hND⟩
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  obtain ⟨φ', hφ', hs, ht, he⟩ :=
    exists_chart_of_injective hp (injective_of_isDeveloping_of_poche hbal hP hp)
  subst he
  have hrange : IsOpen (range φ') := hp.isLocalHomeomorph.isOpenMap.isOpen_range
  have hDH : demiEspace z ⊆ Sphere.openHemisphere l := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  -- a convex neighbourhood `U ⊆ D ∩ φ̃(V)` of `φ̃(N)`, and a point `M ∈ P` over it
  obtain ⟨U, hUo, hNU, hUO, hUH, hUc⟩ := exists_isOpen_closedSeg_subset
    ((isOpen_demiEspace z).inter hrange) ⟨hND, mem_range_self N⟩ (hDH hND)
  obtain ⟨M, hMU, hMP⟩ := mem_closure_iff.1 hNcl (φ' ⁻¹' U) (hUo.preimage hp.continuous) hNU
  -- the segment `(M, N)` of `V`, through the chart `φ̃`
  have hab : φ' N ≠ -φ' M := Sphere.ne_neg_of_mem_openHemisphere (hUH hMU) (hUH hNU)
  have hsub : Sphere.closedSeg (φ' M) (φ' N) ⊆ φ'.target := by
    rw [ht]
    exact (hUc _ hMU _ hNU).trans fun y hy => (hUO hy).2
  have hseg := isProjSegment_of_chart hφ' hab hsub
  rw [φ'.left_inv (hs.symm ▸ mem_univ M), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
  -- condition `b` with `φ̃`, which has the germ of `φ` at `M`
  have hgerm : (φ' : V → S n) =ᶠ[𝓝 M] φ :=
    Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hMP) hpφ
  have hb := (hP.mem_of_segment _ M N hseg hMP φ' hφ' (hs.symm ▸ subset_univ _) hgerm).2
    (hDH hND)
  obtain ⟨q, hq, hqN⟩ := hND
  have hqe : (⟨φ' N, hDH ⟨q, hq, hqN⟩⟩ : Sphere.openHemisphere l) = q := Subtype.ext hqN.symm
  exact hb (by rw [hqe]; exact hq)

/-- **1°c, component form** (l.582–590 and the forward reference l.181–186): for every developing
map `p` equal to `φ` on `P` (the chart `φ̃` of 1° is one), `P` is the connected component of each of
its points in the preimage by `p` of the half-space `D = {z < 1}` of `H̊`. -/
theorem poche_eq_connectedComponentIn [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) {p : V → S n} (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P)
    {x : V} (hx : x ∈ P) : P = connectedComponentIn (p ⁻¹' demiEspace z) x := by
  have hPD : P ⊆ p ⁻¹' demiEspace z := fun y hy => by
    rw [mem_preimage, hpφ hy]
    exact hP.mapsTo_demiEspace hy
  refine Subset.antisymm (hP.isConnected.isPreconnected.subset_connectedComponentIn hx hPD) ?_
  refine (isPreconnected_connectedComponentIn (F := p ⁻¹' demiEspace z) (x := x))
    |>.subset_of_closure_inter_subset hP.isOpen ⟨x, mem_connectedComponentIn (hPD hx), hx⟩ ?_
  rintro y ⟨hycl, hyC⟩
  exact closure_inter_preimage_subset_poche hbal hP hp hpφ
    ⟨hycl, connectedComponentIn_subset _ _ hyC⟩

/-- **1°c, the full form reduced to a connectedness**: `P = φ̃⁻¹(D ∩ φ̃(V))`, the printed claim,
holds iff `D ∩ φ̃(V)` is preconnected, which the printed proof presumes (« on peut construire dans
$D\cap\tilde{\varphi}(V)$ une ligne brisée »). -/
theorem poche_eq_preimage_iff [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) {p : V → S n} (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    P = p ⁻¹' (demiEspace z ∩ range p) ↔ IsPreconnected (demiEspace z ∩ range p) := by
  obtain ⟨x, hx⟩ := hP.isConnected.nonempty
  have hemb : IsOpenEmbedding p :=
    hp.isLocalHomeomorph.isOpenEmbedding_of_injective (injective_of_isDeveloping_of_poche hbal hP hp)
  rw [preimage_inter_range, ← image_preimage_eq_inter_range, hemb.isInducing.isPreconnected_image]
  have hcomp := poche_eq_connectedComponentIn hbal hP hp hpφ hx
  constructor
  · intro h
    rw [← h]
    exact hP.isConnected.isPreconnected
  · intro h
    have hxD : x ∈ p ⁻¹' demiEspace z := by
      rw [hcomp] at hx
      exact connectedComponentIn_subset _ _ hx
    rw [hcomp, h.connectedComponentIn hxD]

/-- **The closure of the pocket lies over `H̊`**: a segment of `V` from a point of `P` to a point of
`closure P` exists inside a convex neighbourhood, and condition *b* puts it over `H̊`. -/
theorem closure_poche_subset_preimage_hemisphere [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    closure P ⊆ p ⁻¹' Sphere.openHemisphere l := by
  intro N hNcl
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  obtain ⟨φ', hφ', hs, ht, he⟩ :=
    exists_chart_of_injective hp (injective_of_isDeveloping_of_poche hbal hP hp)
  subst he
  have hrange : IsOpen (range φ') := hp.isLocalHomeomorph.isOpenMap.isOpen_range
  obtain ⟨l', hl'0, hNl'⟩ := exists_mem_openHemisphere (φ' N)
  haveI : Fact (l' ≠ 0) := ⟨hl'0⟩
  obtain ⟨U, hUo, hNU, hUO, hUH, hUc⟩ :=
    exists_isOpen_closedSeg_subset (l := l') hrange (mem_range_self N) hNl'
  obtain ⟨M, hMU, hMP⟩ := mem_closure_iff.1 hNcl (φ' ⁻¹' U) (hUo.preimage hp.continuous) hNU
  have hab : φ' N ≠ -φ' M := Sphere.ne_neg_of_mem_openHemisphere (hUH hMU) (hUH hNU)
  have hsub : Sphere.closedSeg (φ' M) (φ' N) ⊆ φ'.target := by
    rw [ht]
    exact (hUc _ hMU _ hNU).trans hUO
  have hseg := isProjSegment_of_chart hφ' hab hsub
  rw [φ'.left_inv (hs.symm ▸ mem_univ M), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
  have hgerm : (φ' : V → S n) =ᶠ[𝓝 M] φ :=
    Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hMP) hpφ
  exact (hP.mem_of_segment _ M N hseg hMP φ' hφ' (hs.symm ▸ subset_univ _) hgerm).1
    (mem_image_of_mem φ' hseg.right_mem)

/-- **1°c, the full form, for the constant cote** (`z ≡ 0`, the only constant cote a pocket
admits; OQ-61): then `P = V` and `P = φ̃⁻¹(D ∩ φ̃(V))`. So the open case of the full form is that
of a non-constant cote. -/
theorem poche_eq_preimage_of_cote_eq_zero [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) (hz : ∀ y, z y = 0) :
    P = univ ∧ P = p ⁻¹' (demiEspace z ∩ range p) := by
  have hDH : p ⁻¹' Sphere.openHemisphere l ⊆ p ⁻¹' demiEspace z := fun y hy =>
    ⟨⟨p y, hy⟩, show z ⟨p y, hy⟩ < 1 by rw [hz]; exact zero_lt_one, rfl⟩
  have hH := closure_poche_subset_preimage_hemisphere hbal hP hp hpφ
  have hcl : closure P ⊆ P := fun y hy =>
    closure_inter_preimage_subset_poche hbal hP hp hpφ ⟨hy, hDH (hH hy)⟩
  have huniv : P = univ :=
    IsClopen.eq_univ ⟨isClosed_of_closure_subset hcl, hP.isOpen⟩ hP.isConnected.nonempty
  refine ⟨huniv, ?_⟩
  rw [preimage_inter_range]
  refine (eq_univ_of_forall fun y => hDH (hH ?_)).symm ▸ huniv
  rw [huniv]
  exact subset_closure (mem_univ y)

/-- **The Theorem's 1°** (`bzthm:c2s3t1_poche_balayable`, l.522–524), in one piece: a compatible
chart `φ̃` with source `V`, inducing `φ` on `P`; `P` is the connected component of each of its points
in `φ̃⁻¹(D)`; and `P = φ̃⁻¹(D ∩ φ̃(V))` iff `D ∩ φ̃(V)` is preconnected. -/
theorem theoreme_premier [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P ∧ (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x) ∧
      (P = φ' ⁻¹' (demiEspace z ∩ range φ') ↔ IsPreconnected (demiEspace z ∩ range φ')) := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hP
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact ⟨φ', hφ', hs, hφ'φ, fun x hx => poche_eq_connectedComponentIn hbal hP hp hφ'φ hx,
    poche_eq_preimage_iff hbal hP hp hφ'φ⟩

/-- **« on est toujours dans la situation considérée en exemple »** (the forward reference,
l.181–186): in a connected sweepable `V` with a pocket `(P, H̊, φ, z)`, the developing map `φ̃` of
1° (which extends `φ`, and is injective) and the pocket meet the hypotheses of the projective
example of § 1 (l.172–179): `P` is a connected component of `φ̃⁻¹(D)`, `z` has infimum `0` on
`φ̃(P)`, and `φ̃` maps every segment of `V` with origin in `P` into `H̊`. -/
theorem situation_exemple [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) :
    ∃ p : V → S n, IsDeveloping (GSR n) p ∧ EqOn p φ P ∧ Function.Injective p ∧
      (∀ x ∈ P, P = connectedComponentIn (p ⁻¹' demiEspace z) x) ∧
      IsGLB (z '' ((↑) ⁻¹' (p '' P))) 0 ∧
      ∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N → M ∈ P →
        p '' Sg ⊆ Sphere.openHemisphere l := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hP
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  refine ⟨φ', hp, hφ'φ, injective_of_isDeveloping_of_poche hbal hP hp,
    fun x hx => poche_eq_connectedComponentIn hbal hP hp hφ'φ hx, ?_, ?_⟩
  · rw [image_congr hφ'φ]
    exact hP.isGLB
  · intro Sg M N hSg hM
    exact (hP.mem_of_segment Sg M N hSg hM φ' hφ' (hs.symm ▸ subset_univ _)
      (Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hM) hφ'φ)).1

/-- **OQ-46's alternative reading** (« the one-to-one case that § 3's Théorème shows always
holds »): in a connected sweepable `V` which has one pocket, the projective example of § 1
(l.172–179) holds as printed, without the hypothesis « `p` injective on `P` » that
`exemple_poche_projective` carries. This decides nothing about OQ-46: the example's `W` is
arbitrary. -/
theorem exemple_poche_projective_of_poche [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) {l' : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l' ≠ 0)]
    (z' : Sphere.openHemisphere l' →ᵃ[ℝ] ℝ) {x₀ : V} (hx₀ : p x₀ ∈ demiEspace z')
    (hinf : IsGLB (z' '' ((↑) ⁻¹' (p '' connectedComponentIn (p ⁻¹' demiEspace z') x₀))) 0)
    (hseg : ∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N →
      M ∈ connectedComponentIn (p ⁻¹' demiEspace z') x₀ → p '' Sg ⊆ Sphere.openHemisphere l') :
    ∃ φ' : OpenPartialHomeomorph V (S n),
      EqOn φ' p (connectedComponentIn (p ⁻¹' demiEspace z') x₀) ∧
      IsPocheProj (connectedComponentIn (p ⁻¹' demiEspace z') x₀) l' φ' z' :=
  exemple_poche_projective hp z' hx₀ hinf hseg
    (injective_of_isDeveloping_of_poche hbal hP hp).injOn

end Premier

/-! ### The printed statements, over the paper's manifolds -/

/-- **1° with « P n'est autre que » read as a connected component** (the forward reference,
l.181–186), over the paper's manifolds (Hausdorff, connected, second countable; `V : Type`). -/
def PremierComposantePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ ∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x

/-- **1° as printed** (l.522–524, with the proof's « $P=\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$ »),
over the paper's manifolds. Not proved: see SCOPE. -/
def PremierPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ')

/-- **The connectedness the printed proof of 1°c presumes** (l.587–588, « on peut construire dans
$D\cap\tilde{\varphi}(V)$ une ligne brisée »), over the paper's manifolds: for every pocket and
the chart `φ̃` of 1°, `D ∩ φ̃(V)` is preconnected. Not proved: see SCOPE. -/
def ConnexePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∀ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' →
        φ'.source = univ → EqOn φ' φ P → IsPreconnected (demiEspace z ∩ range φ')

/-- **The component form of 1° holds in every dimension.** -/
theorem premierComposantePrinted (n : ℕ) : PremierComposantePrinted n := by
  intro V _ _ _ _ _ _ hbal P l _ φ z hP
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, -⟩ := theoreme_premier hbal hP
  exact ⟨φ', hφ', hs, hφ'φ, hcomp⟩

/-- **1° as printed is exactly the connectedness its proof presumes**: `PremierPrinted n` holds iff
`ConnexePrinted n` does (the chart is unique, `IsDeveloping.eq_of_eqOn_poche`). -/
theorem premierPrinted_iff (n : ℕ) : PremierPrinted n ↔ ConnexePrinted n := by
  constructor
  · intro h V _ _ _ _ _ _ hbal P l _ φ z hP φ'' hφ'' hs'' hφ''φ
    obtain ⟨φ', hφ', hs, hφ'φ, hfull⟩ := h V hbal P l φ z hP
    have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
    have hp'' : IsDeveloping (GSR n) φ'' := fun x => hφ'' x (hs''.symm ▸ mem_univ x)
    have heq : (φ' : V → S n) = φ'' := hp.eq_of_eqOn_poche hP hp'' hφ'φ hφ''φ
    rw [heq] at hfull
    exact (poche_eq_preimage_iff hbal hP hp'' hφ''φ).1 hfull
  · intro h V _ _ _ _ _ _ hbal P l _ φ z hP
    obtain ⟨φ', hφ', hs, hφ'φ, -, hiff⟩ := theoreme_premier hbal hP
    exact ⟨φ', hφ', hs, hφ'φ, hiff.2 (h V hbal P l φ z hP φ' hφ' hs hφ'φ)⟩

/-! ### Non-vacuity: `ℝⁿ` with its translations and the model pocket -/

section Model

variable (n : ℕ)

/-- **`ℝⁿ`, with its canonical locally projective structure, is sweepable**: the translations are
projective automorphisms, and they move `{0}` everywhere. -/
theorem isBalayable_model :
    @IsBalayable (GSR n) (S n) _ _ _ (Fin n → ℝ) _ (projOfAff n (Fin n → ℝ)) := by
  letI := projOfAff n (Fin n → ℝ)
  have hmor : ∀ y : Fin n → ℝ, IsGXMorphism (GSR n) (S n) (fun w : Fin n → ℝ => y + w) := by
    intro y
    refine ⟨continuous_const.add continuous_id, fun x =>
      ⟨Sphere.affToGS (GAR.translation y), Eventually.of_forall fun w => ?_⟩⟩
    show Sphere.hemiChart n (y + w) = Sphere.affToGS (GAR.translation y) • Sphere.hemiChart n w
    exact Sphere.hemiChart_apply_eq_smul (GAR.translation y) w
  refine ⟨{0}, isCompact_singleton, eq_univ_of_forall fun x => mem_iUnion₂.2
    ⟨GXAut.ofBijective (hmor x) (Equiv.addLeft x).bijective, Subgroup.mem_top _, ?_⟩⟩
  rw [smul_set_singleton, mem_singleton_iff, GXAut.ofBijective_smul, add_zero]

section Local

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- **The hypotheses of 1° are met**, in every dimension: `ℝⁿ` (canonical projective structure)
is connected, sweepable (`isBalayable_model`) and has the pocket `(ℝⁿ, H₀, j, z)` of
`exists_isPocheProj_model`; the conclusion of `theoreme_premier` holds for it. (That pocket has the
cote `z ≡ 0`, which OQ-61 (a) would exclude.) -/
theorem theoreme_premier_model :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (S n))
      (z : Sphere.openHemisphere (Sphere.lastForm n) →ᵃ[ℝ] ℝ),
      IsPocheProj (univ : Set (Fin n → ℝ)) (Sphere.lastForm n) φ z ∧
      ∃ φ' : OpenPartialHomeomorph (Fin n → ℝ) (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ univ ∧
        (∀ x ∈ (univ : Set (Fin n → ℝ)), univ = connectedComponentIn (φ' ⁻¹' demiEspace z) x) ∧
        ((univ : Set (Fin n → ℝ)) = φ' ⁻¹' (demiEspace z ∩ range φ') ↔
          IsPreconnected (demiEspace z ∩ range φ')) := by
  obtain ⟨φ, z, hP⟩ := exists_isPocheProj_model n
  exact ⟨φ, z, hP, theoreme_premier (isBalayable_model n) hP⟩

end Local

end Model

/-! ### A non-degenerate witness: the half-line `]0, ∞[`, its homotheties and the pocket `]0, 1[` -/

section DemiDroite

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- The homothety of ratio `c > 0` of the half-line `]0, ∞[` (`demiDroiteOuverte`). -/
def homothetieDemiDroite (c : ℝ) (hc : 0 < c) : demiDroiteOuverte → demiDroiteOuverte :=
  fun x => ⟨c • (x : Fin 1 → ℝ), show 0 < c * (x : Fin 1 → ℝ) 0 from mul_pos hc x.2⟩

/-- A homothety of `]0, ∞[` is a projective morphism (for the canonical projective structure). -/
theorem isGXMorphism_homothetieDemiDroite (c : ℝ) (hc : 0 < c) :
    IsGXMorphism (GSR 1) (S 1) (homothetieDemiDroite c hc) := by
  refine ⟨((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _, fun x =>
    ⟨Sphere.affToGS (LinearEquiv.smulOfNeZero ℝ (Fin 1 → ℝ) c hc.ne').toAffineEquiv,
      Eventually.of_forall fun y => ?_⟩⟩
  have h := Sphere.hemiChart_apply_eq_smul
    (LinearEquiv.smulOfNeZero ℝ (Fin 1 → ℝ) c hc.ne').toAffineEquiv (y : Fin 1 → ℝ)
  simp only [LinearEquiv.coe_toAffineEquiv, LinearEquiv.smulOfNeZero_apply] at h
  exact h

theorem bijective_homothetieDemiDroite (c : ℝ) (hc : 0 < c) :
    Function.Bijective (homothetieDemiDroite c hc) := by
  refine ⟨fun x y h => Subtype.ext ?_, fun y =>
    ⟨homothetieDemiDroite c⁻¹ (inv_pos.2 hc) y, Subtype.ext ?_⟩⟩
  · exact smul_right_injective (Fin 1 → ℝ) hc.ne' (congrArg Subtype.val h)
  · show c • c⁻¹ • (y : Fin 1 → ℝ) = y
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- **`]0, ∞[` is sweepable**: its homotheties move the point `1` everywhere. -/
theorem isBalayable_demiDroite : IsBalayable (GSR 1) (S 1) demiDroiteOuverte := by
  let one : demiDroiteOuverte := ⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos⟩
  refine ⟨{one}, isCompact_singleton, eq_univ_of_forall fun x => mem_iUnion₂.2
    ⟨GXAut.ofBijective (isGXMorphism_homothetieDemiDroite _ x.2)
      (bijective_homothetieDemiDroite _ x.2), Subgroup.mem_top _, ?_⟩⟩
  rw [smul_set_singleton, mem_singleton_iff, GXAut.ofBijective_smul]
  apply Subtype.ext
  funext i
  rw [Subsingleton.elim i 0]
  show (x : Fin 1 → ℝ) 0 = (x : Fin 1 → ℝ) 0 * 1
  rw [mul_one]

/-- **1° on a non-degenerate example** (`n = 1`): the half-line `]0, ∞[` (canonical projective
structure) is connected and sweepable, and has a pocket `P = ]0, 1[ ≠ V` (the image of the affine
pocket `(]0, 1[, id, x₀)` by the Remarque after Déf. 1′); the chart of 1° exists, and `P` is the
connected component of each of its points in `φ̃⁻¹(D)`. Its cote, the coordinate `x₀` carried by
the Remarque, is not constant on `V`; the statement records `P ≠ V`, which forces it. -/
theorem theoreme_premier_demiDroite :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      IsPocheProj P (Sphere.lastForm 1) φ z ∧ P ≠ univ ∧
      ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (S 1), IsCompatibleChart (GSR 1) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧
        ∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x := by
  set z : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap with hz
  let x₀ : demiDroiteOuverte := ⟨fun _ => 1 / 2, show (0 : ℝ) < 1 / 2 by norm_num⟩
  set U := (Subtype.val : demiDroiteOuverte → Fin 1 → ℝ) ⁻¹' {y | z y < 1} with hU
  have himgU : (Subtype.val '' U : Set (Fin 1 → ℝ)) = {x | 0 < x 0 ∧ x 0 < 1} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hC : Convex ℝ {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hUconn : IsPreconnected U := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert hC.isPreconnected using 1
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hx₀ : z (x₀ : Fin 1 → ℝ) < 1 := show (1 / 2 : ℝ) < 1 by norm_num
  have hPU : connectedComponentIn U x₀ = U := hUconn.connectedComponentIn hx₀
  have hinf : IsGLB (z '' (Subtype.val '' connectedComponentIn U x₀)) 0 := by
    rw [hPU, himgU]
    have : z '' {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro ht
        exact ⟨fun _ => t, ht, rfl⟩
    rw [this]
    exact isGLB_Ioo zero_lt_one
  obtain ⟨φ, -, hφ⟩ := exemple_poche_affine isDeveloping_val_demiDroiteOuverte z hx₀ hinf
    Subtype.val_injective.injOn
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm 1) (Module.finrank_fin_fun ℝ)
  have hP := hφ.toPocheProj e.symm
  have hne : connectedComponentIn U x₀ ≠ univ := by
    rw [hPU]
    intro h
    have h2 : (⟨fun _ => 2, show (0 : ℝ) < 2 by norm_num⟩ : demiDroiteOuverte) ∈ U :=
      h ▸ mem_univ _
    exact absurd (show (2 : ℝ) < 1 from h2) (by norm_num)
  have hconv : IsPreconnected ((demiDroiteOuverte : Set (Fin 1 → ℝ))) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).isPreconnected
  haveI : PreconnectedSpace demiDroiteOuverte := Subtype.preconnectedSpace hconv
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, -⟩ := theoreme_premier isBalayable_demiDroite hP
  exact ⟨_, _, _, hP, hne, φ', hφ', hs, hφ'φ, hcomp⟩

end DemiDroite

end Benzecri
