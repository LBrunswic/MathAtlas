import Benzecri.Chapter2.Lignes
import Benzecri.Chapter2.PseudoBoules

/-!
# Chapter 2 § 2, Prop. 7 and its corollary — in a connected sweepable locally projective manifold, an automorphism of the group moves any compact set (any two points) into a given pocket

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 252–253; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-compact (DEC-137).

* **`bzprop:c2s2p7_compact_dans_poche`** — `benzecri1960_ch2.tex:451` (Prop. 7, l.451–457,
  proof l.459–480). `Benzecri.compact_dans_poche`, every dimension, sorry-free; printed form over
  the paper's manifolds: `compactDansPochePrinted n` for every `n`. The proof's first paragraph is
  `exists_domaineGenerateur_proj` (`IsBalayableFor.exists_domaineGenerateur` for any `(G, X)`).
* **`bzcor:c2s2p7c_deux_points_dans_poche`** — `benzecri1960_ch2.tex:482` (corollary, l.482–487,
  proof l.489–491). `Benzecri.deux_points_dans_poche`, every dimension, sorry-free; printed form:
  `deuxPointsDansPochePrinted n` for every `n`.

The Remark and Prop. 7′ (the affine case, l.493–513) are not here (T-bz-c2-cas-affin).

> **Proposition 7.** Soit $V$ une variété localement projective connexe et balayable pour un
> groupe $G$ d'automorphismes projectifs (cf. chap. 1, § 1, déf. 15). Soit
> $(P, \mathring{H}, \varphi, z)$ une poche de $V$. Soit $E$ un compact de $V$. Il existe un
> automorphisme projectif $g\in G$, tel que $gE\subset P$.
>
> Démonstration. — Nous allons d'abord montrer que tout compact $E$ de $V$ est inclus dans un
> domaine générateur connexe (pour le groupe $G$); nous démontrerons alors la proposition en
> supposant que $E$ est un domaine générateur compact connexe. Soit $K$ un domaine générateur
> compact. $E\cup K$ est aussi un domaine générateur compact; puisque $V$ est localement compact
> et localement connexe, on peut recouvrir $E\cup K$ au moyen d'un nombre fini de compacts
> connexes; soit $E'$, la réunion de ces compacts : puisque $V$ est connexe, $E'$ est inclus dans
> un compact connexe $E''$; il suffit, pour obtenir $E''$, d'ajouter à $E'$ un nombre fini de
> lignes brisées reliant les composantes connexes de $E'$.
>
> Soit donc $E$ un domaine générateur compact connexe. Soit $k$ un nombre strictement positif
> ($k=\log K$). Soit $M^0$ un point de $P$ de cote $z\,\varphi(M^0)$ inférieure à
> $1/K^{n(E, k)}$. Puisque $E$ est un domaine générateur pour $G$, il existe $g\in G$
> automorphisme projectif de $V$ et $N^0\in E$, tels que $gN^0=M^0$. Soit $N$ un point quelconque
> de $E$ : nous allons montrer que $gN\in P$.
>
> En effet (prop. 4), il existe une ligne brisée $L$ reliant $N^0$ à $N$, et formée d'au plus
> $n(E, k)$ segments tous bornés par $k$. Il résulte de la proposition 6 que $gN\in P$.
>
> **Corollaire.** Soit $V$ une variété localement projective, connexe balayable pour un groupe $G$
> d'automorphismes projectifs; soit $(P, \mathring{H}, \varphi, z)$ une poche de $V$; soient $M$
> et $N$ deux points de $V$. Il existe un automorphisme projectif $g\in G$ de $V$ tel que
> $gM\in P$; $gN\in P$.
>
> En effet, $\{M, N\}$ est une partie compacte de $V$.

## The proofs formalized

**First paragraph** (a lemma with no label). A point of a manifold charted on a locally compact,
locally connected Hausdorff model has a compact preconnected neighbourhood: the image by the
inverse chart of the closure of a connected component of the interior of a compact neighbourhood
inside the chart's target (`exists_isCompact_isPreconnected_mem_nhds_of_chartedSpace`; `S(n)` is
compact, Hausdorff and locally path connected, `locPathConnectedSpace_S`). In a preconnected space
where every point has one, every compact set lies in a compact preconnected set
(`exists_isCompact_isPreconnected_superset`): the points `x` such that some compact preconnected
set contains `x₀` and `x` form a clopen set, hence everything; finitely many such sets, each
enlarged by a neighbourhood, cover the compact set and share `x₀`. Applied to `E ∪ K`, `K` a
compact generating domain, this is the paper's `E''` (`exists_domaineGenerateur_proj`).

**Prop. 7.** Dimension `0`: a connected `V` has at most one point (`subsingleton_dim_zero`) and
the pocket is nonempty, so `g = 1`. Dimension `n ≥ 1`: the printed argument with `K = 2`,
`k = log 2`. `M⁰ ∈ P` with `z(φ(M⁰)) < 1/2^{n(F, k)}` comes from `inf z = 0` (condition *a*,
`IsGLB.exists_between`); `gN⁰ = M⁰` with `N⁰ ∈ F`; Prop. 4 (`ligne_brisee`) joins `N⁰` to `N ∈ F`
by `p ≤ n(F, k)` segments majorised by `k`; `g` carries that line to a line from `M⁰` to `gN`
(`IsLigneBrisee.smul`, from `IsMajoreSeg.smul`); `1/2^{n(F, k)} ≤ 1/2^p`; Prop. 6 in its corrected
form `IsPocheProj.ligne_brisee_poche`, valid for every pocket, gives `gN ∈ P`. **Corollary**:
`{M, N}` is compact.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement projective » | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]`; Hausdorff and second countable never used (the printed forms `CompactDansPochePrinted`, `DeuxPointsDansPochePrinted` carry them) |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the empty `V` is allowed, where the statement is trivial) |
| « balayable pour un groupe $G$ d'automorphismes projectifs » (Ch. 1 Déf. 15) | ✓ carried: `G : Subgroup (GXAut (GSR n) (S n) V)`, `IsBalayableFor (GSR n) (S n) V G` (strict) |
| « $(P, \mathring{H}, \varphi, z)$ une poche de $V$ » (Déf. 1′) | ✓ carried: `IsPocheProj P l φ z` (strict), `H̊` given by its equation `l ≠ 0` |
| « $E$ un compact de $V$ » | ⚠ weakened: `IsCompact E` (quasi-compact; Bourbaki's « compact » also asks Hausdorff, automatic in the paper's `V`) |
| conclusion « $g\in G$, $gE\subset P$ » | ✓ carried: `∃ g ∈ G, g • E ⊆ P`; « ⊂ » is the paper's inclusion, not strict: l.129 « φ(P) ⊂ H̊ » is read `⊆` by the strict pocket (`IsPocheProj.image_subset`), and l.237 (3°, conclusion `≤`) and l.549 use it the same way |
| corollary: `M`, `N` two points; « $gM\in P$; $gN\in P$ » | ✓ carried: `∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P` |
| the dimension | ✓ every `n`, `n = 0` included: no `NeZero n` (OQ-45 does not reach these rows) |
| proof, first paragraph: `V` « localement compact et localement connexe » | ✓ derived from the charts (no Hausdorffness of `V` used); the general form `exists_isCompact_isPreconnected_superset_of_locallyConnected` takes the printed hypotheses, with `T2Space` |

## SCOPE (disclosed)

* Nothing is left unproved: no `sorry`, no added hypothesis; both labels are marked.
* **Proof-level remarks** (statements unaffected). (1) « ajouter à $E'$ un nombre fini de lignes
  brisées reliant les composantes connexes de $E'$ » (l.466–468) presupposes that two points of a
  connected `V` are joined by a broken line, which the paper does not prove before Prop. 7 (the
  proof of Prop. 5, l.432–434, asserts it too, while Prop. 4 covers only a compact connected `E`).
  Here the joining is topological (a clopen argument), which needs no broken line and covers
  `n = 0`, where no broken line of majorised segments exists. (2) « Il résulte de la proposition 6
  que $gN\in P$ » (l.478–479) applies Prop. 6 to `gL`, not to `L`: this uses that a projective
  automorphism carries a majorised segment to a majorised segment (2°, `IsMajoreSeg.smul`, and
  `IsLigneBrisee.smul` here), and that `p ≤ n(E, k)` gives `1/K^{n(E, k)} ≤ 1/K^p` (`K > 1`);
  both are left implicit. (3) Prop. 6 is false as printed for a pocket of cote `z ≡ 0`
  (T-bz-c2-lignes, `ligneBriseePochePrinted_iff`), but Prop. 7 uses only « $B\in P$ », which the
  corrected `IsPocheProj.ligne_brisee_poche` gives for every pocket. (4) In dimension `0`, under
  the strict library's Déf. 1 convention, the printed proof does not run (`n(E, k)` is undefined
  and Prop. 4 fails; it would run under OQ-45 (b)), but the statement holds there because a
  connected `V` has at most one point.
* **Notation, not findings**: `K` names both the compact generating domain (l.464) and `e^k`
  (l.471), as the transcription's comment (l.475) records; here the generating domain is `K` and
  `K = 2`. The scan (pp. 252–253, PDF pp. 25–26) agrees with the transcription of l.451–491.
* `IsLigneBrisee.smul` is proved here because the strict library lacks it (the dispatch allows it).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Pointwise

namespace Benzecri

universe u v w

/-! ### The first paragraph: compact connected generating domains -/

section Topology

variable {X : Type v} [TopologicalSpace X]

/-- In a locally compact, locally connected Hausdorff space, every neighbourhood of a point
contains a compact preconnected neighbourhood. -/
theorem exists_isCompact_isPreconnected_mem_nhds_subset [LocallyCompactSpace X]
    [LocallyConnectedSpace X] [T2Space X] {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ C ∈ 𝓝 x, C ⊆ U ∧ IsCompact C ∧ IsPreconnected C := by
  obtain ⟨s, hs, hsU, hsc⟩ := local_compact_nhds hU
  have hxW : x ∈ connectedComponentIn (interior s) x :=
    mem_connectedComponentIn (mem_interior_iff_mem_nhds.2 hs)
  have hWs : closure (connectedComponentIn (interior s) x) ⊆ s :=
    closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) hsc.isClosed
  exact ⟨closure (connectedComponentIn (interior s) x),
    mem_of_superset ((isOpen_interior.connectedComponentIn).mem_nhds hxW) subset_closure,
    hWs.trans hsU, hsc.of_isClosed_subset isClosed_closure hWs,
    isPreconnected_connectedComponentIn.closure⟩

/-- Every point of a manifold charted on a locally compact, locally connected Hausdorff model has a
compact preconnected neighbourhood (no separation of the manifold is used). -/
theorem exists_isCompact_isPreconnected_mem_nhds_of_chartedSpace {M : Type u}
    [TopologicalSpace M] [LocallyCompactSpace X] [LocallyConnectedSpace X] [T2Space X]
    [ChartedSpace X M] (x : M) : ∃ C ∈ 𝓝 x, IsCompact C ∧ IsPreconnected C := by
  have hx : x ∈ (chartAt X x).source := mem_chart_source X x
  obtain ⟨D, hD, hDt, hDc, hDp⟩ := exists_isCompact_isPreconnected_mem_nhds_subset
    ((chartAt X x).open_target.mem_nhds ((chartAt X x).map_source hx))
  refine ⟨(chartAt X x).symm '' D, ?_, hDc.image_of_continuousOn
    ((chartAt X x).continuousOn_symm.mono hDt),
    hDp.image _ ((chartAt X x).continuousOn_symm.mono hDt)⟩
  have h := (chartAt X x).symm.image_mem_nhds ((chartAt X x).map_source hx) hD
  rwa [(chartAt X x).left_inv hx] at h

/-- **In a preconnected space where every point has a compact preconnected neighbourhood, every
compact set lies in a compact preconnected set.** -/
theorem exists_isCompact_isPreconnected_superset [PreconnectedSpace X]
    (h : ∀ x : X, ∃ C ∈ 𝓝 x, IsCompact C ∧ IsPreconnected C) {E : Set X} (hE : IsCompact E) :
    ∃ F, E ⊆ F ∧ IsCompact F ∧ IsPreconnected F := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨E, subset_rfl, hE, by rw [Set.eq_empty_of_isEmpty E]; exact isPreconnected_empty⟩
  choose D hDx hDc hDp using h
  -- `A`: the points joined to `x₀` by a compact preconnected set
  set A : Set X := {x | ∃ C, IsCompact C ∧ IsPreconnected C ∧ x₀ ∈ C ∧ x ∈ C} with hA
  have hDA : ∀ x ∈ A, D x ⊆ A := by
    rintro x ⟨C, hCc, hCp, h0, hx⟩ y hy
    exact ⟨C ∪ D x, hCc.union (hDc x), hCp.union x hx (mem_of_mem_nhds (hDx x)) (hDp x),
      Or.inl h0, Or.inr hy⟩
  have hAo : IsOpen A := isOpen_iff_mem_nhds.2 fun x hx => mem_of_superset (hDx x) (hDA x hx)
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨y, hyD, C, hCc, hCp, h0, hyC⟩ := mem_closure_iff_nhds.1 hx (D x) (hDx x)
    exact ⟨C ∪ D x, hCc.union (hDc x), hCp.union y hyC hyD (hDp x), Or.inl h0,
      Or.inr (mem_of_mem_nhds (hDx x))⟩
  have hA0 : x₀ ∈ A := ⟨D x₀, hDc x₀, hDp x₀, mem_of_mem_nhds (hDx x₀), mem_of_mem_nhds (hDx x₀)⟩
  have hAu : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨x₀, hA0⟩
  choose C hCc hCp hC0 hCx using fun x => (show x ∈ A from hAu ▸ mem_univ x)
  -- `B x = C x ∪ D x`: compact, preconnected, contains `x₀`, a neighbourhood of `x`
  obtain ⟨t, -, ht⟩ := hE.elim_nhds_subcover (fun x => C x ∪ D x)
    (fun x _ => mem_of_superset (hDx x) subset_union_right)
  refine ⟨⋃ x ∈ t, (C x ∪ D x), ht, t.isCompact_biUnion fun x _ => (hCc x).union (hDc x),
    isPreconnected_of_forall x₀ fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 hy
  exact ⟨C x ∪ D x, subset_biUnion_of_mem (u := fun x => C x ∪ D x) hxt, Or.inl (hC0 x), hyx,
    (hCp x).union x (hCx x) (mem_of_mem_nhds (hDx x)) (hDp x)⟩

/-- **The first paragraph's topological step, in its printed hypotheses**: in a connected,
locally compact, locally connected (Hausdorff) space every compact set lies in a compact connected
set. -/
theorem exists_isCompact_isPreconnected_superset_of_locallyConnected [PreconnectedSpace X]
    [LocallyCompactSpace X] [LocallyConnectedSpace X] [T2Space X] {E : Set X} (hE : IsCompact E) :
    ∃ F, E ⊆ F ∧ IsCompact F ∧ IsPreconnected F :=
  exists_isCompact_isPreconnected_superset (fun _ =>
    let ⟨C, hC, _, hCc, hCp⟩ := exists_isCompact_isPreconnected_mem_nhds_subset univ_mem
    ⟨C, hC, hCc, hCp⟩) hE

end Topology

section Generating

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [ChartedSpace X M]

/-- **« tout compact $E$ de $V$ est inclus dans un domaine générateur connexe »** (proof of
Prop. 7, first paragraph), for any `(G, X)`-manifold on a locally compact, locally connected
Hausdorff model: if `M` is preconnected and sweepable for `G₁`, every compact `E` lies in a
compact preconnected generating domain `F` (`⋃_{g ∈ G₁} gF = M`). -/
theorem IsBalayableFor.exists_domaineGenerateur [LocallyCompactSpace X] [LocallyConnectedSpace X]
    [T2Space X] [PreconnectedSpace M] {G₁ : Subgroup (GXAut G X M)}
    (hG : IsBalayableFor G X M G₁) {E : Set M} (hE : IsCompact E) :
    ∃ F, E ⊆ F ∧ IsCompact F ∧ IsPreconnected F ∧ ⋃ g ∈ G₁, g • F = univ := by
  obtain ⟨K, hK, hKU⟩ := hG
  obtain ⟨F, hF, hFc, hFp⟩ := exists_isCompact_isPreconnected_superset
    (exists_isCompact_isPreconnected_mem_nhds_of_chartedSpace (X := X)) (hE.union hK)
  refine ⟨F, subset_union_left.trans hF, hFc, hFp, eq_univ_of_univ_subset (hKU ▸ ?_)⟩
  exact iUnion₂_mono fun g _ => smul_set_mono (subset_union_right.trans hF)

end Generating

section Proj

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **The first paragraph of the proof of Prop. 7, for a locally projective `V`**: a preconnected
`V`, sweepable for a group `G` of projective automorphisms; every compact `E` of `V` lies in a
compact preconnected generating domain. -/
theorem exists_domaineGenerateur_proj [PreconnectedSpace V]
    {G : Subgroup (GXAut (GSR n) (S n) V)} (hG : IsBalayableFor (GSR n) (S n) V G) {E : Set V}
    (hE : IsCompact E) :
    ∃ F, E ⊆ F ∧ IsCompact F ∧ IsPreconnected F ∧ ⋃ g ∈ G, g • F = univ := by
  haveI := locPathConnectedSpace_S n
  exact hG.exists_domaineGenerateur hE

/-- The same with « connexe » read as `IsConnected` (nonempty), for a connected `V`. -/
theorem exists_domaineGenerateur_proj_isConnected [ConnectedSpace V]
    {G : Subgroup (GXAut (GSR n) (S n) V)} (hG : IsBalayableFor (GSR n) (S n) V G) {E : Set V}
    (hE : IsCompact E) :
    ∃ F, E ⊆ F ∧ IsCompact F ∧ IsConnected F ∧ ⋃ g ∈ G, g • F = univ := by
  obtain ⟨F, hEF, hF, hFp, hFG⟩ := exists_domaineGenerateur_proj hG hE
  obtain ⟨x⟩ : Nonempty V := inferInstance
  obtain ⟨g, -, y, hy, -⟩ := mem_iUnion₂.1 (hFG ▸ mem_univ x)
  exact ⟨F, hEF, hF, ⟨⟨y, hy⟩, hFp⟩, hFG⟩

variable [HasGroupoid V (projGroupoid n)]

/-- **A projective automorphism maps a broken line onto a broken line** (2° segment by segment,
`IsMajoreSeg.smul`). -/
theorem IsLigneBrisee.smul (g : GXAut (GSR n) (S n) V) {k : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) : IsLigneBrisee n k p (g • M) (g • N) (g • L) := by
  induction h with
  | segment hS => exact IsLigneBrisee.segment (hS.smul g)
  | cons hS _ ih =>
    rw [smul_set_union]
    exact IsLigneBrisee.cons (hS.smul g) ih

variable {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **Prop. 7** (`bzprop:c2s2p7_compact_dans_poche`), every dimension. -/
theorem compact_dans_poche [PreconnectedSpace V] {G : Subgroup (GXAut (GSR n) (S n) V)}
    (hG : IsBalayableFor (GSR n) (S n) V G) (hP : IsPocheProj P l φ z) {E : Set V}
    (hE : IsCompact E) : ∃ g ∈ G, g • E ⊆ P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- dimension `0`: a connected `V` has at most one point, and `P` is nonempty
    haveI := subsingleton_dim_zero (V := V)
    obtain ⟨x, hx⟩ := hP.isConnected.nonempty
    exact ⟨1, G.one_mem, fun y _ => Subsingleton.elim x y ▸ hx⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  -- a compact connected generating domain `F ⊇ E`
  obtain ⟨F, hEF, hF, hFp, hFG⟩ := exists_domaineGenerateur_proj hG hE
  -- `k = log 2`, `K = 2`; `M⁰ ∈ P` of cote `< 1/2^{n(F, k)}`
  obtain ⟨_, ⟨y, hy, rfl⟩, -, hylt⟩ := hP.isGLB.exists_between
    (show (0 : ℝ) < 1 / 2 ^ nombreRecouvrement n (Real.log 2) F by positivity)
  obtain ⟨M₀, hM₀, hφM₀⟩ := hy
  have hz : z ⟨φ M₀, hP.mapsTo_hemi hM₀⟩ = z y := congrArg z (Subtype.ext hφM₀)
  -- `g N⁰ = M⁰`, `N⁰ ∈ F`
  obtain ⟨g, hg, N₀, hN₀, hgN₀⟩ := mem_iUnion₂.1 (hFG ▸ mem_univ M₀)
  refine ⟨g, hg, (smul_set_mono hEF).trans ?_⟩
  rintro _ ⟨N, hN, rfl⟩
  -- Prop. 4: a broken line from `N⁰` to `N` of `p ≤ n(F, k)` segments majorised by `k`
  obtain ⟨p, L, hp, hL⟩ :=
    ligne_brisee (n := n) hF hFp (Real.log_pos (one_lt_two : (1 : ℝ) < 2)) hN₀ hN
  have hL' := hL.smul g
  simp only at hgN₀
  rw [hgN₀] at hL'
  -- Prop. 6 (corrected form, every pocket): `g N ∈ P`
  have hlt : z ⟨φ M₀, hP.mapsTo_hemi hM₀⟩ < 1 / 2 ^ p := by
    rw [hz]
    exact hylt.trans_le (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (one_le_two : (1 : ℝ) ≤ 2) hp))
  exact (hP.ligne_brisee_poche hL' hM₀ hlt).2.1

/-- **Corollary of Prop. 7** (`bzcor:c2s2p7c_deux_points_dans_poche`), every dimension. -/
theorem deux_points_dans_poche [PreconnectedSpace V] {G : Subgroup (GXAut (GSR n) (S n) V)}
    (hG : IsBalayableFor (GSR n) (S n) V G) (hP : IsPocheProj P l φ z) (M N : V) :
    ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P := by
  obtain ⟨g, hg, hgP⟩ := compact_dans_poche hG hP (isCompact_singleton.insert M : IsCompact {M, N})
  exact ⟨g, hg, hgP (smul_mem_smul_set (mem_insert M {N})),
    hgP (smul_mem_smul_set (mem_insert_of_mem M rfl))⟩

end Proj

/-! ### The printed statements, over the paper's manifolds, in every dimension -/

/-- **Prop. 7 as printed**, over the locally projective `n`-manifolds of the paper (Hausdorff,
connected, second countable; `V : Type`): for every group `G` of projective automorphisms for which
`V` is sweepable, every pocket `(P, H̊, φ, z)` and every compact `E`, some `g ∈ G` has `gE ⊆ P`. -/
def CompactDansPochePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V]
    (G : Subgroup (GXAut (GSR n) (S n) V)), IsBalayableFor (GSR n) (S n) V G →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∀ E : Set V, IsCompact E → ∃ g ∈ G, g • E ⊆ P

/-- **The corollary of Prop. 7 as printed**, over the same manifolds. -/
def DeuxPointsDansPochePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V]
    (G : Subgroup (GXAut (GSR n) (S n) V)), IsBalayableFor (GSR n) (S n) V G →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∀ M N : V, ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P

/-- **Prop. 7 holds as printed in every dimension**, `n = 0` included (no OQ-45 dependence). -/
theorem compactDansPochePrinted (n : ℕ) : CompactDansPochePrinted n :=
  fun _ _ _ _ _ _ _ _ hG _ _ _ _ _ hP _ hE => compact_dans_poche hG hP hE

/-- **The corollary holds as printed in every dimension.** -/
theorem deuxPointsDansPochePrinted (n : ℕ) : DeuxPointsDansPochePrinted n :=
  fun _ _ _ _ _ _ _ _ hG _ _ _ _ _ hP M N => deux_points_dans_poche hG hP M N

end Benzecri
