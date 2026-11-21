import Benzecri.Chapter2.CasAffin
import Benzecri.Chapter2.Developpement

/-!
# Chapter 2 § 3, the affine Theorem's 1° — a connected sweepable locally affine manifold with a pocket `(P, φ, z)` has a compatible chart onto an open set of `ℝⁿ` extending `φ`, and the pocket is a connected component of the preimage of `z < 1`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 255–256; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-premier-affine.

* `bzthm:c2s3t2_poche_balayable_affine` — `benzecri1960_ch2.tex:627`, its 1° only (statement
  l.628–633, proof l.643–646). Not marked: the row is assembled by T-bz-c2-theoreme-affine, and the
  second sentence of 1° is proved here in its component form only (SCOPE).

> Dans le cas affin, on a le
>
> **Théorème.** Soit $V$ une variété localement affine connexe balayable. Soit $(P, \varphi, z)$
> une poche de $V$.
>
> 1° Il existe une carte compatible $\tilde{\varphi}$ de $V$ sur un ouvert de $\R^n$. $P$ n'est
> autre que l'image réciproque par $\tilde{\varphi}$ de l'ensemble des points où $z<1$.
>
> […] Le théorème se démontre comme le précédent : il suffit de remplacer projectif par affin, et
> $S(n)$ ou $\mathring{H}$ par $\R^n$.

And the forward reference after the examples of § 1 (l.181–186), in its affine reading: « si $V$
est une variété localement projective (resp. affine) connexe balayable, possédant une poche
$(P, \mathring{H}, \varphi, z)$ [resp. $(P, \varphi, z)$], on est toujours dans la situation
considérée en exemple. $\varphi$ se prolonge en une application projective (resp. affine) de $V$
sur $S(n)$ (resp. $\R^n$) et $P$ n'est autre qu'une composante connexe de l'image réciproque par
$\varphi$ du demi-espace ouvert de $\mathring{H}$ (resp. $\R^n$) d'équation $z<1$. »

## What is proved (no `sorry`)

* 1°a and 1°b stated once for any `(G, X)` (namespace `PremierGX`), from two facts only: a compatible
  chart `φ` whose source `P` is connected, and every compact set moved into `P` by an automorphism.
  The key step `PremierGX.chemin_jets_ferme` (a path of `J(M)` over a loop is closed), the developing
  map `PremierGX.exists_isDeveloping_eqOn`, injectivity of EVERY developing map
  `PremierGX.injective_of_isDeveloping`, the chart `PremierGX.exists_chart_eqOn`, its uniqueness
  `PremierGX.eq_of_eqOn`. Instantiated at `GA(n, ℝ)` through Prop. 7′ (`compact_dans_poche_affine`,
  `IsPocheAff.forall_compact_smul_subset`).
* 1°a, affine: `exists_isDeveloping_eqOn_poche_affine`, `chemin_jets_ferme_affine`,
  `jets_produit_affine`. 1°b: `injective_of_isDeveloping_of_poche_affine`; the chart:
  `exists_chart_poche_affine`; it is unique: `IsDeveloping.eq_of_eqOn_poche_affine`.
* 1°c, component form: `poche_eq_connectedComponentIn_affine`. The full form:
  `poche_eq_preimage_iff_affine` (it holds iff `{z < 1} ∩ φ̃(V)` is preconnected),
  `poche_eq_preimage_of_cote_eq_zero_affine` (it holds for `z ≡ 0`, the only constant cote:
  `IsPocheAff.cote_eq_zero_of_linear_eq_zero`), `poche_eq_preimage_of_starConvex_affine` and
  `poche_eq_preimage_of_convex_affine` (it holds when `φ̃(V)` is star-shaped about a point of
  cote `< 1`, in particular convex). In dimension `n ≤ 1` the printed full form holds:
  `premierAffinePrinted_of_le_one` (`φ̃(V)` is an interval or a point). Not proved for a
  non-constant cote in dimension `n ≥ 2`.
* 1° in one piece: `theoreme_premier_affine`. Printed forms: `premierComposanteAffinePrinted n` for
  every `n`; `premierAffinePrinted_iff n` (`PremierAffinePrinted n ↔ ConnexeAffinePrinted n`); the
  literal reading without « induisant $\varphi$ sur $P$ »: `PremierAffinePrinted.literal`.
* The forward reference l.181–186, affine case: `situation_exemple_affine`; the affine example of
  § 1 without « `p` injective on `P` » in this situation: `exemple_poche_affine_of_poche`.
* Non-vacuity: `theoreme_premier_affine_model` (`ℝⁿ` swept by its translations, every `n`, `z ≡ 0`,
  `P = V`, full form included) and `theoreme_premier_affine_demiEspace` (the half-space
  `{x₀ > 0} ⊂ ℝⁿ⁺¹`, every `n`, non-constant cote `x₀`, `P = {x₀ < 1} ≠ V`, full form included).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement affine » | ⚠ weakened: `[ChartedSpace (Fin n → ℝ) V]`, `[HasGroupoid V (affGroupoid n)]`; Hausdorff and second countable never used (the printed forms carry them) |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the pocket makes `V` nonempty) |
| `V` balayable | ✓ carried: `IsBalayable (GAR n) (Fin n → ℝ) V` (Ch. 1, Déf. 15: for the group of all affine automorphisms) |
| `(P, φ, z)` une poche de `V` | ✓ carried: `IsPocheAff P φ z` (Déf. 1, strict) |
| the dimension | ✓ every `n`, `n = 0` included (no `NeZero n`) |
| 1°: « une carte compatible $\tilde\varphi$ de $V$ sur un ouvert de $\R^n$ » | ✓ carried, and more: `OpenPartialHomeomorph` (open target), `IsCompatibleChart`, `source = univ`, and `EqOn φ̃ φ P` (« induisant $\varphi$ sur $P$ », not printed in the affine 1°: settled by the text, SCOPE) |
| 1°: « $P$ n'est autre que l'image réciproque par $\tilde\varphi$ de l'ensemble des points où $z<1$ » | component form; full form iff `{z < 1} ∩ φ̃(V)` is preconnected, proved for `z ≡ 0`, for a star-shaped or convex `φ̃(V)`, and for `n ≤ 1` (SCOPE) |

## SCOPE (disclosed)

* **Not marked**, as dispatched: the row is assembled by T-bz-c2-theoreme-affine (2°–4°), and the
  second sentence of 1° is proved in its component form only.
* **1°c, the full form `P = φ̃⁻¹({z < 1} ∩ φ̃(V))` is not proved for a non-constant cote** (the
  affine twin of OQ-71). The proof is « comme le précédent » (l.644–645), whose 1°c (l.587–590)
  builds « dans $D\cap\tilde{\varphi}(V)$ une ligne brisée » and so presumes that set connected; the
  forward reference (l.184–186) claims only « une composante connexe ». Proved: the component form;
  the full form iff `{z < 1} ∩ φ̃(V)` is preconnected (for one `V`, and for the printed statement);
  the full form for `z ≡ 0`, when `φ̃(V)` is star-shaped about a point of cote `< 1` (so for a
  convex `φ̃(V)`, which 3° gives for a shell), in every dimension `n ≤ 1`, and on the half-space
  witness, whose cote is not constant. Neither proved nor refuted for a non-constant cote in
  dimension `n ≥ 2`.
* **« induisant $\varphi$ sur $P$ » is not printed in the affine 1°** (l.631–632; the scan, p. 256,
  agrees with the transcription), although the projective 1° prints it (l.522–523). The text
  settles it: the forward reference « $\varphi$ se prolonge en une application … (resp. affine) »
  (l.184–185; scan p. 248) asserts the extension in the affine case, and « comme le précédent »
  (l.644–645) carries the projective 1° over. Read as present: every statement here carries
  `EqOn φ̃ φ P`, which is stronger, and it is what ties `z` to `φ̃` in the second sentence; the
  literal form (some chart, no `EqOn`) follows (`PremierAffinePrinted.literal`). An omission at the
  level of a misprint, not a question.
* « comme le précédent : il suffit de remplacer projectif par affin, et $S(n)$ ou $\mathring{H}$
  par $\R^n$ » (l.644–645): the projective 1° (`Benzecri.Chapter2.Developpement`) re-run. 1°a and 1°b
  are proved once for any `(G, X)` with the rigidity of `IsDeveloping.existsUnique_smul_eq`, then
  instantiated; `D` is read `{z < 1} ⊆ ℝⁿ`; the convex neighbourhood of 1°c is a ball of `ℝⁿ`.
  Condition *b* of Déf. 1 has no hemisphere clause, so `z ≡ 0` needs no twin of
  `closure_poche_subset_preimage_hemisphere`. Not derived from the projective 1° through
  `GXAut.affToProj`: that would need `φ̃(V)` inside the hemisphere `j(ℝⁿ)`, which is not known in
  advance (it follows from the affine 1°).
* Independent of OQ-61: nothing here assumes a non-constant cote. Under OQ-61 (a) the `ℝⁿ` witness
  (`z ≡ 0`) would no longer be a pocket; the half-space witness would.
* The inclusion `P ⊆ φ̃⁻¹(z < 1)`, which the proof does not argue, needs `z < 1` on `φ(P)` where
  condition *a* gives `z ≤ 1` (`IsPocheAff.cote_lt_one`).
* « sur » in the proof's « application de $V$ sur $S(n)$ », read with $\R^n$ for $S(n)$, is read
  « dans » (into), as in the projective file; onto is false on the half-space witness, where
  `φ̃(V)` is the half-space. 1° itself says « sur un ouvert de $\R^n$ ». A usage note.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology unitInterval
open scoped Pointwise

namespace Benzecri

universe u

/-! ### 1°a and 1°b for any `(G, X)`: an open connected chart domain into which every compact set
can be moved -/

namespace PremierGX

section General

variable {M : Type u} [TopologicalSpace M] {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
  [MulAction G X] [ContinuousConstSMul G X] [IsAnalyticAction G X] [ChartedSpace X M]
  [HasGroupoid M (gxGroupoid G X)]

omit [IsAnalyticAction G X] in
/-- A compatible chart composed with an automorphism of `M` is compatible (for any `(G, X)`; the
projective case is `IsCompatibleChart.trans_aut`). -/
theorem isCompatibleChart_trans_aut {φ : OpenPartialHomeomorph M X}
    (hφ : IsCompatibleChart G φ) (g : GXAut G X M) :
    IsCompatibleChart G (g.toHomeomorph.toOpenPartialHomeomorph.trans φ) := by
  rw [isCompatibleChart_iff] at hφ ⊢
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  have hx' : g • x ∈ φ.source := by simpa [GXAut.smul_def] using hx
  obtain ⟨h, hh⟩ := g.isGXMorphism.exists_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid _ _).chart_mem_maximalAtlas x) hφ (mem_chart_source _ x) hx'
  exact ⟨h, by simpa [GXAut.smul_def] using hh⟩

/-- **1°a, the key step, for any `(G, X)`**: if every compact set of `M` can be moved by an
automorphism into the source `P` of one compatible chart, a path `[j, j']` of `J(M)` whose
projection is a loop is closed. -/
theorem chemin_jets_ferme {P : Set M} {φ : OpenPartialHomeomorph M X}
    (hφ : IsCompatibleChart G φ) (hs : φ.source = P)
    (hmove : ∀ E : Set M, IsCompact E → ∃ g : GXAut G X M, g • E ⊆ P)
    (Γ : C(I, jets G X M)) (hΓ : (Γ 0).1.1 = (Γ 1).1.1) : Γ 0 = Γ 1 := by
  have hK : IsCompact (range fun t => (Γ t).1.1) :=
    isCompact_range (continuous_jetSource.comp (continuous_subtype_val.comp Γ.continuous))
  obtain ⟨g, hg⟩ := hmove _ hK
  have hψ := isCompatibleChart_iff.1 (isCompatibleChart_trans_aut hφ g)
  have hsrc : ∀ t, (Γ t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
    intro t
    have : g • (Γ t).1.1 ∈ P := hg (smul_mem_smul_set (mem_range_self t))
    simpa [GXAut.smul_def, hs] using this
  apply Subtype.ext
  rw [jetSMul_eq_of_path hψ Γ hsrc 0, jetSMul_eq_of_path hψ Γ hsrc 1, hΓ]

/-- **1°a for any `(G, X)`**: `M` connected and locally path connected, `φ` a compatible chart
whose source `P` is connected, and every compact set movable into `P` by an automorphism; then
there is a developing map `p : M → X` equal to `φ` on `P`. -/
theorem exists_isDeveloping_eqOn [PreconnectedSpace M] [LocPathConnectedSpace M] {P : Set M}
    {φ : OpenPartialHomeomorph M X} (hφ : IsCompatibleChart G φ) (hs : φ.source = P)
    (hP : IsConnected P) (hmove : ∀ E : Set M, IsCompact E → ∃ g : GXAut G X M, g • E ⊆ P) :
    ∃ p : M → X, IsDeveloping G p ∧ EqOn p φ P := by
  obtain ⟨x₀, hx₀⟩ := hP.nonempty
  haveI : ConnectedSpace M := { toNonempty := ⟨x₀⟩ }
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hx₀φ : x₀ ∈ φ.source := hs ▸ hx₀
  let e₀ : jets G X M := ⟨jet x₀ φ, hφ x₀ hx₀φ⟩
  have cov := isCoveringMap_jets M X G
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ := cov.isLocalHomeomorph.existsUnique_continuousMap_lifts
    (ContinuousMap.id M) x₀ e₀ rfl (fun γ hγ => by
      simpa [and_comm] using cov.exists_path_lifts ((ContinuousMap.id M).comp γ) e₀
        (by rw [ContinuousMap.comp_apply, ContinuousMap.id_apply, hγ]; rfl))
    (fun γ γ' Γ Γ' hγ hγ' hΓ hΓ' hlift hlift' h1 => by
      -- the hypothesis moves both paths into `P`, the source of the chart `φ ∘ g`
      have hK : IsCompact (range γ ∪ range γ') :=
        (isCompact_range γ.continuous).union (isCompact_range γ'.continuous)
      obtain ⟨g, hg⟩ := hmove _ hK
      have hψ := isCompatibleChart_iff.1 (isCompatibleChart_trans_aut hφ g)
      have hl : ∀ t, (Γ t).1.1 = γ t := fun t => congrFun hlift t
      have hl' : ∀ t, (Γ' t).1.1 = γ' t := fun t => congrFun hlift' t
      have hsrc : ∀ t, (Γ t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
        intro t
        have : g • γ t ∈ P := hg (smul_mem_smul_set (Or.inl (mem_range_self t)))
        rw [hl t]
        simpa [GXAut.smul_def, hs] using this
      have hsrc' : ∀ t, (Γ' t).1.1 ∈ (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
        intro t
        have : g • γ' t ∈ P := hg (smul_mem_smul_set (Or.inr (mem_range_self t)))
        rw [hl' t]
        simpa [GXAut.smul_def, hs] using this
      apply Subtype.ext
      rw [jetSMul_eq_of_path hψ Γ hsrc 1, jetSMul_eq_of_path hψ Γ' hsrc' 1, hΓ, hΓ', hl 1, hl' 1,
        h1])
  have hsec : ∀ x, (F x).1.1 = x := fun x => congrFun hF x
  have hp := isDeveloping_developingOfSection F.continuous hsec
  have hgerm : (φ : M → X) =ᶠ[𝓝 x₀] developingOfSection F := by
    have h := jet_developingOfSection F.continuous hsec x₀
    rw [hF₀] at h
    exact (jet_eq_jet_iff.1 h).symm
  refine ⟨developingOfSection F, hp, fun x hx => ?_⟩
  exact (eqOn_of_germ_eq_isDeveloping hφ hp hP.isPreconnected hs.symm.subset hx₀ hgerm hx).symm

/-- **1°b for any `(G, X)`**, for EVERY developing map: under the hypotheses of
`exists_isDeveloping_eqOn`, a developing map `p : M → X` is injective. -/
theorem injective_of_isDeveloping [PreconnectedSpace M] [LocPathConnectedSpace M] {P : Set M}
    {φ : OpenPartialHomeomorph M X} (hφ : IsCompatibleChart G φ) (hs : φ.source = P)
    (hP : IsConnected P) (hmove : ∀ E : Set M, IsCompact E → ∃ g : GXAut G X M, g • E ⊆ P)
    {p : M → X} (hp : IsDeveloping G p) : Function.Injective p := by
  obtain ⟨x₀, hx₀⟩ := hP.nonempty
  haveI : Nonempty M := ⟨x₀⟩
  -- `p = c • φ̃` and `φ̃ = φ` on `P`
  obtain ⟨p₀, hp₀, hp₀φ⟩ := exists_isDeveloping_eqOn hφ hs hP hmove
  obtain ⟨c, hc, -⟩ := hp₀.existsUnique_smul_eq hp
  intro A B hAB
  -- `g` with `gA, gB ∈ P`, and `γ` with `p ∘ g = γ ∘ p`
  obtain ⟨g, hg⟩ := hmove {A, B} (isCompact_singleton.insert A)
  have hgA : g • A ∈ P := hg (smul_mem_smul_set (mem_insert A {B}))
  have hgB : g • B ∈ P := hg (smul_mem_smul_set (mem_insert_of_mem A rfl))
  have hpg : IsDeveloping G (fun y => p (g • y)) :=
    isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
  obtain ⟨γ, hγ, -⟩ := hp.existsUnique_smul_eq hpg
  have h1 : p (g • A) = p (g • B) := by rw [hγ A, hγ B, hAB]
  have h2 : φ (g • A) = φ (g • B) := by
    rw [hc, hc] at h1
    rw [← hp₀φ hgA, ← hp₀φ hgB]
    exact MulAction.injective c h1
  have h3 : g • A = g • B := φ.injOn (hs.symm ▸ hgA) (hs.symm ▸ hgB) h2
  exact MulAction.injective g h3

omit [IsAnalyticAction G X] in
/-- An injective developing map is a compatible chart of `M` onto its (open) image (for any
`(G, X)`; the projective case is `exists_chart_of_injective`). -/
theorem exists_chart_of_injective [Nonempty M] {p : M → X} (hp : IsDeveloping G p)
    (hinj : Function.Injective p) :
    ∃ φ : OpenPartialHomeomorph M X, IsCompatibleChart G φ ∧ φ.source = univ ∧
      φ.target = range p ∧ ⇑φ = p := by
  have he := hp.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  refine ⟨he.toOpenPartialHomeomorph p, fun x _ => ?_, he.toOpenPartialHomeomorph_source _,
    he.toOpenPartialHomeomorph_target _, he.toOpenPartialHomeomorph_apply _⟩
  rw [he.toOpenPartialHomeomorph_apply]
  exact hp x

/-- **1°, first sentence, for any `(G, X)`**: a compatible chart `φ̃` with source `M`, equal to
`φ` on `P`. -/
theorem exists_chart_eqOn [PreconnectedSpace M] [LocPathConnectedSpace M] {P : Set M}
    {φ : OpenPartialHomeomorph M X} (hφ : IsCompatibleChart G φ) (hs : φ.source = P)
    (hP : IsConnected P) (hmove : ∀ E : Set M, IsCompact E → ∃ g : GXAut G X M, g • E ⊆ P) :
    ∃ φ' : OpenPartialHomeomorph M X, IsCompatibleChart G φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P := by
  obtain ⟨x₀, hx₀⟩ := hP.nonempty
  haveI : Nonempty M := ⟨x₀⟩
  obtain ⟨p, hp, hpφ⟩ := exists_isDeveloping_eqOn hφ hs hP hmove
  obtain ⟨φ', hφ', hs', -, he⟩ :=
    exists_chart_of_injective hp (injective_of_isDeveloping hφ hs hP hmove hp)
  exact ⟨φ', hφ', hs', fun x hx => by rw [he]; exact hpφ hx⟩

/-- **Uniqueness, for any `(G, X)`**: two developing maps equal to `φ` on a nonempty open `P`
are equal (rigidity, `IsDeveloping.existsUnique_smul_eq`). -/
theorem eq_of_eqOn [PreconnectedSpace M] {P : Set M} {φ : M → X} (hPo : IsOpen P)
    (hPne : P.Nonempty) {p p' : M → X} (hp : IsDeveloping G p) (hp' : IsDeveloping G p')
    (hpφ : EqOn p φ P) (hp'φ : EqOn p' φ P) : p = p' := by
  obtain ⟨x₀, hx₀⟩ := hPne
  haveI : Nonempty M := ⟨x₀⟩
  obtain ⟨c, hc, -⟩ := hp.existsUnique_smul_eq hp'
  have hc1 : c = 1 := hp.eq_of_eventuallyEq (x := x₀) (by
    filter_upwards [hPo.mem_nhds hx₀] with y hy
    rw [← hc y, hp'φ hy, ← hpφ hy, one_smul])
  funext y
  rw [hc y, hc1, one_smul]

end General

end PremierGX

/-! ### The cote is `< 1` on an affine pocket; segments through a chart -/

section Cote

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}

/-- **The cote is `< 1` on an affine pocket** (condition *a* gives `≤ 1`; `φ(P)` is open and an
affine function reaching its supremum at an interior point is constant, against `inf = 0`). -/
theorem IsPocheAff.cote_lt_one (hP : IsPocheAff P φ z) {M : V} (hM : M ∈ P) : z (φ M) < 1 := by
  rcases (hP.le_one M hM).lt_or_eq with h | h
  · exact h
  exfalso
  have hopen : IsOpen (φ '' P) := by
    rw [← hP.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  -- an affine function with a local maximum at an interior point has a zero linear part
  have hlin : ∀ u : Fin n → ℝ, z.linear u = 0 := by
    intro u
    have hc : Continuous fun t : ℝ => t • u + φ M :=
      (continuous_id.smul continuous_const).add continuous_const
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • u + φ M ∈ φ '' P :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [zero_smul, zero_add]
        exact hopen.mem_nhds ⟨M, hM, rfl⟩)
    have hle : ∀ᶠ t in 𝓝 (0 : ℝ), t * z.linear u ≤ 0 := hev.mono fun t ht => by
      obtain ⟨y, hy, hyt⟩ := ht
      have h1 := hP.le_one y hy
      rw [hyt, ← vadd_eq_add, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, h] at h1
      linarith
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hle
    have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h2 := @hball (-(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith)
    nlinarith
  -- so `z ≡ 1`, against `inf z = 0`
  have hconst : ∀ y, z y = 1 := fun y => by
    rw [← vsub_vadd y (φ M), AffineMap.map_vadd, hlin, zero_vadd]
    exact h
  have h10 : (1 : ℝ) ≤ 0 := hP.isGLB.2 (by
    rintro _ ⟨y, -, rfl⟩
    rw [hconst])
  linarith

/-- **The only constant cote of an affine pocket is `0`** (condition *a*: the infimum of a
constant on the nonempty `φ(P)` is that constant). So the full form of 1°c, proved below for
`z ≡ 0`, is open only for a non-constant cote. -/
theorem IsPocheAff.cote_eq_zero_of_linear_eq_zero (hP : IsPocheAff P φ z) (hz : z.linear = 0)
    (y : Fin n → ℝ) : z y = 0 := by
  obtain ⟨M, hM⟩ := hP.isConnected.nonempty
  have hconst : ∀ w, z w = z (φ M) := fun w => by
    rw [← vsub_vadd w (φ M), AffineMap.map_vadd, hz, LinearMap.zero_apply, zero_vadd]
  have himg : z '' (φ '' P) = {z (φ M)} := by
    ext t
    constructor
    · rintro ⟨w, -, rfl⟩
      exact hconst w
    · rintro rfl
      exact ⟨φ M, ⟨M, hM, rfl⟩, rfl⟩
  have hglb := hP.isGLB
  rw [himg] at hglb
  rw [hconst y]
  exact (isGLB_singleton.unique hglb)

/-- **A segment of `ℝⁿ` inside the target of a compatible chart is the image of a segment of
`V`** (the affine twin of `isProjSegment_of_chart`). -/
theorem isAffSegment_of_chart {ψ : OpenPartialHomeomorph V (Fin n → ℝ)}
    (hψ : IsCompatibleChart (GAR n) ψ) {a b : Fin n → ℝ} (hsub : segment ℝ a b ⊆ ψ.target) :
    IsAffSegment n (ψ.symm '' segment ℝ a b) (ψ.symm a) (ψ.symm b) := by
  have ha := hsub (left_mem_segment ℝ a b)
  have hb := hsub (right_mem_segment ℝ a b)
  refine ⟨ψ, hψ, ?_, ψ.map_target ha, ψ.map_target hb, trivial, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ψ.map_target (hsub hy)
  · rw [ψ.right_inv ha, ψ.right_inv hb]
    exact ψ.image_symm_image_of_subset_target hsub

end Cote

/-! ### The affine Theorem's 1° -/

section PremierAffine

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]
  {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}

/-- Prop. 7′ in the form the generic lemmas take: every compact set is moved into `P` by an
affine automorphism. -/
theorem IsPocheAff.forall_compact_smul_subset [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) :
    ∀ E : Set V, IsCompact E → ∃ g : GXAut (GAR n) (Fin n → ℝ) V, g • E ⊆ P := by
  intro E hE
  obtain ⟨g, -, hg⟩ := compact_dans_poche_affine (G := ⊤) hbal hP hE
  exact ⟨g, hg⟩

/-- **1°a, the paper's key step, affine case** (l.545–557 with « projectif » replaced by
« affin »): a path `[j, j']` of `J(V)` whose projection is a loop is closed. -/
theorem chemin_jets_ferme_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) (Γ : C(I, jets (GAR n) (Fin n → ℝ) V))
    (hΓ : (Γ 0).1.1 = (Γ 1).1.1) : Γ 0 = Γ 1 := by
  exact PremierGX.chemin_jets_ferme hP.compatible hP.source_eq
    (hP.forall_compact_smul_subset hbal) Γ hΓ

/-- **1°a, affine case**: a map `φ̃ : V → ℝⁿ` all of whose jets lie in `J(V)` (a developing map),
equal to `φ` on `P`. -/
theorem exists_isDeveloping_eqOn_poche_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) :
    ∃ p : V → Fin n → ℝ, IsDeveloping (GAR n) p ∧ EqOn p φ P := by
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  exact PremierGX.exists_isDeveloping_eqOn hP.compatible hP.source_eq hP.isConnected
    (hP.forall_compact_smul_subset hbal)

/-- **1°a, « le revêtement $J(V)$ de $V$ est isomorphe à un produit »**, affine case,
set-theoretically: every jet of `J(V)` at `x` is `g • jet x φ̃` for a unique `g ∈ GA(n, ℝ)`. -/
theorem jets_produit_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) :
    ∃ p : V → Fin n → ℝ, IsDeveloping (GAR n) p ∧ EqOn p φ P ∧
      ∀ (x : V) (γ : Germ (𝓝 x) (Fin n → ℝ)),
        (⟨x, γ⟩ : Jet V (Fin n → ℝ)) ∈ jets (GAR n) (Fin n → ℝ) V ↔
          ∃! g : GAR n, (⟨x, γ⟩ : Jet V (Fin n → ℝ)) = jetSMul g (jet x p) := by
  obtain ⟨p, hp, hpφ⟩ := exists_isDeveloping_eqOn_poche_affine hbal hP
  exact ⟨p, hp, hpφ, fun x γ => hp.existsUnique_jetSMul_eq x γ⟩

/-- **1°b, affine case**, for EVERY developing map: it is injective. -/
theorem injective_of_isDeveloping_of_poche_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) : Function.Injective p := by
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  exact PremierGX.injective_of_isDeveloping hP.compatible hP.source_eq hP.isConnected
    (hP.forall_compact_smul_subset hbal) hp

/-- **1°, first sentence, affine case** (l.631–632): a compatible chart `φ̃` of `V` (source `V`)
onto an open set of `ℝⁿ`, inducing `φ` on `P`. -/
theorem exists_chart_poche_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) :
    ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P := by
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  exact PremierGX.exists_chart_eqOn hP.compatible hP.source_eq hP.isConnected
    (hP.forall_compact_smul_subset hbal)

/-- **The chart of 1° is unique**, affine case: two developing maps equal to `φ` on `P` are
equal. -/
theorem IsDeveloping.eq_of_eqOn_poche_affine [PreconnectedSpace V] (hP : IsPocheAff P φ z)
    {p p' : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p) (hp' : IsDeveloping (GAR n) p')
    (hpφ : EqOn p φ P) (hp'φ : EqOn p' φ P) : p = p' := by
  exact PremierGX.eq_of_eqOn hP.isOpen hP.isConnected.nonempty hp hp' hpφ hp'φ

/-- **1°c, the closure step, affine case**: a point of `φ̃⁻¹(z < 1)` adherent to `P` lies in `P`
(a segment from a point of `P` inside a ball, and condition *b*). -/
theorem closure_inter_preimage_subset_poche_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    closure P ∩ p ⁻¹' {y | z y < 1} ⊆ P := by
  rintro N ⟨hNcl, hND⟩
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  obtain ⟨φ', hφ', hs, ht, he⟩ := PremierGX.exists_chart_of_injective hp
    (injective_of_isDeveloping_of_poche_affine hbal hP hp)
  subst he
  have hrange : IsOpen (range φ') := hp.isLocalHomeomorph.isOpenMap.isOpen_range
  have hzc : Continuous z := z.continuous_of_finiteDimensional
  -- a ball `B ⊆ {z < 1} ∩ φ̃(V)` around `φ̃(N)`, and a point `M ∈ P` over it
  have hO : IsOpen ({y | z y < 1} ∩ range φ') := (isOpen_lt hzc continuous_const).inter hrange
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO (φ' N) ⟨hND, mem_range_self N⟩
  obtain ⟨M, hMU, hMP⟩ := mem_closure_iff.1 hNcl (φ' ⁻¹' Metric.ball (φ' N) ε)
    (Metric.isOpen_ball.preimage hp.continuous) (Metric.mem_ball_self hε)
  -- the segment `(M, N)` of `V`, through the chart `φ̃`
  have hsub : segment ℝ (φ' M) (φ' N) ⊆ φ'.target := by
    rw [ht]
    exact ((convex_ball _ _).segment_subset hMU (Metric.mem_ball_self hε)).trans
      fun y hy => (hball hy).2
  have hseg := isAffSegment_of_chart hφ' hsub
  rw [φ'.left_inv (hs.symm ▸ mem_univ M), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
  -- condition `b` with `φ̃`, which has the germ of `φ` at `M`
  have hgerm : (φ' : V → Fin n → ℝ) =ᶠ[𝓝 M] φ :=
    Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hMP) hpφ
  exact hP.mem_of_segment _ M N hseg hMP φ' hφ' (hs.symm ▸ subset_univ _) hgerm hND

/-- **1°c, component form, affine case** (l.632–633 and the forward reference l.181–186): for
every developing map `p` equal to `φ` on `P`, `P` is the connected component of each of its points
in `p⁻¹(z < 1)`. -/
theorem poche_eq_connectedComponentIn_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) {x : V} (hx : x ∈ P) :
    P = connectedComponentIn (p ⁻¹' {y | z y < 1}) x := by
  have hPD : P ⊆ p ⁻¹' {y | z y < 1} := fun y hy => by
    show z (p y) < 1
    rw [hpφ hy]
    exact hP.cote_lt_one hy
  refine Subset.antisymm (hP.isConnected.isPreconnected.subset_connectedComponentIn hx hPD) ?_
  refine (isPreconnected_connectedComponentIn (F := p ⁻¹' {y | z y < 1}) (x := x))
    |>.subset_of_closure_inter_subset hP.isOpen ⟨x, mem_connectedComponentIn (hPD hx), hx⟩ ?_
  rintro y ⟨hycl, hyC⟩
  exact closure_inter_preimage_subset_poche_affine hbal hP hp hpφ
    ⟨hycl, connectedComponentIn_subset _ _ hyC⟩

/-- **1°c, the full form reduced to a connectedness, affine case**: `P = φ̃⁻¹({z < 1} ∩ φ̃(V))`
holds iff `{z < 1} ∩ φ̃(V)` is preconnected. -/
theorem poche_eq_preimage_iff_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) :
    P = p ⁻¹' ({y | z y < 1} ∩ range p) ↔ IsPreconnected ({y | z y < 1} ∩ range p) := by
  obtain ⟨x, hx⟩ := hP.isConnected.nonempty
  have hemb : IsOpenEmbedding p := hp.isLocalHomeomorph.isOpenEmbedding_of_injective
    (injective_of_isDeveloping_of_poche_affine hbal hP hp)
  rw [preimage_inter_range, ← image_preimage_eq_inter_range, hemb.isInducing.isPreconnected_image]
  have hcomp := poche_eq_connectedComponentIn_affine hbal hP hp hpφ hx
  constructor
  · intro h
    rw [← h]
    exact hP.isConnected.isPreconnected
  · intro h
    have hxD : x ∈ p ⁻¹' {y | z y < 1} := by
      rw [hcomp] at hx
      exact connectedComponentIn_subset _ _ hx
    rw [hcomp, h.connectedComponentIn hxD]

/-- **1°c, the full form, when `φ̃(V)` is star-shaped about a point `c` of cote `< 1`** (a
sufficient condition for the connectedness of `{z < 1} ∩ φ̃(V)`, which is then star-shaped about
`c`); in particular when `φ̃(V)` is convex (`poche_eq_preimage_of_convex_affine`). -/
theorem poche_eq_preimage_of_starConvex_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) {c : Fin n → ℝ} (hc : z c < 1)
    (hstar : StarConvex ℝ c (range p)) :
    P = p ⁻¹' ({y | z y < 1} ∩ range p) := by
  obtain ⟨x, -⟩ := hP.isConnected.nonempty
  have hcr : c ∈ range p := by
    have := hstar (mem_range_self x) zero_le_one le_rfl (add_zero 1)
    simpa using this
  have hD : Convex ℝ {y : Fin n → ℝ | z y < 1} := (convex_Iio (1 : ℝ)).affine_preimage z
  refine (poche_eq_preimage_iff_affine hbal hP hp hpφ).2 ?_
  exact (((hD.starConvex hc).inter hstar).isPathConnected ⟨hc, hcr⟩).isConnected.isPreconnected

/-- **1°c, the full form, when `φ̃(V)` is convex** (what 3° proves for a shell). -/
theorem poche_eq_preimage_of_convex_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) (hconv : Convex ℝ (range p)) :
    P = p ⁻¹' ({y | z y < 1} ∩ range p) := by
  obtain ⟨x, hx⟩ := hP.isConnected.nonempty
  have hzx : z (p x) < 1 := by
    rw [hpφ hx]
    exact hP.cote_lt_one hx
  exact poche_eq_preimage_of_starConvex_affine hbal hP hp hpφ hzx
    (hconv.starConvex (mem_range_self x))

/-- **1°c, the full form, for the constant cote**, affine case (`z ≡ 0`): then `P = V` and
`P = φ̃⁻¹({z < 1} ∩ φ̃(V))`. -/
theorem poche_eq_preimage_of_cote_eq_zero_affine [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hpφ : EqOn p φ P) (hz : ∀ y, z y = 0) :
    P = univ ∧ P = p ⁻¹' ({y | z y < 1} ∩ range p) := by
  have hall : p ⁻¹' {y | z y < 1} = univ :=
    eq_univ_of_forall fun y => show z (p y) < 1 by rw [hz]; exact zero_lt_one
  have hcl : closure P ⊆ P := fun y hy =>
    closure_inter_preimage_subset_poche_affine hbal hP hp hpφ ⟨hy, hall ▸ mem_univ y⟩
  have huniv : P = univ :=
    IsClopen.eq_univ ⟨isClosed_of_closure_subset hcl, hP.isOpen⟩ hP.isConnected.nonempty
  refine ⟨huniv, ?_⟩
  rw [preimage_inter_range, hall, huniv]

/-- **The affine Theorem's 1°** (`bzthm:c2s3t2_poche_balayable_affine`, l.631–633), in one piece:
a compatible chart `φ̃` with source `V`, inducing `φ` on `P`; `P` is the connected component of each
of its points in `φ̃⁻¹(z < 1)`; and `P = φ̃⁻¹({z < 1} ∩ φ̃(V))` iff `{z < 1} ∩ φ̃(V)` is
preconnected. -/
theorem theoreme_premier_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) :
    ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P ∧
      (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' {y | z y < 1}) x) ∧
      (P = φ' ⁻¹' ({y | z y < 1} ∩ range φ') ↔ IsPreconnected ({y | z y < 1} ∩ range φ')) := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche_affine hbal hP
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact ⟨φ', hφ', hs, hφ'φ, fun x hx => poche_eq_connectedComponentIn_affine hbal hP hp hφ'φ hx,
    poche_eq_preimage_iff_affine hbal hP hp hφ'φ⟩

/-- **« on est toujours dans la situation considérée en exemple », affine case** (the forward
reference, l.181–186): the developing map `φ̃` of 1° extends `φ`, is injective, `P` is a connected
component of `φ̃⁻¹(z < 1)`, and `z` has infimum `0` on `φ̃(P)`: the hypotheses of the affine example
of § 1 (l.155–166). -/
theorem situation_exemple_affine [PreconnectedSpace V] (hbal : IsBalayable (GAR n) (Fin n → ℝ) V)
    (hP : IsPocheAff P φ z) :
    ∃ p : V → Fin n → ℝ, IsDeveloping (GAR n) p ∧ EqOn p φ P ∧ Function.Injective p ∧
      (∀ x ∈ P, P = connectedComponentIn (p ⁻¹' {y | z y < 1}) x) ∧ IsGLB (z '' (p '' P)) 0 := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche_affine hbal hP
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  refine ⟨φ', hp, hφ'φ, injective_of_isDeveloping_of_poche_affine hbal hP hp,
    fun x hx => poche_eq_connectedComponentIn_affine hbal hP hp hφ'φ hx, ?_⟩
  rw [image_congr hφ'φ]
  exact hP.isGLB

/-- **The affine example of § 1 without « `p` injective on `P` »**, in the Theorem's situation
(the affine twin of `exemple_poche_projective_of_poche`): in a connected sweepable `V` with one
pocket, every developing map `p` is injective, so `exemple_poche_affine` applies with no injectivity
hypothesis. -/
theorem exemple_poche_affine_of_poche [PreconnectedSpace V]
    (hbal : IsBalayable (GAR n) (Fin n → ℝ) V) (hP : IsPocheAff P φ z) {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (z' : (Fin n → ℝ) →ᵃ[ℝ] ℝ) {x₀ : V} (hx₀ : z' (p x₀) < 1)
    (hinf : IsGLB (z' '' (p '' connectedComponentIn (p ⁻¹' {y | z' y < 1}) x₀)) 0) :
    ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
      EqOn φ' p (connectedComponentIn (p ⁻¹' {y | z' y < 1}) x₀) ∧
      IsPocheAff (connectedComponentIn (p ⁻¹' {y | z' y < 1}) x₀) φ' z' := by
  exact exemple_poche_affine hp z' hx₀ hinf
    (injective_of_isDeveloping_of_poche_affine hbal hP hp).injOn

end PremierAffine

/-! ### The printed statements, over the paper's manifolds -/

/-- **The affine 1° with « P n'est autre que » read as a connected component** (the forward
reference, l.181–186), over the paper's manifolds (Hausdorff, connected, second countable;
`V : Type`), the chart inducing `φ` on `P`. -/
def PremierComposanteAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
        ∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' {y | z y < 1}) x

/-- **The affine 1° as printed** (l.631–633), with the chart inducing `φ` on `P` (the projective
1°'s « induisant $\varphi$ sur $P$ », which the affine 1° does not print; SCOPE), and the full
form `P = φ̃⁻¹({z < 1} ∩ φ̃(V))` of the projective proof (l.586), over the paper's manifolds. -/
def PremierAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
        P = φ' ⁻¹' ({y | z y < 1} ∩ range φ')

/-- **The affine 1° literally as printed**: no « induisant $\varphi$ sur $P$ », so only SOME
compatible chart `φ̃` with source `V` and `P = φ̃⁻¹({z < 1} ∩ φ̃(V))`. Weaker than
`PremierAffinePrinted` (`PremierAffinePrinted.literal`). -/
def PremierAffineLiteralPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∃ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧
        P = φ' ⁻¹' ({y | z y < 1} ∩ range φ')

/-- **The connectedness the projective proof of 1°c presumes, affine case** (l.587–588, « on
peut construire dans $D\cap\tilde{\varphi}(V)$ une ligne brisée », with $D$ read `{z < 1}` of
`ℝⁿ`), over the paper's manifolds: for every pocket and the chart `φ̃` of 1°, `{z < 1} ∩ φ̃(V)` is
preconnected. -/
def ConnexeAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V],
    IsBalayable (GAR n) (Fin n → ℝ) V →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∀ φ' : OpenPartialHomeomorph V (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' → φ'.source = univ → EqOn φ' φ P →
        IsPreconnected ({y | z y < 1} ∩ range φ')

/-- **The component form of the affine 1° holds in every dimension.** -/
theorem premierComposanteAffinePrinted (n : ℕ) : PremierComposanteAffinePrinted n := by
  intro V _ _ _ _ _ _ hbal P φ z hP
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, -⟩ := theoreme_premier_affine hbal hP
  exact ⟨φ', hφ', hs, hφ'φ, hcomp⟩

/-- **The affine 1° as printed is exactly the connectedness its proof presumes**:
`PremierAffinePrinted n` holds iff `ConnexeAffinePrinted n` does. -/
theorem premierAffinePrinted_iff (n : ℕ) : PremierAffinePrinted n ↔ ConnexeAffinePrinted n := by
  constructor
  · intro h V _ _ _ _ _ _ hbal P φ z hP φ'' hφ'' hs'' hφ''φ
    obtain ⟨φ', hφ', hs, hφ'φ, hfull⟩ := h V hbal P φ z hP
    have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
    have hp'' : IsDeveloping (GAR n) φ'' := fun x => hφ'' x (hs''.symm ▸ mem_univ x)
    have heq : (φ' : V → Fin n → ℝ) = φ'' := hp.eq_of_eqOn_poche_affine hP hp'' hφ'φ hφ''φ
    rw [heq] at hfull
    exact (poche_eq_preimage_iff_affine hbal hP hp'' hφ''φ).1 hfull
  · intro h V _ _ _ _ _ _ hbal P φ z hP
    obtain ⟨φ', hφ', hs, hφ'φ, -, hiff⟩ := theoreme_premier_affine hbal hP
    exact ⟨φ', hφ', hs, hφ'φ, hiff.2 (h V hbal P φ z hP φ' hφ' hs hφ'φ)⟩

/-- The reading with « induisant $\varphi$ sur $P$ » implies the literal one. -/
theorem PremierAffinePrinted.literal {n : ℕ} (h : PremierAffinePrinted n) :
    PremierAffineLiteralPrinted n := by
  intro V _ _ _ _ _ _ hbal P φ z hP
  obtain ⟨φ', hφ', hs, -, hfull⟩ := h V hbal P φ z hP
  exact ⟨φ', hφ', hs, hfull⟩

/-- In dimension `n ≤ 1`, a preconnected part of `ℝⁿ` is convex (a point, or an interval). -/
theorem convex_of_isPreconnected_of_le_one {n : ℕ} (hn : n ≤ 1) {s : Set (Fin n → ℝ)}
    (hs : IsPreconnected s) : Convex ℝ s := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · exact Set.subsingleton_of_subsingleton.convex
  · let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
    have h1 : IsPreconnected (e '' s) := hs.image _ e.continuous.continuousOn
    have h2 := h1.convex.linear_preimage (e : (Fin 1 → ℝ) →ₗ[ℝ] ℝ)
    have h3 : (e : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) ⁻¹' (e '' s) = s :=
      preimage_image_eq s e.injective
    rwa [h3] at h2

/-- **The connectedness the proof presumes holds in dimension `n ≤ 1`**: `φ̃(V)` is then an
interval (or a point), so `{z < 1} ∩ φ̃(V)` is convex. -/
theorem connexeAffinePrinted_of_le_one {n : ℕ} (hn : n ≤ 1) : ConnexeAffinePrinted n := by
  intro V _ _ _ _ _ _ _ P φ z _ φ' hφ' hs _
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have hconv : Convex ℝ (range φ') :=
    convex_of_isPreconnected_of_le_one hn (isPreconnected_range hp.continuous)
  exact (((convex_Iio (1 : ℝ)).affine_preimage z).inter hconv).isPreconnected

/-- **The affine 1° holds as printed, full form included, in dimension `n ≤ 1`.** -/
theorem premierAffinePrinted_of_le_one {n : ℕ} (hn : n ≤ 1) : PremierAffinePrinted n :=
  (premierAffinePrinted_iff n).2 (connexeAffinePrinted_of_le_one hn)

/-! ### Non-vacuity -/

/-- **The hypotheses of the affine 1° are met in every dimension** (`n = 0` included): `ℝⁿ`,
connected, sweepable by its translations, with the pocket `(ℝⁿ, id, 0)` (`z ≡ 0`, `P = V`); the
conclusion of `theoreme_premier_affine` holds, the full form included. -/
theorem theoreme_premier_affine_model (n : ℕ) :
    IsBalayableFor (GAR n) (Fin n → ℝ) (Fin n → ℝ) (translationSubgroup n) ∧
    IsBalayable (GAR n) (Fin n → ℝ) (Fin n → ℝ) ∧
    IsPocheAff (univ : Set (Fin n → ℝ)) (OpenPartialHomeomorph.refl _) 0 ∧
    ∃ φ' : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' (OpenPartialHomeomorph.refl _) univ ∧
      (∀ x ∈ (univ : Set (Fin n → ℝ)),
        univ = connectedComponentIn (φ' ⁻¹' {y | (0 : (Fin n → ℝ) →ᵃ[ℝ] ℝ) y < 1}) x) ∧
      (univ : Set (Fin n → ℝ)) =
        φ' ⁻¹' ({y | (0 : (Fin n → ℝ) →ᵃ[ℝ] ℝ) y < 1} ∩ range φ') := by
  have hbal : IsBalayable (GAR n) (Fin n → ℝ) (Fin n → ℝ) :=
    (isBalayableFor_translationSubgroup n).isBalayable
  have hP := isPocheAff_model n
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, -⟩ := theoreme_premier_affine hbal hP
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact ⟨isBalayableFor_translationSubgroup n, hbal, hP, φ', hφ', hs, hφ'φ, hcomp,
    (poche_eq_preimage_of_cote_eq_zero_affine hbal hP hp hφ'φ fun _ => rfl).2⟩

/-- **The affine 1° on a non-degenerate example, in every dimension `n + 1 ≥ 1`**: the open
half-space `{x₀ > 0}` of `ℝⁿ⁺¹` (`demiEspaceOuvert`), connected, sweepable by its affine
automorphisms, with the pocket `P = {x₀ < 1} ≠ V` and the NON-CONSTANT cote `z = x₀`; the chart of
1° exists, `P` is the connected component of each of its points in `φ̃⁻¹(z < 1)`, and the full form
`P = φ̃⁻¹({z < 1} ∩ φ̃(V))` holds too. -/
theorem theoreme_premier_affine_demiEspace (n : ℕ) :
    ∃ φ : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
      IsPocheAff {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ≠ univ ∧
      (∃ y, (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y ≠ 0) ∧
      ∃ φ' : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
        IsCompatibleChart (GAR (n + 1)) φ' ∧ φ'.source = univ ∧
        EqOn φ' φ {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
        (∀ x ∈ {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1},
          {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} = connectedComponentIn
            (φ' ⁻¹' {y | (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1}) x) ∧
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} = φ' ⁻¹'
          ({y | (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1} ∩ range φ') := by
  obtain ⟨φ, hP, hφval, -⟩ := exists_isPocheAff_demiEspace n
  have hbal := isBalayable_demiEspaceOuvert n
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, hiff⟩ := theoreme_premier_affine hbal hP
  have hp' : IsDeveloping (GAR (n + 1)) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  -- the chart of 1° is the inclusion (uniqueness)
  have heq : (φ' : demiEspaceOuvert n → Fin (n + 1) → ℝ) = Subtype.val :=
    hp'.eq_of_eqOn_poche_affine hP (isDeveloping_val_demiEspaceOuvert n) hφ'φ hφval.symm
  refine ⟨φ, hP, ?_, ⟨fun _ => 1, ?_⟩, φ', hφ', hs, hφ'φ, hcomp, hiff.2 ?_⟩
  · intro h
    have h2 : (⟨fun _ => 2, show (0 : ℝ) < 2 by norm_num⟩ : demiEspaceOuvert n) ∈
        {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} := h ▸ mem_univ _
    exact absurd (show (2 : ℝ) < 1 from h2) (by norm_num)
  · show (1 : ℝ) ≠ 0
    exact one_ne_zero
  · rw [heq]
    have hset : {y : Fin (n + 1) → ℝ |
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap y < 1} ∩
        range (Subtype.val : demiEspaceOuvert n → Fin (n + 1) → ℝ) =
        {x : Fin (n + 1) → ℝ | 0 < x 0 ∧ x 0 < 1} := by
      ext y
      constructor
      · rintro ⟨h1, ⟨q, rfl⟩⟩
        exact ⟨q.2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, ⟨⟨y, h1⟩, rfl⟩⟩
    rw [hset]
    exact ((convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)).isPreconnected

end Benzecri
