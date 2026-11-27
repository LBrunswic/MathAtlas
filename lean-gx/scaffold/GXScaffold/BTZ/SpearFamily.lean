import GX.BTZ.Surgery
import GXScaffold.BTZ.CompleteCauchy

/-!
# `GXScaffold.BTZ.SpearFamily` — a locally finite family of disjoint spears around the BTZ points of a Cauchy surface (btz § 5.4)

Target T-btz-spear-family. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`). Row (unmarked,
partial; this file is step (1) of the Cauchy-completeness of `Reg M`,
`GX.E0RegComplete.regM_isCauchyComplete_of_complete`, assembled in
`GXScaffold/BTZ/RegCompleteLength.lean`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576, which cites the surgery of
  `prop:abs_max`'s proof (l.1090–1091) « in disjoint spear neighborhoods of `sing₀(M)` » (l.1574).

> Consider $\Sigma$ a Cauchy-surface of $M$ and $\Sigma^*$ the Cauchy-surface of $M^*$ obtained by
> applying point (ii) of Lemma \ref{lem:curve_extension} in disjoint spear neighborhoods of
> $\sing_0(M)$. (l.1574)

> Let $\Sigma$ be a Cauchy-surface of $M$, for each BTZ line $\Delta$ of $M$, one can apply
> successively Lemma \ref{lem:tube} to show $\Delta$ admits a spear neighborhood, Lemma
> \ref{lem:add_BTZ_param} to construct a spear neighborhood $\mathcal S_\Delta$ around $\Delta$ whose
> vertex in the past of $\Sigma$ and such that $\Sigma\cap \mathcal S_\Delta$ is a smooth spacelike
> circle in the shaft of $\mathcal S_\Delta$ […]. Since $M$ is Cauchy-compact, it admits finitely
> many BTZ-lines and one can take the spear neighborhoods $\mathcal S_\Delta$ disjoint with $\Delta$
> running across the BTZ lines of $M$. (l.1090–1091)

## What is proved (no `sorry` in this file; standard axioms only)

* `exists_lfSurgeryData` (and `exists_lfSurgeryData_of_rimC1`, which asks only a Cauchy surface
  with the `C¹` rim condition): for a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold `M` and a
  `C¹` spacelike complete Cauchy surface `S` (`IsE0C1CompleteCauchy`), an `LFSurgeryData M S`:
  a **countable**, **locally finite** family of **pairwise disjoint closed** spears
  (`E0Surgery.SpearSurgeryDatum`, B21 Lemmas 2.3 `lem:tube` and 2.4 `lem:add_BTZ_param`, with the
  graph of Lemma 2.6(ii)), indexed by `S ∩ sing₀(M)` (an equivalence `pt`), the point `pt i` on
  the ray of the `i`-th spear, `S`'s trace on each spear the graph of `τ_Σ` in the shaft, whose rim
  is a `C¹` circle (`rimC1`).
* The construction (the argument B21 does not print for infinitely many lines): the rays are
  locally finite (a BTZ point has a neighbourhood whose BTZ points are on its line,
  `E0LM.e0_sing_nhds_component`; distinct points of `S` are on distinct lines); along a compact
  exhaustion `K n` of `M`, each spear is thinned until it misses `K n` for every `n` below the
  first one its ray meets (`SpearSurgeryDatum.exists_radius_disjoint`: the spears of radius
  `R' → 0` are closed and decrease to the ray), which makes the spears locally finite; then each is
  thinned again until its head avoids the (closed, by local finiteness) union of the others, and
  `E0Surgery.SpearSurgeryDatum.disjoint_of_head` makes them pairwise disjoint.
* `LFSurgeryData.toSurgeryData`: a finite family is the strict `E0Surgery.SurgeryData`;
  `countable_inter_S0`: `S ∩ sing₀(M)` is countable.

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable |
| globally hyperbolic | ✓ `(CE M).GloballyHyperbolic` |
| Cauchy-maximal | ✓ `E0Spear.IsE0CauchyMaximal M` (`lem:tube`'s hypothesis) |
| Cauchy-complete (`S` smooth spacelike complete) | ✓ read `IsE0C1CompleteCauchy M S` (the row's reading, OQ-142); ⚠ weakened: only `cauchy` and `rim` are used (`exists_lfSurgeryData_of_rimC1`) |

## SCOPE (disclosed)

This is the data of the surgery only (step (1) of the Cauchy-completeness of `Reg M`). That `Σ*`
is a Cauchy surface of `Reg M` with infinitely many spears (step (2), `RegCompleteCauchy`) and that
it is complete (step (3), `RegCompleteLength`) are not proved here; `btzprop:reg_complete` stays partial for
its `𝔼₀` scope. The strict `E0Surgery.SurgeryData` (finite) is left as it
is. The reading `IsE0C1CompleteCauchy` is imported from `GXScaffold.BTZ.CompleteCauchy`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0SpearFamily

open E0 E0Spear E0Surgery E0RegComplete

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [SecondCountableTopology M] in
/-- A `C¹` spacelike complete Cauchy surface satisfies the strict `E0Surgery.RimC1` (its field
`rim`, verbatim). The rim condition, the spear data from it (`E0Surgery.exists_spearSurgeryDatum`,
`E0Surgery.exists_spearSurgeryDatum_cover`) and their thinning
(`E0Surgery.SpearSurgeryDatum.exists_shrink`) are the strict library's (T-gx-btz-cleanup). -/
theorem rimC1_of_isE0C1CompleteCauchy {S : Set M} (hS : IsE0C1CompleteCauchy M S) :
    RimC1 M S :=
  hS.rim

/-- **A thin enough spear misses a compact set its ray misses**: the spears `ψ(spear(v, R'))`,
`R' → 0`, are closed and decrease to the ray. -/
theorem exists_radius_disjoint (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (D : SpearSurgeryDatum M S) {K : Set M} (hK : IsCompact K)
    (hray : ∀ t, 0 ≤ t → D.ψ (E0Spear.yAxis D.v t) ∉ K) :
    ∃ R' > 0, R' ≤ D.R ∧ Disjoint (D.ψ '' E0Spear.spearY D.v R') K := by
  by_contra hne
  push Not at hne
  have hne' : ∀ R' > 0, R' ≤ D.R → (D.ψ '' E0Spear.spearY D.v R' ∩ K).Nonempty := fun R' h1 h2 =>
    Set.not_disjoint_iff_nonempty_inter.1 (hne R' h1 h2)
  set r : ℕ → ℝ := fun n => D.R / (n + 1) with hr
  have hrpos : ∀ n, 0 < r n := fun n => div_pos D.pos (by positivity)
  have hrle : ∀ n, r n ≤ D.R := fun n =>
    div_le_self D.pos.le (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  have hranti : ∀ n, r (n + 1) ≤ r n := fun n =>
    div_le_div_of_nonneg_left D.pos.le (by positivity) (by push_cast; linarith)
  set t : ℕ → Set M := fun n => D.ψ '' E0Spear.spearY D.v (r n) ∩ K with ht
  have hsubW : ∀ n, E0Spear.spearY D.v (r n) ⊆ D.W := fun n =>
    (image_mono (E0Spear.spear_mono le_rfl (hrle n))).trans D.spear_sub
  have hAcl : ∀ n, IsClosed (D.ψ '' E0Spear.spearY D.v (r n)) := fun n =>
    isClosed_image_spearY hGH D.isOpen (hsubW n) D.mor D.inj
  have htcl : ∀ n, IsClosed (t n) := fun n => (hAcl n).inter hK.isClosed
  have htd : ∀ n, t (n + 1) ⊆ t n := fun n =>
    inter_subset_inter_left _ (image_mono (image_mono (E0Spear.spear_mono le_rfl (hranti n))))
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd
    (fun n => hne' (r n) (hrpos n) (hrle n)) (hK.inter_left (hAcl 0)) htcl
  have hy' : ∀ n, y ∈ t n := fun n => mem_iInter.1 hy n
  obtain ⟨⟨_, ⟨x, hx, rfl⟩, hxy⟩, hyK⟩ := hy' 0
  have hrad : ∀ n, rad x ≤ r n := by
    intro n
    obtain ⟨⟨_, ⟨x', hx', rfl⟩, hx'y⟩, -⟩ := hy' n
    have hW : paperInY x ∈ D.W := hsubW 0 ⟨x, hx, rfl⟩
    have hW' : paperInY x' ∈ D.W := hsubW n ⟨x', hx', rfl⟩
    have heq : paperInY x' = paperInY x := D.inj hW' hW (hx'y.trans hxy.symm)
    have : x' = x := by
      have := congrArg paperOfY heq
      rwa [paperOfY_paperInY, paperOfY_paperInY] at this
    rw [← this]; exact hx'.2
  have hr0 : rad x = 0 := by
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (rad_nonneg x)
    obtain ⟨n, hn⟩ := exists_nat_gt (D.R / ε)
    have h1 : D.R / (n + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    have := hrad n
    simp only [hr] at this
    linarith
  have hx2 : x.2 = 0 := norm_eq_zero.1 hr0
  have hv : D.v ≤ x.1 := by
    have := hx.1; simp only [fcoord, hr0] at this; linarith
  refine hray (x.1 - D.v) (by linarith) ?_
  have : D.ψ (E0Spear.yAxis D.v (x.1 - D.v)) = y := by
    rw [← hxy]
    show D.ψ (paperInY ((D.v + (x.1 - D.v), 0) : E0)) = D.ψ (paperInY x)
    congr 2
    exact Prod.ext (by simp) hx2.symm
  rw [this]; exact hyK

variable (M) in
/-- **The data of the surgery for a Cauchy surface with possibly infinitely many BTZ points**
(B21 l.1090–1091 and btz l.1574, « disjoint spear neighborhoods of `sing₀(M)` »): a countable,
locally finite family of pairwise disjoint closed spears, one around each point of `S ∩ sing₀(M)`
(`pt`, that point on the spear's ray), `S`'s trace on each the graph of `τ_Σ` in the shaft (the
fields of `SpearSurgeryDatum`) whose rim is a `C¹` circle. -/
structure LFSurgeryData (S : Set M) where
  ι : Type
  countable : Countable ι
  D : ι → SpearSurgeryDatum M S
  pt : ι ≃ ↥(S ∩ E0CBG.S0 M)
  pt_ray : ∀ i, ∃ t, 0 < t ∧ ((pt i : M)) = (D i).ψ (E0Spear.yAxis (D i).v t)
  disjoint : Pairwise fun i j => Disjoint (D i).spearSet (D j).spearSet
  isClosed : ∀ i, IsClosed (D i).spearSet
  locallyFinite : LocallyFinite fun i => (D i).spearSet
  rimC1 : ∀ i, ContDiff ℝ 1 (rimFun (D i).τS (D i).R)

namespace LFSurgeryData

variable {S : Set M} (Dat : LFSurgeryData M S)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The point `pt i` lies in the `i`-th spear. -/
theorem pt_mem (i : Dat.ι) : ((Dat.pt i : M)) ∈ (Dat.D i).spearSet := by
  obtain ⟨t, ht, h⟩ := Dat.pt_ray i
  rw [h]
  exact ⟨_, E0Spear.yAxis_mem_spearY (Dat.D i).pos.le ht.le, rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The spears cover `S ∩ sing₀(M)`. -/
theorem covers : S ∩ E0CBG.S0 M ⊆ ⋃ i, (Dat.D i).spearSet := by
  intro y hy
  refine mem_iUnion.2 ⟨Dat.pt.symm ⟨y, hy⟩, ?_⟩
  have h := Dat.pt_mem (Dat.pt.symm ⟨y, hy⟩)
  rwa [Equiv.apply_symm_apply] at h

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **A finite family is the strict `E0Surgery.SurgeryData`.** -/
def toSurgeryData (h : Finite Dat.ι) : SurgeryData M S :=
  ⟨Dat.ι, h, Dat.D, Dat.disjoint, Dat.isClosed, Dat.covers⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `S ∩ sing₀(M)` is countable. -/
theorem countable_inter_S0 (Dat : LFSurgeryData M S) : (S ∩ E0CBG.S0 M).Countable := by
  haveI := Dat.countable
  have h : Countable ↥(S ∩ E0CBG.S0 M) := Dat.pt.symm.injective.countable
  exact Set.countable_coe_iff.1 h

end LFSurgeryData

/-- **Step (1) of the non-compact surgery** (B21 l.1090–1091, btz l.1574), for a Cauchy surface
with the `C¹` rim condition: a countable, locally finite family of pairwise disjoint closed
spears around `S ∩ sing₀(M)`. -/
theorem exists_lfSurgeryData_of_rimC1 (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) (hrim : RimC1 M S)
    (hmax : E0Spear.IsE0CauchyMaximal M) : Nonempty (LFSurgeryData M S) := by
  classical
  set ι := ↥(S ∩ E0CBG.S0 M)
  have hD : ∀ q : ι, ∃ D : SpearSurgeryDatum M S,
      q.1 ∈ connectedComponentIn (E0CBG.S0 M) D.p ∧
        ∃ t, 0 < t ∧ q.1 = D.ψ (E0Spear.yAxis D.v t) := fun q =>
    exists_spearSurgeryDatum_cover hGH hS hrim hmax q.2.1 q.2.2
  choose D₀ hDc t ht hqt using hD
  -- distinct points of `S` are on distinct lines
  have hsep : ∀ i j : ι, ∀ a : M, a ∈ connectedComponentIn (E0CBG.S0 M) (D₀ i).p →
      a ∈ connectedComponentIn (E0CBG.S0 M) (D₀ j).p → i = j := by
    intro i j a hai haj
    have hij : connectedComponentIn (E0CBG.S0 M) (D₀ i).p =
        connectedComponentIn (E0CBG.S0 M) (D₀ j).p := by
      rw [connectedComponentIn_eq hai, connectedComponentIn_eq haj]
    have hjS : j.1 ∈ S ∩ connectedComponentIn (E0CBG.S0 M) (D₀ j).p := ⟨j.2.1, hDc j⟩
    have hiS : i.1 ∈ S ∩ connectedComponentIn (E0CBG.S0 M) (D₀ j).p := ⟨i.2.1, hij ▸ hDc i⟩
    exact Subtype.ext (eq_of_mem_component hGH hS (D₀ j).p_mem hiS hjS)
  -- the rays
  set F : ι → Set M := fun i => (fun s => (D₀ i).ψ (E0Spear.yAxis (D₀ i).v s)) '' Ici 0 with hFdef
  have hF0 : ∀ i, F i ⊆ E0CBG.S0 M := by
    rintro i _ ⟨s, hs, rfl⟩; exact (D₀ i).ray.mem_S0 hs
  have hFc : ∀ i, F i ⊆ connectedComponentIn (E0CBG.S0 M) (D₀ i).p := by
    rintro i _ ⟨s, hs, rfl⟩; exact (D₀ i).ray_mem_component hs
  have hFne : ∀ i, (F i).Nonempty := fun i => ⟨_, 0, self_mem_Ici, rfl⟩
  -- the rays are locally finite
  have hFlf : LocallyFinite F := by
    intro x
    by_cases hx : x ∈ E0CBG.S0 M
    · obtain ⟨O, hO, hxO, hOsub⟩ := E0LM.e0_sing_nhds_component hx
      refine ⟨O, hO.mem_nhds hxO, Set.Subsingleton.finite ?_⟩
      have key : ∀ i, (F i ∩ O).Nonempty →
          x ∈ connectedComponentIn (E0CBG.S0 M) (D₀ i).p := by
        rintro i ⟨a, haF, haO⟩
        have ha1 : a ∈ connectedComponentIn (E0CBG.S0 M) x := hOsub ⟨haO, hF0 i haF⟩
        have ha2 := hFc i haF
        rw [connectedComponentIn_eq ha2, ← connectedComponentIn_eq ha1]
        exact mem_connectedComponentIn hx
      intro i hi j hj
      exact hsep i j x (key i hi) (key j hj)
    · refine ⟨(E0CBG.S0 M)ᶜ, isClosed_S0.isOpen_compl.mem_nhds hx, ?_⟩
      refine Set.finite_empty.subset fun i hi => ?_
      obtain ⟨a, haF, haO⟩ := hi
      exact haO (hF0 i haF)
  -- a compact exhaustion
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E0Y M
  set K := CompactExhaustion.choice M
  have hex : ∀ i, ∃ n, (F i ∩ K n).Nonempty := fun i => by
    obtain ⟨a, ha⟩ := hFne i
    obtain ⟨n, hn⟩ := K.exists_mem a
    exact ⟨n, a, ha, hn⟩
  set N : ι → ℕ := fun i => Nat.find (hex i) with hN
  -- first thinning: each spear misses `K n` for every `n` below the first its ray meets
  have hR₁ : ∀ i, ∃ R' > 0, R' ≤ (D₀ i).R ∧ ∀ n < N i,
      Disjoint ((D₀ i).ψ '' E0Spear.spearY (D₀ i).v R') (K n) := by
    intro i
    have hn : ∀ n : Fin (N i), ∃ R' > 0, R' ≤ (D₀ i).R ∧
        Disjoint ((D₀ i).ψ '' E0Spear.spearY (D₀ i).v R') (K n) := by
      intro n
      refine exists_radius_disjoint hGH (D₀ i) (K.isCompact n) fun s hs hsK => ?_
      exact Nat.find_min (hex i) n.2 ⟨_, ⟨s, hs, rfl⟩, hsK⟩
    choose r hrpos hrle hrdis using hn
    obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_of_finite r hrpos
    refine ⟨min ρ (D₀ i).R, lt_min hρ (D₀ i).pos, min_le_right _ _, fun n hn => ?_⟩
    refine (hrdis ⟨n, hn⟩).mono_left (image_mono (image_mono (E0Spear.spear_mono le_rfl ?_)))
    exact (min_le_left _ _).trans (hρle _)
  choose R₁ hR₁pos hR₁le hR₁dis using hR₁
  have hshr₁ : ∀ i, ∃ D' : SpearSurgeryDatum M S, D'.p = (D₀ i).p ∧ D'.ψ = (D₀ i).ψ ∧
      D'.v = (D₀ i).v ∧ D'.R = R₁ i := fun i => (D₀ i).exists_shrink hrim (hR₁pos i) (hR₁le i)
  choose D₁ hD₁p hD₁ψ hD₁v hD₁R using hshr₁
  have hD₁set : ∀ i, (D₁ i).spearSet = (D₀ i).ψ '' E0Spear.spearY (D₀ i).v (R₁ i) := fun i => by
    show (D₁ i).ψ '' E0Spear.spearY (D₁ i).v (D₁ i).R = _
    rw [hD₁ψ, hD₁v, hD₁R]
  have hlf₁ : LocallyFinite fun i => (D₁ i).spearSet := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem_nhds x
    refine ⟨K n, hn, (hFlf.finite_nonempty_inter_compact (K.isCompact n)).subset ?_⟩
    rintro i ⟨a, haD, haK⟩
    have hNi : N i ≤ n := by
      by_contra hlt
      push Not at hlt
      have haD' : a ∈ (D₁ i).spearSet := haD
      rw [hD₁set] at haD'
      exact Set.disjoint_left.1 (hR₁dis i n hlt) haD' haK
    obtain ⟨b, hbF, hbK⟩ := Nat.find_spec (hex i)
    exact ⟨b, hbF, K.subset hNi hbK⟩
  have hcl₁ : ∀ i, IsClosed (D₁ i).spearSet := fun i =>
    isClosed_image_spearY hGH (D₁ i).isOpen (D₁ i).spear_sub (D₁ i).mor (D₁ i).inj
  -- second thinning: the head of each spear avoids the union of the others
  set G : ι → Set M := fun j => ⋃ i, if i = j then ∅ else (D₁ i).spearSet with hG
  have hGcl : ∀ j, IsClosed (G j) := fun j => by
    refine LocallyFinite.isClosed_iUnion (hlf₁.subset fun i => ?_) fun i => ?_
    · split_ifs
      · exact empty_subset _
      · exact subset_rfl
    · split_ifs
      · exact isClosed_empty
      · exact hcl₁ i
  have hmemG : ∀ i j, i ≠ j → (D₁ i).spearSet ⊆ G j := fun i j hij y hy =>
    mem_iUnion.2 ⟨i, by rw [if_neg hij]; exact hy⟩
  have hpG : ∀ j, (D₁ j).p ∉ G j := by
    intro j hp
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    by_cases hij : i = j
    · rw [if_pos hij] at hi; exact hi
    · rw [if_neg hij] at hi
      have h1 := (D₁ i).spearSet_inter_S0_subset hi (D₁ j).p_mem
      rw [hD₁p, hD₁p] at h1
      have h2 : (D₀ j).p ∈ connectedComponentIn (E0CBG.S0 M) (D₀ j).p :=
        mem_connectedComponentIn (D₀ j).p_mem
      exact hij (hsep i j _ h1 h2)
  have hρ : ∀ j, ∃ ρ > 0, ∀ x : E0, fcoord x = (D₁ j).v → rad x ≤ ρ →
      (D₁ j).ψ (paperInY x) ∉ G j := fun j =>
    (D₁ j).exists_head_avoid (hGcl j) (hpG j)
  choose ρ hρpos hρ using hρ
  have hshr : ∀ j, ∃ D' : SpearSurgeryDatum M S, D'.p = (D₁ j).p ∧ D'.ψ = (D₁ j).ψ ∧
      D'.v = (D₁ j).v ∧ D'.R = min (ρ j) (D₁ j).R := fun j =>
    (D₁ j).exists_shrink hrim (lt_min (hρpos j) (D₁ j).pos) (min_le_right _ _)
  choose D hDp hDψ hDv hDR using hshr
  have hsub : ∀ j, (D j).spearSet ⊆ (D₁ j).spearSet := fun j => by
    show (D j).ψ '' E0Spear.spearY (D j).v (D j).R ⊆ _
    rw [hDψ, hDv, hDR]
    exact image_mono (image_mono (E0Spear.spear_mono le_rfl (min_le_right _ _)))
  have hlf : LocallyFinite fun i => (D i).spearSet := hlf₁.subset hsub
  have hpt : ∀ i : ι, ∃ s, 0 < s ∧ (i : M) = (D i).ψ (E0Spear.yAxis (D i).v s) := fun i =>
    ⟨t i, ht i, by rw [hDψ, hDv, hD₁ψ, hD₁v]; exact hqt i⟩
  have hne : ∀ i, ((fun i => (D i).spearSet) i).Nonempty := fun i => by
    obtain ⟨s, hs, h⟩ := hpt i
    exact ⟨_, _, E0Spear.yAxis_mem_spearY (D i).pos.le hs.le, rfl⟩
  have hcount : Countable ι := Set.countable_univ_iff.1 (hlf.countable_univ hne)
  refine ⟨⟨ι, hcount, D, Equiv.refl ι, hpt, ?_, fun i => isClosed_image_spearY hGH (D i).isOpen
    (D i).spear_sub (D i).mor (D i).inj, hlf, fun i => hrim (D i).R (D i).v (D i).W (D i).ψ
    (D i).τS (D i).pos (D i).isOpen (D i).spear_sub (D i).mor (D i).inj (D i).continuousOn
    (D i).shaft (D i).graph⟩⟩
  intro i j hij
  refine SpearSurgeryDatum.disjoint_of_head hGH (D i) (D j) ?_ ?_
  · intro s hs hmem
    have h0 : (D i).ψ (E0Spear.yAxis (D i).v s) ∈ E0CBG.S0 M := (D i).ray.mem_S0 hs
    have hci := (D i).ray_mem_component hs
    have hcj := (D j).spearSet_inter_S0_subset hmem h0
    rw [hDp, hD₁p] at hci hcj
    exact hij (hsep i j _ hci hcj)
  · intro x hx hfx hmem
    have hfx' : fcoord x = (D₁ j).v := by rw [hfx, hDv]
    have hrx : rad x ≤ ρ j := hx.2.trans ((hDR j).le.trans (min_le_left _ _))
    refine hρ j x hfx' hrx ?_
    rw [← hDψ]
    exact hmemG i j hij (hsub i hmem)

/-- **The surgery data of a `C¹` spacelike complete Cauchy surface** (step (1) of
`E0RegComplete.regM_isCauchyComplete_of_complete`). -/
theorem exists_lfSurgeryData (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1CompleteCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Nonempty (LFSurgeryData M S) :=
  exists_lfSurgeryData_of_rimC1 hGH hS.cauchy (rimC1_of_isE0C1CompleteCauchy hS) hmax

end E0SpearFamily

end GX
