import BenzecriScaffold.Cone.Base
import Mathlib.Topology.PartitionOfUnity

/-!
# `BenzecriScaffold.Cone.Section` — a section of `V → B`, `V ≅ B × ℝ₊*` (§ 2, p. 241; Déf. 3)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 240–241; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF p. 13–14).
Package WP-45o (wave 3, layer L5; fix round after AUDIT-1 and DEC-122).

* **`bzdef:c1s2d3_homotheties_positives`** — `benzecri1960_ch1.tex:526` (Déf. 3, l.526–538,
  p. 240), **closed in its corrected form (DEC-122), the finding recorded**; marked here, where it
  is completed. Its last sentence « cet espace fibré est topologiquement trivial » is
  `ConeBase.exists_trivialization_of_properSMul`: for `V` a « variété » (Hausdorff, second
  countable) on which `ℝ₊*` acts properly, there is an `ℝ₊*`-equivariant homeomorphism
  `V ≃ₜ B × ℝ₊*` over `B` (`ConeBase.trivialization`, from a homogeneous norm). The rest of Déf. 3
  is proved in `Cone/Basic` (the action `posSMul`, its independence of the chart for `V` Hausdorff,
  the action law, continuity, freeness, affine but not conical automorphisms) and `Cone/Base` (the
  principal bundle, `ConeBase.coneTrivialization`). **The finding**: without properness the
  triviality is false — the counterexample `V` of `Cone/Counterexample` is homeomorphic to `B × ℝ₊*`
  by no homeomorphism (`Benzecri.ConeCex.not_def3TrivialAsPrinted`).
* Unlabelled prose — `benzecri1960_ch1.tex:549` (l.549–552, p. 241), « si $V$ est supposé
  para-compact, on peut donc construire une section de $V$ au-dessus de $B$ »: **closed in its
  corrected form (DEC-122), the finding recorded** — `ConeBase.exists_section_of_properSMul` (`V`
  second countable, `ℝ₊*` acting properly). The printed inference is false: the counterexample `V`
  is paracompact and has no section (`Benzecri.ConeCex.not_p241SectionAsPrinted`). For `V`
  second countable the three conditions « a continuous section exists », « `B` is Hausdorff », « the
  action is proper » are equivalent (`ConeBase.exists_section_iff_properSMul`,
  `ConeBase.t2Space_iff_properSMul`). The construction is the plan's: a continuous homogeneous
  « norm » `N : V → ℝ₊*`, `N(λm) = λN(m)` (`ConeBase.exists_homogeneous_norm`), glued from the local
  norms `‖f(m)‖` of the cone charts by a partition of unity of `B` subordinate to the base charts;
  the section is `σ(p(m)) = N(m)⁻¹ m` (`ConeBase.sectionOfNorm`), the locus `N = 1`. The forms with
  `B` as hypothesis are kept: `ConeBase.exists_section` (`B` Hausdorff and paracompact),
  `ConeBase.exists_section_of_secondCountable`, `ConeBase.exists_trivialization`.

> Tout fibré localement trivial, dont la fibre est contractile, et dont la base est un espace
> normal, à base dénombrable d'ouverts, possède une section; si $V$ est supposé para-compact, on
> peut donc construire une section de $V$ au-desus de $B$.
>
> (Déf. 3) $V$ est ainsi munie d'une structure d'espace fibré $\R^+$-principal : cet espace fibré
> est topologiquement trivial, puisque $\R^+$ est homéomorphe au segment ouvert, et nous en
> construirons plus loin une section.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « fibré localement trivial, dont la fibre est contractile » | ✓ proved, not assumed: `Cone/Base`'s `coneTrivialization` (fibre `ℝ₊*`); the general theorem on bundles with contractible fibre is NOT formalized — bypassed by the direct homogeneous-norm construction |
| « la base est un espace normal » | ✓ derived in the corrected forms: `B` is Hausdorff (properness, `t2Space_of_properSMul`), locally compact and second countable, hence paracompact and normal; in the forms with `B` as hypothesis, `[T2Space B] [ParacompactSpace B]` |
| « à base dénombrable d'ouverts » | ✓ carried as `[SecondCountableTopology V]` (« variété », plan F6); then `B` is second countable |
| « si $V$ est supposé para-compact » | ✗ **finding (DEC-122)**: not sufficient (`ConeCex.not_p241SectionAsPrinted`); replaced by `V` second countable |
| (not printed) the action of `ℝ₊*` is proper | ⚠ **added, ruled (DEC-122)**: the correction; equivalent to `B` Hausdorff, and necessary (`exists_section_iff_properSMul`) |
| `V` a « variété » (Hausdorff) | ✓ carried: `[T2Space V]` (Déf. 3's action; DEC-122 keeps this reading) |

## SCOPE (disclosed)

* « au-desus » is the transcription's `[sic]` (« au-dessus »).
* The cited theorem (« Tout fibré localement trivial, dont la fibre est contractile … possède une
  section ») is not formalized in general: for the fibre `ℝ₊*` the partition-of-unity construction
  of a homogeneous norm gives the section directly, which is how the plan proposed it.
* The paper's hypothesis « $V$ para-compact » is replaced by `V` second countable (part of
  « variété », plan F6). A form with `[ParacompactSpace V] [ConnectedSpace V]` (the audit's optional
  nit: a connected, locally compact, paracompact Hausdorff space is σ-compact) is NOT formalized:
  Mathlib has no « connected + paracompact + locally compact ⇒ σ-compact » at this pin.
* « puisque $\R^+$ est homéomorphe au segment ouvert » (contractibility) is not used: the section is
  explicit.
* `ConeBase.secondCountableTopology` moved to `Cone/Base` (same name).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function

namespace Benzecri

universe u

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (n + 1)) V]
  [HasConeCharts (n + 1) V] [T2Space V]

namespace ConeBase

/-! ### Local norms -/

/-- The local « norm » along a cone chart `f`: `m ↦ ‖f(m)‖` (sup norm of `ℝⁿ⁺¹`). -/
def localNorm (e : OpenPartialHomeomorph V (RnO (n + 1))) (m : V) : ℝ := ‖(e m).val‖

omit [ChartedSpace (RnO (n + 1)) V] [HasConeCharts (n + 1) V] [T2Space V] in
theorem localNorm_pos (e : OpenPartialHomeomorph V (RnO (n + 1))) (m : V) : 0 < localNorm e m :=
  norm_pos_iff.2 (e m).val_ne_zero

/-- A local norm is homogeneous of degree 1: `‖f(λm)‖ = λ‖f(m)‖`. -/
theorem localNorm_posSMul {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) (c : RPos) :
    localNorm e (posSMul (n + 1) c m) = ((c : ℝˣ) : ℝ) * localNorm e m := by
  simp only [localNorm, he.map_smul hm, Punctured.val_smul_pos, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Punctured.pos c)]

omit [ChartedSpace (RnO (n + 1)) V] [HasConeCharts (n + 1) V] [T2Space V] in
theorem continuousAt_localNorm {e : OpenPartialHomeomorph V (RnO (n + 1))} {m : V}
    (hm : m ∈ e.source) : ContinuousAt (localNorm e) m :=
  (continuous_norm.comp Punctured.continuous_val).continuousAt.comp (e.continuousAt hm)

/-! ### A homogeneous norm, by a partition of unity on the base -/

/-- The open cover of `B` by the domains of the base charts of the chosen cone charts. -/
def chartCover (x : V) : Set (ConeBase n V) :=
  (baseChart (isConeChart_coneChartAt (n := n + 1) x)).source

theorem isOpen_chartCover (x : V) : IsOpen (chartCover (n := n) x) :=
  (baseChart _).open_source

theorem iUnion_chartCover : (univ : Set (ConeBase n V)) ⊆ ⋃ x, chartCover x := fun b _ =>
  mem_iUnion.2 ⟨Quotient.out b, Quotient.out b, mem_coneChartAt_source _, Quotient.out_eq b⟩

/-- **A homogeneous « norm » on `V`** (p. 241): if the base `B` is Hausdorff and paracompact, there
is a continuous `N : V → ℝ₊*` with `N(λm) = λN(m)`. It is glued from the local norms `‖f(m)‖` of
the cone charts by a partition of unity `{φ_x}` of `B` subordinate to the base charts:
`N(m) = Σ φ_x(p(m)) ‖f_x(m)‖`. -/
theorem exists_homogeneous_norm [T2Space (ConeBase n V)] [ParacompactSpace (ConeBase n V)] :
    ∃ N : V → RPos, Continuous N ∧ ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m := by
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (chartCover (n := n) (V := V))
    isOpen_chartCover iUnion_chartCover
  set e : V → OpenPartialHomeomorph V (RnO (n + 1)) := fun x => coneChartAt (n + 1) x
  have he : ∀ x, IsConeChart (n + 1) (e x) := fun x => isConeChart_coneChartAt x
  -- the terms `φ_x(p(m)) ‖f_x(m)‖`
  set t : V → V → ℝ := fun x m => f x (mk m) * localNorm (e x) m with ht_def
  have hsupp : ∀ x m, mk m ∈ tsupport (f x) → m ∈ (e x).source := fun x m h =>
    (mk_mem_baseChart_source_iff (he x)).1 (hf x h)
  have hzero : ∀ x m, m ∉ (e x).source → f x (mk m) = 0 := fun x m h =>
    image_eq_zero_of_notMem_tsupport fun h' => h (hsupp x m h')
  have hcont : ∀ x, Continuous (t x) := by
    intro x
    refine continuous_iff_continuousAt.2 fun m => ?_
    by_cases hm : mk m ∈ tsupport (f x)
    · exact ((f x).continuous.comp continuous_mk).continuousAt.mul
        (continuousAt_localNorm (hsupp x m hm))
    · have hev : (fun m => f x (mk m)) =ᶠ[𝓝 m] fun _ => 0 :=
        continuous_mk.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hm)
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hev] with y hy
      simp only [ht_def, hy, zero_mul]
  have hlf : LocallyFinite fun x => support (t x) :=
    (f.locallyFinite.preimage_continuous continuous_mk).subset fun x m hm => by
      simp only [ht_def, mem_support] at hm
      exact left_ne_zero_of_mul hm
  have hfin : ∀ m, HasFiniteSupport fun x => t x m := fun m =>
    (f.locallyFinite.point_finite (mk m)).subset fun x hx => by
      simp only [ht_def, mem_support] at hx
      exact left_ne_zero_of_mul hx
  have hpos : ∀ m, 0 < ∑ᶠ x, t x m := by
    intro m
    obtain ⟨x, hx⟩ := f.exists_pos (mem_univ (mk m))
    refine finsum_pos (fun y => mul_nonneg (f.nonneg y _) (localNorm_pos _ _).le) ⟨x, ?_⟩ (hfin m)
    exact mul_pos hx (localNorm_pos _ _)
  have hhom : ∀ (c : RPos) m x, t x (posSMul (n + 1) c m) = ((c : ℝˣ) : ℝ) * t x m := by
    intro c m x
    by_cases hm : m ∈ (e x).source
    · simp only [ht_def, mk_posSMul, localNorm_posSMul (he x) hm]
      ring
    · simp only [ht_def, mk_posSMul, hzero x m hm, zero_mul, mul_zero]
  refine ⟨fun m => Punctured.posUnit _ (hpos m), continuous_RPos_iff.2 ?_, fun c m => ?_⟩
  · exact continuous_finsum hcont hlf
  · refine Subtype.ext (Units.ext ?_)
    simp only [Punctured.coe_posUnit, Subgroup.coe_mul, Units.val_mul, hhom c m]
    exact (mul_finsum _ _).symm

/-! ### The section -/

variable {N : V → RPos}

/-- **The section `σ : B → V` defined by a homogeneous norm**: `σ(p(m)) = N(m)⁻¹ m`, the unique
point of the fibre where `N = 1`. -/
def sectionOfNorm (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) :
    ConeBase n V → V :=
  Quotient.lift (fun m => posSMul (n + 1) (N m)⁻¹ m) fun a b hab => by
    obtain ⟨c, rfl⟩ := rel_iff.1 hab
    show posSMul (n + 1) (N (posSMul (n + 1) c b))⁻¹ (posSMul (n + 1) c b) =
      posSMul (n + 1) (N b)⁻¹ b
    rw [hN, ← posSMul_mul, mul_inv_rev, inv_mul_cancel_right]

theorem sectionOfNorm_mk (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) (m : V) :
    sectionOfNorm hN (mk m) = posSMul (n + 1) (N m)⁻¹ m := rfl

theorem mk_sectionOfNorm (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m)
    (b : ConeBase n V) : mk (sectionOfNorm hN b) = b := by
  obtain ⟨m, rfl⟩ := mk_surjective b
  rw [sectionOfNorm_mk, mk_posSMul]

theorem norm_sectionOfNorm (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m)
    (b : ConeBase n V) : N (sectionOfNorm hN b) = 1 := by
  obtain ⟨m, rfl⟩ := mk_surjective b
  rw [sectionOfNorm_mk, hN, inv_mul_cancel]

theorem continuous_sectionOfNorm (hNc : Continuous N)
    (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) :
    Continuous (sectionOfNorm hN) := by
  refine isOpenQuotientMap_mk.isQuotientMap.continuous_iff.2 ?_
  show Continuous fun m => posSMul (n + 1) (N m)⁻¹ m
  exact (continuous_posSMul (n := n + 1)).comp ((hNc.inv).prodMk continuous_id)

/-- **« on peut donc construire une section de $V$ au-dessus de $B$ »** (p. 241), for `B` Hausdorff
and paracompact: a continuous `σ : B → V` with `p ∘ σ = id`. -/
theorem exists_section [T2Space (ConeBase n V)] [ParacompactSpace (ConeBase n V)] :
    ∃ σ : ConeBase n V → V, Continuous σ ∧ ∀ b, mk (σ b) = b := by
  obtain ⟨N, hNc, hN⟩ := exists_homogeneous_norm (n := n) (V := V)
  exact ⟨sectionOfNorm hN, continuous_sectionOfNorm hNc hN, mk_sectionOfNorm hN⟩

/-- **The hypothesis `B` Hausdorff is necessary**: if `V → B` has a continuous section, `B` is
Hausdorff (it is homeomorphic to the image of the section in the Hausdorff `V`). -/
theorem t2Space_of_section {σ : ConeBase n V → V} (hσ : Continuous σ) (hmk : ∀ b, mk (σ b) = b) :
    T2Space (ConeBase n V) :=
  (IsEmbedding.of_leftInverse (f := mk) (g := σ) hmk continuous_mk hσ).t2Space

/-! ### `V` is the trivial principal bundle `B × ℝ₊*` -/

/-- **« cet espace fibré est topologiquement trivial »** (Déf. 3): a homogeneous norm gives an
`ℝ₊*`-equivariant homeomorphism `V ≃ₜ B × ℝ₊*`, `m ↦ (p(m), N(m))`, inverse
`(b, λ) ↦ λσ(b)`. -/
def trivialization (hNc : Continuous N)
    (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) : V ≃ₜ ConeBase n V × RPos where
  toFun m := (mk m, N m)
  invFun p := posSMul (n + 1) p.2 (sectionOfNorm hN p.1)
  left_inv m := by
    show posSMul (n + 1) (N m) (sectionOfNorm hN (mk m)) = m
    rw [sectionOfNorm_mk, ← posSMul_mul, mul_inv_cancel, posSMul_one]
  right_inv p := by
    obtain ⟨b, c⟩ := p
    refine Prod.ext ?_ ?_
    · show mk (posSMul (n + 1) c (sectionOfNorm hN b)) = b
      rw [mk_posSMul, mk_sectionOfNorm]
    · show N (posSMul (n + 1) c (sectionOfNorm hN b)) = c
      rw [hN, norm_sectionOfNorm (N := N) hN, mul_one]
  continuous_toFun := continuous_mk.prodMk hNc
  continuous_invFun := (continuous_posSMul (n := n + 1)).comp
    (continuous_snd.prodMk ((continuous_sectionOfNorm hNc hN).comp continuous_fst))

theorem trivialization_apply (hNc : Continuous N)
    (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) (m : V) :
    trivialization hNc hN m = (mk m, N m) := rfl

/-- The trivialisation is `ℝ₊*`-equivariant. -/
theorem trivialization_posSMul (hNc : Continuous N)
    (hN : ∀ (c : RPos) (m : V), N (posSMul (n + 1) c m) = c * N m) (c : RPos) (m : V) :
    trivialization hNc hN (posSMul (n + 1) c m) =
      ((trivialization hNc hN m).1, c * (trivialization hNc hN m).2) := by
  simp only [trivialization_apply, mk_posSMul, hN]

/-- **The principal bundle `V → B` is trivial** when `B` is Hausdorff and paracompact. -/
theorem exists_trivialization [T2Space (ConeBase n V)] [ParacompactSpace (ConeBase n V)] :
    ∃ T : V ≃ₜ ConeBase n V × RPos, (∀ m, (T m).1 = mk m) ∧
      ∀ (c : RPos) (m : V), T (posSMul (n + 1) c m) = ((T m).1, c * (T m).2) := by
  obtain ⟨N, hNc, hN⟩ := exists_homogeneous_norm (n := n) (V := V)
  exact ⟨trivialization hNc hN, fun _ => rfl, trivialization_posSMul hNc hN⟩

/-! ### Countability: the paper's « à base dénombrable d'ouverts » -/

/-- The base is locally compact (it is charted on the compact `S(n)`). -/
theorem locallyCompactSpace : LocallyCompactSpace (ConeBase n V) :=
  ChartedSpace.locallyCompactSpace (S n) _

/-- **For `V` second countable and `B` Hausdorff, `B` is paracompact**, so the section exists. -/
theorem paracompactSpace [SecondCountableTopology V] [T2Space (ConeBase n V)] :
    ParacompactSpace (ConeBase n V) := by
  haveI := secondCountableTopology (n := n) (V := V)
  haveI := locallyCompactSpace (n := n) (V := V)
  infer_instance

/-- **The section, under the paper's countability hypothesis** (p. 241, « à base dénombrable
d'ouverts »): for `V` second countable and `B` Hausdorff, `V → B` has a continuous section. -/
theorem exists_section_of_secondCountable [SecondCountableTopology V] [T2Space (ConeBase n V)] :
    ∃ σ : ConeBase n V → V, Continuous σ ∧ ∀ b, mk (σ b) = b := by
  haveI := paracompactSpace (n := n) (V := V)
  exact exists_section

/-! ### The corrected forms (DEC-122): a proper action of `ℝ₊*` -/

/-- **p. 241, corrected form (DEC-122)**: for `V` second countable (« variété ») on which `ℝ₊*`
acts properly, `V → B` has a continuous section. The printed inference (« si $V$ est supposé
para-compact, on peut donc construire une section ») is false without properness
(`Benzecri.ConeCex.not_p241SectionAsPrinted`); properness is equivalent to `B` Hausdorff
(`t2Space_iff_properSMul`), which a section forces (`t2Space_of_section`). -/
theorem exists_section_of_properSMul [SecondCountableTopology V]
    (h : @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V)) :
    ∃ σ : ConeBase n V → V, Continuous σ ∧ ∀ b, mk (σ b) = b := by
  haveI := t2Space_of_properSMul h
  exact exists_section_of_secondCountable

/-- **Déf. 3, « cet espace fibré est topologiquement trivial », corrected form (DEC-122)**: for `V`
second countable on which `ℝ₊*` acts properly, there is an `ℝ₊*`-equivariant homeomorphism
`V ≃ₜ B × ℝ₊*` over `B`. False without properness (`Benzecri.ConeCex.not_def3TrivialAsPrinted`). -/
theorem exists_trivialization_of_properSMul [SecondCountableTopology V]
    (h : @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V)) :
    ∃ T : V ≃ₜ ConeBase n V × RPos, (∀ m, (T m).1 = mk m) ∧
      ∀ (c : RPos) (m : V), T (posSMul (n + 1) c m) = ((T m).1, c * (T m).2) := by
  haveI := t2Space_of_properSMul h
  haveI := paracompactSpace (n := n) (V := V)
  exact exists_trivialization

/-- **The three conditions are equivalent** (for `V` second countable): `V → B` has a continuous
section iff `B` is Hausdorff iff the action of `ℝ₊*` is proper. -/
theorem exists_section_iff_properSMul [SecondCountableTopology V] :
    (∃ σ : ConeBase n V → V, Continuous σ ∧ ∀ b, mk (σ b) = b) ↔
      @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V) := by
  refine ⟨fun ⟨σ, hσ, hmk⟩ => ?_, exists_section_of_properSMul⟩
  haveI := t2Space_of_section hσ hmk
  exact properSMul_of_t2Space

/-- If `V` is homeomorphic to `B × ℝ₊*` (by any homeomorphism), `B` is Hausdorff: `B × ℝ₊*` is, and
`b ↦ (b, 1)` embeds `B` in it. -/
theorem t2Space_of_homeomorph (T : V ≃ₜ ConeBase n V × RPos) : T2Space (ConeBase n V) :=
  haveI : T2Space (ConeBase n V × RPos) := T.symm.isEmbedding.t2Space
  (isEmbedding_prodMkLeft (1 : RPos)).t2Space

end ConeBase


end Benzecri
