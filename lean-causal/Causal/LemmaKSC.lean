import Causal.LemmaKReduction
import Causal.LevinTimeFunction

/-!
# Lemma K with second countability — what it buys, and the exact local residue of the bare form

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts twice and never
proves (Rem 2.3 `clomax`, `GHFspace.tex:572`, the sentence at l.576–578; §11, l.3537–3540); it
carries no paper label. Its bare form is `isCauchySurface_of_isLocallyCauchy`
(`CausalScaffold.CompactCauchy`), a tagged `sorry`; DEC-92 asks it to be settled. This file adds
**second countability**, which is part of ETT's own definition of a spacetime and so is not a
weakening of the paper:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:255`)

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Barbot, Rem 2.3, l.576–578)

**Verdict: not settled.** The second-countable form
`isCauchySurface_of_isLocallyCauchy_of_secondCountable` is stated, with a tagged `sorry`, in the
scaffold module `CausalScaffold.LemmaKSCOpen`. This file proves what second countability does
give, and states the residue exactly, in local form.

## What is proved

* **Every tarentin globally hyperbolic Hausdorff spacetime is locally compact**
  (`locallyCompactSpace_of_globallyHyperbolic`: a point lies in the interior of a compact
  diamond). With second countability it is σ-compact and metrizable
  (`sigmaCompactSpace_of_globallyHyperbolic`, `metrizableSpace_of_globallyHyperbolic`). No
  second countability is needed for local compactness; it discharges the `LocallyCompactSpace`
  hypotheses of `Causal.Flat.CBGCompact` for every GH spacetime of the library. Local and
  σ-compactness are proved in the ETT-layer `Causal.LevinTimeFunction` since T-abs-hoist-levin
  (same full names), metrizability here.
* **Second countability kills the long ray** (`countable_of_wellOrdered_chain`): in a second
  countable space with closed `J^+(x)` and causal `≤`, a well-ordered strictly increasing causal
  chain is countable (the sets `J^+(e_i)` strictly decrease; a basic open set around `e_i`
  missing `J^+(e_{i⁺})` determines `i`). This is round 1's argument
  (`Causal.LemmaKReduction`, SCOPE), formalized: the mechanism of the conjectured counterexample
  to `CurvesExtend` (`Causal.CurvesExtend`, SCOPE) cannot occur in an ETT spacetime.
* **The core of `Causal.LemmaKBare` is sharp** (`isCauchySurface_iff_isOpen_strictJplus`): where
  curves extend, a compact connected locally Cauchy `Σ` is a Cauchy surface **iff** its strict
  causal future and strict causal past are open. The new half is
  `isOpen_strictJplus_of_isCauchySurface`: for a compact Cauchy surface the strict future is
  `M ∖ J^-(Σ)`.
* **Acausality is a local property of `Σ`** (`isAcausal_iff_of_isLocallyCauchy`): where curves
  extend, a compact connected locally Cauchy `Σ` is acausal **iff** the set of its points having
  another point of `Σ` in their causal past is open in `Σ`. The proof is `LemmaKBare`'s Zorn and
  connectedness argument, under the relative openness only
  (`isAcausal_of_isLocallyCauchy_of_relOpen`).
* **The residue in local form** (`isCauchySurface_iff_local`): where curves extend, a compact
  connected locally Cauchy `Σ` is a Cauchy surface iff
  (1') every `w ∈ Σ` with some `z ∈ Σ`, `z ≤ w`, `z ≠ w`, has a neighbourhood in which every point
  of `Σ` has the same property; and
  (2') `J^+(Σ) ∪ J^-(Σ)` is a neighbourhood of each of its points **off** `Σ` (at the points of
  `Σ` it is one by the charts).

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `T2Space` | ✓ carried |
| `Tarentin`, `CausallyArcConnected`, `J^±(p) ≠ {p}`, `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected, `IsLocallyCauchy` | ✓ carried |
| second countability (`ETT.tex:255`) | ✓ carried where used (`SecondCountableTopology M`): faithful to ETT, not a weakening |
| — | ⚠ strengthened, named (kb/0012), in the characterisations: `C.CurvesExtend` |
| — | the characterisations are equivalences: (1')+(2'), or the openness of `strictJplus`, are not implied by the paper's hypotheses — that implication IS the open question |

## SCOPE (disclosed)

* **Verdict on DEC-92 with second countability: not settled.** No proof and no counterexample.
* **Route (a) cannot close Lemma K, even if completed.** Second countability is used nowhere in
  the residue: it bears only on `CurvesExtend` (a time function from GH + SC, Levin's theorem
  for closed orders on second countable locally compact spaces, would give `CurvesExtend` by
  `curvesExtend_of_timeFunction`), and *under* `CurvesExtend` Lemma K is still equivalent to
  (1')+(2') (`isCauchySurface_iff_local`), equivalently to the openness of the strict causal
  future and past (`isCauchySurface_iff_isOpen_strictJplus`). Geroch's route is not available:
  admissible measures are a hypothesis of `geroch_i_imp_ii`, constructed in ETT for strongly
  causal Lorentzian and `𝔼_{≥0}`-manifolds (`prop:mesure_dieckmann_Lorentz`,
  `prop:mesure_admissible`, `ETT.tex:1054`, `1726`) and, using second countability, glued from
  local ones (`prop:mesure_dieckmann_topo`, `ETT.tex:1094`) — never produced from the bare
  hypotheses of Lemma K.
  *Superseded in round 3:* Levin's theorem is now proved (`Causal.LevinTimeFunction`, in
  `Causal.LevinUtility` until T-abs-hoist-levin; `curvesExtend_of_secondCountable`: a continuous
  time function, hence `CurvesExtend`, in every second countable tarentin globally hyperbolic
  Hausdorff spacetime), and the characterisations below hold with `hext` discharged
  (`isCauchySurface_iff_local_of_secondCountable`,
  `isCauchySurface_iff_isOpen_strictJplus_of_secondCountable`, in `Causal.LevinUtility`; sharp
  form in `Causal.LemmaKSCLocal`). As predicted, that does not close Lemma K.
* **Why (1') and (2') are hard, in one sentence each.** (1') is lower semicontinuity of
  "`J^-(w) ∩ Σ ≠ {w}`" along `Σ`; it holds where a point just below `w` is in the *chronological*
  past of `w` (push-up and `Z^-`), and fails to follow from `≤` alone where `J^-(w)` has empty
  interior near `w` (a BTZ line: `Z^-` fails there, `SingularFlatAxioms.mem_Zminus_iff`).
  (2') is the same phenomenon at a point `q ∈ J^+(Σ) ∖ Σ` on the boundary of `J^+(Σ)`, which a
  curve outside `J^+(Σ) ∪ J^-(Σ)` reaches from below without entering any chart of `Σ`. Both
  statements involve only `≤`: the chronological relation `≪` is a tool of `LemmaKBare`'s proofs
  and plays no role in the statement of Lemma K, so no choice of `≪` can help where `≤`'s strict
  futures are not open.
* The scaffold statement `CausalScaffold.LemmaKSCOpen.isCauchySurface_of_isLocallyCauchy_of_secondCountable`
  is the stub's statement with `[SecondCountableTopology M]` added and nothing else; the master
  session adds `CausalScaffold.LemmaKSCOpen` to the scaffold root (kb/0025).
* Non-vacuity: on the timelike line (second countable) every hypothesis of the
  characterisations holds with `Σ = {0}` (`timelikeLine_lemmaKSC_hypotheses`), and the local
  residue holds there (`timelikeLine_lemmaKSC_local`).
* gx contract (a)–(f): not applicable; no length, metric or Lipschitz graph is defined here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ### Metrizability

Local compactness (`locallyCompactSpace_of_globallyHyperbolic`) and σ-compactness
(`sigmaCompactSpace_of_globallyHyperbolic`) are in `Causal.LevinTimeFunction`
(T-abs-hoist-levin), same full names. -/

/-- With second countability, a tarentin globally hyperbolic Hausdorff spacetime is
metrizable. -/
theorem metrizableSpace_of_globallyHyperbolic [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) : MetrizableSpace M := by
  haveI := locallyCompactSpace_of_globallyHyperbolic hT hG
  infer_instance

/-! ### Second countability kills the long ray -/

/-- **A well-ordered strictly increasing causal chain is countable** in a second countable space
with closed `J^+(x)` and causal `≤`: a basic open set around `e_i` missing the closed
`J^+(e_{i⁺})` (`i⁺` the successor of `i`) determines `i`. -/
theorem countable_of_wellOrdered_chain [SecondCountableTopology M] (hcaus : C.IsCausal)
    (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x})) {ι : Type v} [LinearOrder ι] [WellFoundedLT ι]
    (e : ι → M) (he : ∀ i j, i < j → C.le ⊤ (e i) (e j) ∧ e i ≠ e j) : Countable ι := by
  set A : Set ι := {i | ∃ j, i < j} with hA
  -- the successor of a non-maximal index
  have hsucc : ∀ i : A, ∃ s, i.1 < s ∧ ∀ j, i.1 < j → s ≤ j := fun i => by
    obtain ⟨s, hs, hmin⟩ := (wellFounded_lt (α := ι)).has_min {j | i.1 < j} i.2
    exact ⟨s, hs, fun j hj => not_lt.1 (hmin j hj)⟩
  choose s hs hsmin using hsucc
  have hnot : ∀ i : A, e i.1 ∉ C.Jplus ⊤ {e (s i)} := fun i ⟨_, hy, hle⟩ => by
    rw [mem_singleton_iff] at hy
    subst hy
    exact (he _ _ (hs i)).2 (hcaus (he _ _ (hs i)).1 hle)
  have hb : ∀ i : A, ∃ b ∈ countableBasis M, e i.1 ∈ b ∧ b ⊆ (C.Jplus ⊤ {e (s i)})ᶜ :=
    fun i => (isBasis_countableBasis M).exists_subset_of_mem_open (hnot i) (hJ _).isOpen_compl
  choose b hbB hbe hbsub using hb
  have hinj : Injective fun i : A => (⟨b i, hbB i⟩ : countableBasis M) := by
    have key : ∀ i k : A, i.1 < k.1 → b i ≠ b k := fun i k hik hbik => by
      have hle : C.le ⊤ (e (s i)) (e k.1) := by
        rcases (hsmin i k.1 hik).lt_or_eq with h | h
        · exact (he _ _ h).1
        · rw [h]; exact C.le_refl trivial
      exact hbsub i (hbik ▸ hbe k) ⟨_, mem_singleton _, hle⟩
    intro i k hik
    simp only [Subtype.mk.injEq] at hik
    rcases lt_trichotomy i.1 k.1 with h | h | h
    · exact absurd hik (key i k h)
    · exact Subtype.ext h
    · exact absurd hik.symm (key k i h)
  haveI : Countable (countableBasis M) := (countable_countableBasis M).to_subtype
  have hAc : A.Countable := countable_coe_iff.1 hinj.countable
  have hB : {i : ι | ∀ j, ¬ i < j}.Subsingleton := fun i hi k hk => by
    rcases lt_trichotomy i k with h | h | h
    · exact absurd h (hi k)
    · exact h
    · exact absurd h (hk i)
  have huniv : (univ : Set ι) ⊆ A ∪ {i : ι | ∀ j, ¬ i < j} := fun i _ => by
    by_cases h : ∃ j, i < j
    · exact Or.inl h
    · exact Or.inr fun j hj => h ⟨j, hj⟩
  exact countable_univ_iff.1 ((hAc.union hB.countable).mono huniv)

/-- The countability of well-ordered causal chains on a second countable tarentin globally
hyperbolic Hausdorff spacetime. -/
theorem GloballyHyperbolic.countable_of_wellOrdered_chain [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) {ι : Type v} [LinearOrder ι] [WellFoundedLT ι]
    (e : ι → M) (he : ∀ i j, i < j → C.le ⊤ (e i) (e j) ∧ e i ≠ e j) : Countable ι :=
  Causality.countable_of_wellOrdered_chain hG.1 (hG.isClosed_Jplus_singleton hT) e he

/-! ### The core of `LemmaKBare` is sharp -/

/-- **For a compact Cauchy surface the strict causal future and past are open**: where curves
extend, they are `M ∖ J^-(Σ)` and `M ∖ J^+(Σ)`. -/
theorem isOpen_strictJplus_of_isCauchySurface [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : C.IsCauchySurface S) :
    IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) := by
  have hcaus := hG.1
  have hle := hG.isClosed_le hT
  obtain ⟨hac, hcov⟩ := (isCauchySurface_iff_of_curvesExtend hT hG hC hJm hJp hext hSc hSne).1 hS
  constructor
  · have heq : C.strictJplus S = (C.Jminus ⊤ S)ᶜ := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx, hne⟩ ⟨w, hw, hxw⟩
        have h := hac z hz w hw (C.le_trans hzx hxw)
        subst h
        exact hne (hcaus hzx hxw).symm
      · intro hx
        rcases hcov x with ⟨z, hz, hzx⟩ | h
        · refine ⟨z, hz, hzx, fun h => hx ?_⟩
          rw [h]; exact ⟨z, hz, C.le_refl trivial⟩
        · exact absurd h hx
    rw [heq]
    exact (isClosed_Jminus_of_isCompact hle hSc).isOpen_compl
  · have heq : C.dual.strictJplus S = (C.Jplus ⊤ S)ᶜ := by
      ext x
      constructor
      · rintro ⟨z, hz, hxz, hne⟩ ⟨w, hw, hwx⟩
        have h := hac w hw z hz (C.le_trans hwx hxz)
        subst h
        exact hne (hcaus hxz hwx)
      · intro hx
        rcases hcov x with h | ⟨z, hz, hxz⟩
        · exact absurd h hx
        · refine ⟨z, hz, hxz, fun h => hx ?_⟩
          rw [h]; exact ⟨z, hz, C.le_refl trivial⟩
    rw [heq]
    exact (isClosed_Jplus_of_isCompact hle hSc).isOpen_compl

/-- **The core of `LemmaKBare` is sharp.** Where curves extend, a compact connected locally Cauchy
set is a Cauchy surface if and only if its strict causal future and its strict causal past are
open. -/
theorem isCauchySurface_iff_isOpen_strictJplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔ IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) :=
  ⟨isOpen_strictJplus_of_isCauchySurface hT hG hC hJm hJp hext hSc hSconn.nonempty,
    fun h => isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp hext hSc
      hSconn hloc h.1 h.2⟩

/-! ### Acausality is a local property of `Σ` -/

/-- **Acausality from relative openness.** `LemmaKBare`'s step 1 (`isAcausal_of_isLocallyCauchy`)
with the openness of the strict causal future weakened to: the points of `Σ` lying in the strict
causal future of `Σ` form an open subset of `Σ`. -/
theorem isAcausal_of_isLocallyCauchy_of_relOpen [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S)
    (hQ : ∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) :
    C.IsAcausal S := by
  have hcaus := hG.1
  -- an open set of `M` cutting `S ∩ strictJplus S` out of `S`
  choose! N hN hNsub using hQ
  set O : Set M := ⋃ w ∈ S ∩ C.strictJplus S, interior (N w) with hOdef
  have hOo : IsOpen O := isOpen_biUnion fun _ _ => isOpen_interior
  have hOS : ∀ s ∈ S, s ∈ O ↔ s ∈ C.strictJplus S := fun s hs => by
    constructor
    · intro h
      obtain ⟨w, hw, hsw⟩ := mem_iUnion₂.1 h
      exact hNsub w hw ⟨hs, interior_subset hsw⟩
    · intro h
      exact mem_iUnion₂.2 ⟨s, ⟨hs, h⟩, mem_interior_iff_mem_nhds.2 (hN s ⟨hs, h⟩)⟩
  -- an open neighbourhood of the diagonal of `S` on which `S` is acausal
  set W : Set (M × M) := ⋃ (U : Opens M) (_ : C.CausallyConvexIn (U : Set M) ⊤ ∧
    C.IsCauchySurfaceOn U (S ∩ U)), (U : Set M) ×ˢ (U : Set M) with hWdef
  have hWo : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen.prod U.isOpen
  have hWdiag : ∀ z ∈ S, (z, z) ∈ W := fun z hz => by
    obtain ⟨U, hzU, hU, hSU⟩ := hloc z hz
    exact mem_iUnion₂.2 ⟨U, ⟨hU, hSU⟩, hzU, hzU⟩
  have hWac : ∀ z ∈ S, ∀ w ∈ S, C.le ⊤ z w → (z, w) ∈ W → z = w := by
    intro z hz w hw hzw hW
    obtain ⟨U, ⟨hU, hSU⟩, hzU, hwU⟩ := mem_iUnion₂.1 hW
    exact eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU ⟨hz, hzU⟩ ⟨hw, hwU⟩ hzw
  -- the strictly related pairs of `S`, a compact set
  set P : Set (M × M) := ((S ×ˢ S) ∩ {q | C.le ⊤ q.1 q.2}) \ W with hPdef
  have hPc : IsCompact P :=
    (hSc.prod hSc).of_isClosed_subset
      (((hSc.isClosed.prod hSc.isClosed).inter (hG.isClosed_le hT)).sdiff hWo)
      fun q hq => hq.1.1
  have hK : IsClosed (Prod.snd '' P) := (hPc.image continuous_snd).isClosed
  have hKQ : Prod.snd '' P ⊆ C.strictJplus S := by
    rintro _ ⟨⟨z, w⟩, ⟨⟨⟨hz, -⟩, hzw⟩, hW⟩, rfl⟩
    refine ⟨z, hz, hzw, fun h => hW ?_⟩
    simp only at h
    rw [h]; exact hWdiag z hz
  have hQK : S ∩ C.strictJplus S ⊆ Prod.snd '' P := by
    rintro w ⟨hw, z, hz, hzw, hne⟩
    exact ⟨(z, w), ⟨⟨⟨hz, hw⟩, hzw⟩, fun hW => hne (hWac z hz w hw hzw hW).symm⟩, rfl⟩
  -- a `≤`-minimal point of `S` (Zorn), which is not in the strict future
  obtain ⟨s₀, hs₀⟩ := hSconn.nonempty
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded (α := S)
    (r := fun a b : S => C.le ⊤ (b : M) a) (fun c hc => by
      by_cases hne : c.Nonempty
      · haveI : Nonempty c := hne.to_subtype
        let t : c → Set M := fun i => S ∩ C.Jminus ⊤ {((i : S) : M)}
        have hmem : ∀ i : c, ((i : S) : M) ∈ t i := fun i =>
          ⟨(i : S).2, ⟨_, mem_singleton _, C.le_refl trivial⟩⟩
        obtain ⟨m', hm'⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
          (fun i j => by
            by_cases hij : (i : S) = (j : S)
            · refine ⟨i, le_rfl, ?_⟩
              show t i ⊆ t j
              simp only [t, hij, subset_refl]
            · rcases hc i.2 j.2 hij with h | h
              · refine ⟨j, fun x hx => ⟨hx.1, ?_⟩, le_rfl⟩
                obtain ⟨_, rfl, hxj⟩ := hx.2
                exact ⟨_, mem_singleton _, C.le_trans hxj h⟩
              · refine ⟨i, le_rfl, fun x hx => ⟨hx.1, ?_⟩⟩
                obtain ⟨_, rfl, hxi⟩ := hx.2
                exact ⟨_, mem_singleton _, C.le_trans hxi h⟩)
          (fun i => ⟨_, hmem i⟩) (fun i => hSc.inter_right (hG.isClosed_Jminus_singleton hT _))
          (fun i => hSc.isClosed.inter (hG.isClosed_Jminus_singleton hT _))
        have hm'S : m' ∈ S := (mem_iInter.1 hm' (Classical.arbitrary c)).1
        refine ⟨⟨m', hm'S⟩, fun a ha => ?_⟩
        obtain ⟨_, rfl, h⟩ := (mem_iInter.1 hm' ⟨a, ha⟩).2
        exact h
      · refine ⟨⟨s₀, hs₀⟩, fun a ha => absurd ⟨a, ha⟩ hne⟩)
    (fun h₁ h₂ => C.le_trans h₂ h₁)
  have hmQ : (m : M) ∉ C.strictJplus S := by
    rintro ⟨z, hz, hzm, hne⟩
    exact hne (hcaus (hm ⟨z, hz⟩ hzm) hzm)
  -- connectedness
  by_contra hnac
  have hA : (S ∩ O).Nonempty := by
    simp only [IsAcausal, not_forall] at hnac
    obtain ⟨z, hz, w, hw, hzw, hne⟩ := hnac
    exact ⟨w, hw, (hOS w hw).2 ⟨z, hz, hzw, Ne.symm hne⟩⟩
  obtain ⟨s, hsS, hsO, hsK⟩ := hSconn.isPreconnected _ _ hOo hK.isOpen_compl
    (fun s hs => by
      by_cases h : s ∈ C.strictJplus S
      · exact Or.inl ((hOS s hs).2 h)
      · exact Or.inr fun h' => h (hKQ h'))
    hA ⟨m, m.2, fun h => hmQ (hKQ h)⟩
  exact hsK (hQK ⟨hsS, (hOS s hsS).1 hsO⟩)

/-- **Acausality is a local property of `Σ`.** Where curves extend, a compact connected locally
Cauchy set `Σ` is acausal iff every point of `Σ` having another point of `Σ` in its causal past
has a neighbourhood in which every point of `Σ` has one. -/
theorem isAcausal_iff_of_isLocallyCauchy [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsAcausal S ↔ ∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S := by
  refine ⟨fun hac w hw => ?_, isAcausal_of_isLocallyCauchy_of_relOpen hT hG hC hext hSc hSconn hloc⟩
  obtain ⟨hwS, z, hz, hzw, hne⟩ := hw
  exact absurd (hac z hz w hwS hzw).symm hne

/-! ### The residue in local form -/

/-- **The bare form, where curves extend, is exactly two local conditions.** A compact connected
locally Cauchy set `Σ` is a Cauchy surface iff (1') the points of `Σ` with another point of `Σ` in
their causal past form an open subset of `Σ`, and (2') `J^+(Σ) ∪ J^-(Σ)` is a neighbourhood of
each of its points off `Σ`. -/
theorem isCauchySurface_iff_local [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔
      (∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) ∧
      (∀ q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S, q ∉ S → C.Jplus ⊤ S ∪ C.Jminus ⊤ S ∈ 𝓝 q) := by
  have hcaus := hG.1
  have hiff := isCauchySurface_iff_of_curvesExtend hT hG hC hJm hJp hext hSc hSconn.nonempty
  have hac_iff := isAcausal_iff_of_isLocallyCauchy hT hG hC hext hSc hSconn hloc
  constructor
  · intro hS
    obtain ⟨hac, hcov⟩ := hiff.1 hS
    refine ⟨hac_iff.1 hac, fun q _ _ => ?_⟩
    rw [eq_univ_of_forall hcov]
    exact univ_mem
  · rintro ⟨h1, h2⟩
    have hac := hac_iff.2 h1
    refine isCauchySurface_of_isAcausal_of_isOpen hT hG hC hJm hJp hSc hSconn.nonempty hac ?_
    rw [isOpen_iff_mem_nhds]
    intro q hq
    by_cases hqS : q ∈ S
    · obtain ⟨U, hqU, hU, hSU⟩ := hloc q hqS
      refine mem_of_superset (U.isOpen.mem_nhds hqU) fun r hr => ?_
      rcases mem_Jplus_or_Jminus_of_isCauchySurfaceOn hcaus hext hSU hr with
        ⟨z, hz, hzr⟩ | ⟨z, hz, hrz⟩
      · exact Or.inl ⟨z, hz.1, C.le_mono le_top hzr⟩
      · exact Or.inr ⟨z, hz.1, C.le_mono le_top hrz⟩
    · exact h2 q hq hqS

end Causality

/-! ### Non-vacuity: the timelike line -/

/-- On the timelike line (second countable), every hypothesis of the characterisations holds with
`Σ = {0}`. -/
theorem timelikeLine_lemmaKSC_hypotheses :
    SecondCountableTopology ℝ ∧ timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.CurvesExtend ∧
      IsCompact ({0} : Set ℝ) ∧ IsConnected ({0} : Set ℝ) ∧
      timelikeLine.IsLocallyCauchy ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact ⟨inferInstance, hT, hG, hC, hJm, hJp, hext, hSc, hSconn, hloc.isLocallyCauchy⟩

/-- The local residue (1')+(2') holds on the timelike line for `Σ = {0}`, through the
characterisation. -/
theorem timelikeLine_lemmaKSC_local :
    (∀ w ∈ ({0} : Set ℝ) ∩ timelikeLine.strictJplus {0},
        ∃ N ∈ 𝓝 w, ({0} : Set ℝ) ∩ N ⊆ timelikeLine.strictJplus {0}) ∧
      (∀ q ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ {0}, q ∉ ({0} : Set ℝ) →
        timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ {0} ∈ 𝓝 q) := by
  obtain ⟨-, hT, hG, hC, hJm, hJp, hext, hSc, hSconn, hloc⟩ := timelikeLine_lemmaKSC_hypotheses
  exact (Causality.isCauchySurface_iff_local hT hG hC hJm hJp hext hSc hSconn hloc).1
    timelikeLine_isCauchySurface_zero_of_lemmaKBare

end Causal
