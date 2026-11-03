import Causal.Flat.AchronalDomains
import Causal.Flat.Penrose
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# `Causal.Flat.Externals` — the external results of Barbot §5, §9, §10, §11, as named `Prop`s

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). Package
WP-33c (DEC-36, DEC-44). **No ledger label is certified here** (no `**` mark): each external
theorem is a `Prop` (never an `axiom`) named after its source, with proved non-vacuity witnesses
and the reduction lemma its consumer runs. Labels (lines of `papers/barbot/legacy/labeled/GHFspace.tex`),
all unmarked:

* `bthm:ausl` — `GHFspace.tex:1697` (Thm 5.1): `AuslanderCarriereDalbo`; consumer
  `exists_invariant_maxUnipotent` (with `bthm:unip`).
* `bthm:unip` — `GHFspace.tex:1710` (Thm 5.2): `MaxUnipotentSubspace`.
* `bprop:sanloxo` — `GHFspace.tex:2573` (Prop 9.1): `BenoistNoLox` (its whole conclusion is the
  honest unit, SCOPE); consumer `exists_finiteIndex_fixes_of_noLox`. Not proved here, and since
  DEC-111 (2026-11-03) **proved** as `benoistNoLox d` in `Flat/GromovProof`, every `d`, by
  Gromov's classification on `ℍᵈ` (no Zariski closure, no discreteness, no finite index).
* `bprop:admlox` — `GHFspace.tex:1230` (Prop 4.17), its input: `LimitSetMinimal`; consumer
  `limitSet_invariant_and_minimal` (the half of 4.17 on `𝒮`). Finding: "nonempty" is needed.
* Selberg's lemma (DEC-44, [10.G], finding F2): `SelbergLemma`; consumer
  `exists_finiteIndex_torsionFree_linOf`. Since DEC-115 (2026-11-03) **proved** as
  `selbergLemma V` in `Flat/SelbergProof`, every finite-dimensional real `V`, by congruence
  subgroups (statement here unchanged).
* Folklore, proved: l.3295–3297 (`eigen_of_commute`, `lorentzSphere_fixed_of_commute`);
  `bprop:U_timelike` — `GHFspace.tex:3347` (Prop 10.4) uses a folklore **refuted** for `n ≥ 3`
  (`not_abelianPairAsPrinted`), true form on unipotents `fixed_null_of_commute_unipotent`.

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$. Then, the identity
> component $G_{0}$ of the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent. In
> particular, $\Gamma_{nd} = L^{-1}(G_{0} \cap L(\Gamma))$ is nilpotent. (l.1699–1703)

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (l.1712–1717)

> If $\Gamma$ does not contain loxodromic elements, it is elementary; i.e., up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), or its linear part
> stabilizes an isotropic vector. (l.2575–2577)
>
> If $\Gamma$ has no loxodromic elements, according to \cite{benoist}, the same is true for its
> Zariski closure $G$. Since $G$ has a finite number of connected components, we can assume,
> restricting $\Gamma$ to a finite index subgroup if necessary, that $\Gamma$ is contained in the
> identity component $G_{0}$. (l.2581–2584)

> For any admissible representation $\rho$, the closure of the set of repulsive fixed points in
> ${\mathcal J}$ of loxodromic elements of $\rho(\Gamma)$ is a $\rho(\Gamma)$-invariant subset
> $\Lambda(\rho)$ contained in any closed $\rho(\Gamma)$-invariant subset of ${\mathcal J}$.
> (l.1232–1238) […] there is a closed subset $\widehat{\Lambda}$, the limit set, contained in every
> $\Gamma$-invariant closed subset […] It is also well-known that $\widehat{\Lambda}$ is the
> closure of repulsive fixed points of loxodromic elements of $\Gamma$. (l.1246–1254)

> Therefore, $L(\gamma)$ is an isometry of the hyperbolic space ${\mathcal H}$ commuting with the
> loxodromic element $L(\gamma_{0})$: hence, it preserves the \emph{two} fixed points of
> $L(\gamma_{0})$ in $\partial{\mathcal H}$. (l.3294–3297)
>
> Now, an abelian subgroup of $SO_{0}(1,n-1)$ fixes a pair of isotropic directions, except if it
> consists only one elliptic elements fixing one and only one timelike vector $v_{0}$. (l.3356–3359)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, `SO₀(1, n−1)` is `lorentz d`, `𝒮 ≅ S^{d−1}`.

**Topologies (defined once, scoped).** `lorentzTopology`: `SO₀(1, d)` with the subspace topology of
`Minkowski d →L[ℝ] Minkowski d` (operator norm = matrix topology); `isomTopology`: `Isom(𝐌ⁿ)` with
that of `End × 𝐌ⁿ` (linear part, translation part). `linClosureIdentityComponent Γ` is Barbot's
`G₀`, the identity component of the closure of `L(Γ)` (not of `Γ`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| 5.1: `Γ ≤ Aff(n, ℝ)` discrete, closure in `GL(n, ℝ)` | restricted to the use (implied by the cited theorem): `Γ ≤ Isom(𝐌ⁿ)` only — in kb/0006's terms the `Prop` assumes more about `Γ` (⚠ strengthened hypothesis), the safe direction for an assumed external; closure in `SO₀(1, d)` (SCOPE) |
| 5.1: `Γ_nd = L⁻¹(G₀ ∩ L(Γ))` | `Γ ∩ L⁻¹⟨G₀⟩` (`⟨G₀⟩ = G₀`, a subgroup; SCOPE) |
| 5.2: `Γ` nilpotent, affine | restricted to the use (implied by the cited theorem): nilpotent subgroup of `Isom(𝐌ⁿ)` (⚠ strengthened hypothesis in kb/0006's terms, the safe direction for an external); `U` nonempty ✓ carried |
| 9.1: `Γ` without loxodromic | ✓ carried, on `L(Γ) ≤ SO₀(1, d)`; ⚠ weakened: no discreteness (Benoist needs none) |
| 9.1: "stabilizes an isotropic vector" | ⚠ strengthened conclusion: *fixes* a nonzero null vector (strongest form; SCOPE) |
| 4.17 input: `Γ` discrete, no global fixed point on `𝐇̄ⁿ⁻¹` (l.1212–1214) | ✓ carried |
| 4.17: "any closed invariant subset" | ⚠ strengthened: **nonempty** (finding: `∅` is closed and invariant) |
| Selberg: finitely generated linear group (char 0) | over `ℝ`, finite-dimensional `V`; proved since DEC-115 (`selbergLemma`, `Flat/SelbergProof`) |
| 10.4 folklore: "abelian ⇒ a pair of isotropic directions, or elliptic" | refuted (`not_abelianPairAsPrinted`, `n ≥ 3`); true forms proved for loxodromic and unipotent members |

## SCOPE (disclosed)
* Nothing here is a proof of an external theorem; the `Prop`s are hypotheses for §8–§11. Each has
  a proved witness that it is **not false** (it holds at `d = 0`, Barbot's `n = 1`:
  `auslanderCarriereDalbo_zero`, `maxUnipotentSubspace_zero`, `benoistNoLox_zero`,
  `limitSetMinimal_zero`; and `selbergLemma_real` for `V = ℝ`) and, where cheap, that it is **not
  trivially true** — its conclusion fails once the hypothesis is dropped:
  `not_benoist_conclusion_stdBoost` (`⟨boost⟩`, `d ≥ 1`), `not_limitSet_conclusion_stdBoostL`
  (the discrete `⟨boost⟩` — `discreteTopology_zpowers_stdBoostL` — has a global fixed point and
  the invariant `{eᵢ}` misses the repulsive `−eᵢ`), `not_maxUnipotent_conclusion_top` (the
  non-nilpotent `Isom(𝐌ⁿ)`, `d ≥ 1`: no nonempty invariant unipotent subspace at all), and
  `not_selberg_conclusion_torsion` (the infinite torsion group of root-of-unity rotations of
  `ℝ² ≅ ℂ`, necessarily not finitely generated: no torsion-free subgroup of finite index).
  `not_isTorsionFree_neg_one` only shows that `H = G` will not do in `SelbergLemma` (for `{±1}`
  the conclusion holds with `H = ⊥`). For `AuslanderCarriereDalbo` the witnesses are classes
  satisfying the conclusion (`ausConclusion_of_comm`); a non-discrete group with non-nilpotent
  `G₀` (e.g. `Isom(𝐌ⁿ)`, `d ≥ 2`) needs the connectedness of `SO₀(1, d)`, not done.
* **The `d = 0` "not false" witnesses are degenerate**: `SO₀(1, 0)` is trivial
  (`lorentz_zero_eq_one`) and `𝒮 = S⁻¹` is empty (`isEmpty_penroseSphere_zero`), so
  `auslanderCarriereDalbo_zero`, `maxUnipotentSubspace_zero` and `benoistNoLox_zero` hold because
  every group involved is abelian or trivial, and `limitSetMinimal_zero` holds vacuously. They
  show the `Prop`s are consistent, not that they are inhabited in an interesting dimension. In
  particular no group satisfying the hypotheses of `LimitSetMinimal` (discrete, no global fixed
  point on `𝐇̄ⁿ⁻¹`) is exhibited in `d ≥ 2` here; the natural one, the dihedral group generated by
  a boost along `xᵢ` and the rotation by `π` swapping `±eᵢ`, is not formalized.
* 5.1 is cited for `Aff(n)` and the closure in `GL(n)`; `SO₀(1, d)` is closed in `GL`, so the
  closure and its identity component agree — not proved here, and not needed by the consumer.
* `BenoistNoLox` states 9.1's conclusion, not Benoist's theorem: the latter is about Zariski
  closures, absent from mathlib, and 9.1's proof is not decomposable without them. The conclusion
  itself needs neither: it is proved in `Flat/GromovProof` (`benoistNoLox`, DEC-111) by Gromov's
  bounded/unbounded-orbit dichotomy on `ℍᵈ`, so `BenoistNoLox` is no longer an open external. "Fixes" is
  stronger than the printed "stabilizes (a direction)", and true: an element of `SO₀` scaling a null
  vector by `λ ≠ 1` is loxodromic — through `lorentz_trichotomy`, which is not used here.
* `LimitSetMinimal` is stated on `𝒮` (the paper's proof reduces 4.17 to `𝒮` through `δ`,
  l.1242–1251); the lift to `𝒥` (the basin of repulsion of `x₀`, l.1258–1266) is not formalized.
* The folklore of 10.4 in its corrected form ("an abelian subgroup fixes an isotropic direction —
  two if it has a loxodromic — or fixes a timelike vector") needs, for a parabolic `R ∘ U` with
  `R ≠ id` and for an all-elliptic group, the trichotomy: not formalized; the loxodromic and
  unipotent members are (`lorentzSphere_fixed_of_commute`, `fixed_null_of_commute_unipotent`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat

open Set Topology Module

variable {d : ℕ}

/-! ### 0. Topologies on `SO₀(1, d)` and `Isom(𝐌ⁿ)` -/

/-- A linear automorphism of `Minkowski d`, as an element of the normed algebra of continuous
linear endomorphisms (finite dimension: every linear map is continuous). -/
noncomputable def linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Minkowski d →L[ℝ] Minkowski d :=
  LinearMap.toContinuousLinearMap (A : Minkowski d →ₗ[ℝ] Minkowski d)

@[simp] theorem linToCLM_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (v : Minkowski d) :
    linToCLM A v = A v := rfl

theorem linToCLM_injective : Function.Injective (linToCLM (d := d)) := fun A B h =>
  LinearEquiv.ext fun v => by
    have := congrArg (fun f : Minkowski d →L[ℝ] Minkowski d => f v) h
    simpa using this

theorem linToCLM_mul (A B : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    linToCLM (A * B) = linToCLM A * linToCLM B :=
  ContinuousLinearMap.ext fun _ => rfl

theorem linToCLM_one : linToCLM (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 :=
  ContinuousLinearMap.ext fun _ => rfl

/-- **The topology of `SO₀(1, d)`**: the subspace topology of the operator-norm (equivalently,
matrix) topology of `Minkowski d →L[ℝ] Minkowski d`. **Scoped** to `Causal.Flat`, as
`Bieberbach`'s action of `E ≃ᵃⁱ[ℝ] E` is: mathlib puts no topology on `≃ₗ`, and a global
instance would be a latent diamond. -/
noncomputable scoped instance lorentzTopology : TopologicalSpace (lorentz d) :=
  TopologicalSpace.induced (fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d))
    inferInstance

theorem continuous_lorentz_linToCLM :
    Continuous (fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) :=
  continuous_induced_dom

theorem isEmbedding_lorentz_linToCLM :
    IsEmbedding (fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) :=
  ⟨⟨rfl⟩, fun _ _ h => Subtype.ext (linToCLM_injective h)⟩

scoped instance lorentz_t2Space : T2Space (lorentz d) :=
  isEmbedding_lorentz_linToCLM.t2Space

/-- Multiplication on `SO₀(1, d)` is continuous. -/
scoped instance lorentz_continuousMul : ContinuousMul (lorentz d) :=
  ⟨by
    rw [isEmbedding_lorentz_linToCLM.isInducing.continuous_iff]
    have : (fun p : lorentz d × lorentz d =>
        linToCLM ((p.1 * p.2 : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) =
        fun p => linToCLM (p.1 : Minkowski d ≃ₗ[ℝ] Minkowski d) *
          linToCLM (p.2 : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
      funext p; exact linToCLM_mul _ _
    rw [Function.comp_def, this]
    exact (continuous_lorentz_linToCLM.comp continuous_fst).mul
      (continuous_lorentz_linToCLM.comp continuous_snd)⟩

/-- The pair (linear part, translation part) of an isometry. -/
noncomputable def isomPair (g : isom d) : (Minkowski d →L[ℝ] Minkowski d) × Minkowski d :=
  (linToCLM (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear, transPart (g : Minkowski d ≃ᵃ[ℝ] Minkowski d))

theorem isomPair_injective : Function.Injective (isomPair (d := d)) := by
  intro g h hgh
  have h1 := linToCLM_injective (congrArg Prod.fst hgh)
  have h2 : transPart (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) =
      transPart (h : Minkowski d ≃ᵃ[ℝ] Minkowski d) := congrArg Prod.snd hgh
  refine Subtype.ext (AffineEquiv.ext fun x => ?_)
  rw [apply_eq_linear_add_transPart, apply_eq_linear_add_transPart, h1, h2]

/-- **The topology of `Isom(𝐌ⁿ)`**: the subspace topology of `Aff(n, ℝ) ⊆ End(ℝⁿ) × ℝⁿ`
(linear part, translation part). Scoped, as `lorentzTopology`. -/
noncomputable scoped instance isomTopology : TopologicalSpace (isom d) :=
  TopologicalSpace.induced isomPair inferInstance

/-! ### Group-theoretic helpers -/

theorem isNilpotent_closure_of_comm {G : Type*} [Group G] {S : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : Group.IsNilpotent (Subgroup.closure S) :=
  ⟨⟨1, Subgroup.upperCentralSeries_one_eq_top_iff.2 (Subgroup.isMulCommutative_closure h)⟩⟩

theorem isNilpotent_of_comm {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : Group.IsNilpotent H :=
  ⟨⟨1, Subgroup.upperCentralSeries_one_eq_top_iff.2 ⟨⟨fun a b => Subtype.ext (h _ a.2 _ b.2)⟩⟩⟩⟩

/-- The closure of a set of pairwise commuting elements of `SO₀(1, d)` is pairwise commuting. -/
theorem lorentz_closure_comm {S : Set (lorentz d)} (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
  intro x hx y hy
  have hc : IsClosed {p : lorentz d × lorentz d | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq continuous_mul (continuous_snd.mul continuous_fst)
  have hxy : (x, y) ∈ closure (S ×ˢ S) := by rw [closure_prod_eq]; exact ⟨hx, hy⟩
  exact closure_minimal (fun p hp => h p.1 hp.1 p.2 hp.2) hc hxy

/-- **`SO₀(1, 0)` is trivial** (Barbot's `n = 1`): a `minkQ`-preserving, time-orientation
preserving automorphism of the line `ℝ × ℝ⁰` is the identity. -/
theorem lorentz_zero_eq_one {A : Minkowski 0 ≃ₗ[ℝ] Minkowski 0} (hA : A ∈ lorentz 0) : A = 1 := by
  have h2 : ∀ v : Minkowski 0, v = v.1 • timeUnit 0 := fun v =>
    Prod.ext (by simp [timeUnit]) (Subsingleton.elim _ _)
  have hq := lorentz.minkQ_apply hA (timeUnit 0)
  have hf := lorentz.isFutureCausal_apply hA (v := timeUnit 0) ⟨by simp [timeUnit], by
    rw [minkQ_timeUnit]; norm_num⟩
  set a := (A (timeUnit 0)).1 with ha
  have hAt : A (timeUnit 0) = a • timeUnit 0 := h2 _
  rw [hAt, minkQ_smul, minkQ_timeUnit] at hq
  have ha0 : 0 ≤ a := by
    have := hf.1; rw [hAt] at this; simpa [timeUnit] using this
  have ha1 : a = 1 := by nlinarith
  refine LinearEquiv.ext fun v => ?_
  rw [h2 v, map_smul, hAt, ha1, one_smul]
  rfl

/-- In dimension `d = 0` every isometry is a translation. -/
theorem isom_zero_apply (g : isom 0) (x : Minkowski 0) : g • x = x + trOf g := by
  rw [smul_eq_lin_add, lorentz_zero_eq_one (linOf_mem g)]
  rfl

/-- **Translations commute**; in dimension `d = 0` every subgroup of `Isom` is abelian. -/
theorem isom_zero_comm (g h : isom 0) : g * h = h * g := by
  refine Subtype.ext (AffineEquiv.ext fun x => ?_)
  have e1 : ((g * h : isom 0) : Minkowski 0 ≃ᵃ[ℝ] Minkowski 0) x = g • (h • x) := rfl
  have e2 : ((h * g : isom 0) : Minkowski 0 ≃ᵃ[ℝ] Minkowski 0) x = h • (g • x) := rfl
  rw [e1, e2, isom_zero_apply, isom_zero_apply, isom_zero_apply, isom_zero_apply]
  abel

/-! ### 1. Auslander, Carrière–Dal'bo — `bthm:ausl` -/

/-- Barbot's `L(Γ)`, a subgroup of `SO₀(1, d)`. -/
noncomputable abbrev linearImage (Γ : Subgroup (isom d)) : Subgroup (lorentz d) :=
  Γ.map linearPart

/-- Barbot's `G₀`: the identity component of the closure of `L(Γ)` (l.1701–1702), in the
topology `lorentzTopology`. -/
def linClosureIdentityComponent (Γ : Subgroup (isom d)) : Set (lorentz d) :=
  connectedComponentIn (closure (linearImage Γ : Set (lorentz d))) 1

/-- Barbot's `Γ_nd = L⁻¹(G₀ ∩ L(Γ)) ∩ Γ` (l.1702–1703), with `G₀` replaced by the subgroup it
generates (equal to it: `G₀` is a subgroup, SCOPE). -/
noncomputable def nonDiscretePart (Γ : Subgroup (isom d)) : Subgroup (isom d) :=
  Γ ⊓ (Subgroup.closure (linClosureIdentityComponent Γ)).comap linearPart

theorem nonDiscretePart_le (Γ : Subgroup (isom d)) : nonDiscretePart Γ ≤ Γ := inf_le_left

/-- The conclusion of `bthm:ausl` for one group `Γ`: `G₀` is nilpotent and `Γ_nd` is nilpotent. -/
def AusConclusion (Γ : Subgroup (isom d)) : Prop :=
  Group.IsNilpotent (Subgroup.closure (linClosureIdentityComponent Γ)) ∧
    Group.IsNilpotent (nonDiscretePart Γ)

variable (d) in
/-- **Auslander's theorem, refined by Carrière and Dal'bo** (`bthm:ausl`, l.1697–1704,
`cardal` Theorem 1.2.1), external (DEC-36), for discrete subgroups of `Isom(𝐌ⁿ)`. -/
def AuslanderCarriereDalbo : Prop :=
  ∀ Γ : Subgroup (isom d), DiscreteTopology Γ → AusConclusion Γ

/-- **Witness: abelian groups.** For an abelian `Γ` the conclusion holds, with no discreteness. -/
theorem ausConclusion_of_comm {Γ : Subgroup (isom d)} (hΓ : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g) :
    AusConclusion Γ := by
  have hL : ∀ x ∈ (linearImage Γ : Set (lorentz d)), ∀ y ∈ (linearImage Γ : Set (lorentz d)),
      x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hΓ g hg h hh]
  have hcl := lorentz_closure_comm hL
  refine ⟨isNilpotent_closure_of_comm fun x hx y hy =>
    hcl x (connectedComponentIn_subset _ _ hx) y (connectedComponentIn_subset _ _ hy),
    isNilpotent_of_comm fun x hx y hy => hΓ x hx.1 y hy.1⟩

theorem ausConclusion_bot : AusConclusion (⊥ : Subgroup (isom d)) :=
  ausConclusion_of_comm fun g hg h hh => by
    rw [Subgroup.mem_bot] at hg hh; rw [hg, hh]

/-- **Witness: dimension `d = 0`** (Barbot's `n = 1`): the Prop holds, every group being abelian. -/
theorem auslanderCarriereDalbo_zero : AuslanderCarriereDalbo 0 :=
  fun _ _ => ausConclusion_of_comm fun g _ h _ => isom_zero_comm g h

/-! ### 2. The maximal unipotent subspace — `bthm:unip` -/

/-- `U` is `N`-invariant and `N` acts unipotently on it: for `γ ∈ N`, `(L(γ) − id)^m` vanishes on
the direction of `U` for some `m`. -/
def IsUnipotentInvariant (N : Subgroup (isom d)) (U : AffineSubspace ℝ (Minkowski d)) : Prop :=
  (∀ γ ∈ N, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) ∧
    ∀ γ ∈ N, ∃ m : ℕ, ∀ w ∈ U.direction, (pOf (linOf γ) ^ m) w = 0

/-- `U` is a **maximal** `N`-invariant affine subspace on which `N` acts unipotently. -/
def IsMaxUnipotent (N : Subgroup (isom d)) (U : AffineSubspace ℝ (Minkowski d)) : Prop :=
  IsUnipotentInvariant N U ∧ ∀ U', IsUnipotentInvariant N U' → U ≤ U' → U' = U

variable (d) in
/-- **Carrière–Dal'bo's maximal unipotent subspace** (`bthm:unip`, l.1709–1717, `cardal`
Proposition 1.2.2), external (DEC-36), for nilpotent groups of isometries of `𝐌ⁿ`: a nonempty
maximal invariant unipotent affine subspace exists, and it is the only maximal one. -/
def MaxUnipotentSubspace : Prop :=
  ∀ N : Subgroup (isom d), Group.IsNilpotent N →
    ∃ U : AffineSubspace ℝ (Minkowski d), (U : Set (Minkowski d)).Nonempty ∧ IsMaxUnipotent N U ∧
      ∀ U', IsMaxUnipotent N U' → U' = U

/-- **Witness: groups of translations.** If every element of `N` has trivial linear part, `𝐌ⁿ`
itself is the unique maximal unipotent subspace. -/
theorem maxUnipotent_of_translations {N : Subgroup (isom d)} (hN : ∀ γ ∈ N, linOf γ = 1) :
    (⊤ : AffineSubspace ℝ (Minkowski d)) ≠ ⊥ ∧ IsMaxUnipotent N ⊤ ∧
      ∀ U', IsMaxUnipotent N U' → U' = ⊤ := by
  have htop : IsUnipotentInvariant N ⊤ :=
    ⟨fun _ _ _ => by simp, fun γ hγ => ⟨1, fun w _ => by rw [hN γ hγ, pOf_one]; rfl⟩⟩
  refine ⟨fun h => ?_, ⟨htop, fun U' _ hU' => top_le_iff.1 hU'⟩, fun U' hU' =>
    (hU'.2 ⊤ htop le_top).symm⟩
  have : (0 : Minkowski d) ∈ (⊤ : AffineSubspace ℝ (Minkowski d)) := AffineSubspace.mem_top ℝ _ 0
  rw [h] at this; exact (AffineSubspace.notMem_bot ℝ _ 0) this

/-- **Witness: dimension `d = 0`** (Barbot's `n = 1`): the Prop holds. -/
theorem maxUnipotentSubspace_zero : MaxUnipotentSubspace 0 := by
  intro N _
  have hN : ∀ γ ∈ N, linOf γ = 1 := fun γ _ => lorentz_zero_eq_one (linOf_mem γ)
  obtain ⟨-, h1, h2⟩ := maxUnipotent_of_translations hN
  exact ⟨⊤, ⟨0, AffineSubspace.mem_top ℝ _ 0⟩, h1, h2⟩

theorem stdBoost_apply_add (i : Fin d) (ζ : ℝ) :
    stdBoost i ζ (timeUnit d + spaceUnit i) = Real.exp ζ • (timeUnit d + spaceUnit i) := by
  have h0 : minkB (timeUnit d + spaceUnit i) (timeUnit d) = -1 := by
    rw [minkB_add_left, ← minkQ_eq_minkB, minkQ_timeUnit, minkB_comm, minkB_timeUnit_spaceUnit]
    ring
  have h1 : minkB (timeUnit d + spaceUnit i) (spaceUnit i) = 1 := by
    rw [minkB_add_left, minkB_timeUnit_spaceUnit, ← minkQ_eq_minkB, minkQ_spaceUnit]; ring
  rw [stdBoost, boost_apply, boostLin_apply, h0, h1, ← Real.cosh_add_sinh]; module

theorem stdBoost_apply_sub (i : Fin d) (ζ : ℝ) :
    stdBoost i ζ (timeUnit d - spaceUnit i) = Real.exp (-ζ) • (timeUnit d - spaceUnit i) := by
  have h0 : minkB (timeUnit d - spaceUnit i) (timeUnit d) = -1 := by
    rw [minkB_sub_left, ← minkQ_eq_minkB, minkQ_timeUnit, minkB_comm, minkB_timeUnit_spaceUnit]
    ring
  have h1 : minkB (timeUnit d - spaceUnit i) (spaceUnit i) = -1 := by
    rw [minkB_sub_left, minkB_timeUnit_spaceUnit, ← minkQ_eq_minkB, minkQ_spaceUnit]; ring
  rw [stdBoost, boost_apply, boostLin_apply, h0, h1, ← Real.cosh_sub_sinh]; module

theorem pow_pOf_apply_of_eigen {A : Minkowski d ≃ₗ[ℝ] Minkowski d} {w : Minkowski d} {c : ℝ}
    (h : A w = c • w) (m : ℕ) : (pOf A ^ m) w = (c - 1) ^ m • w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, pOf_apply, h,
      show c • w - w = (c - 1) • w by rw [sub_smul, one_smul], map_smul, ih, smul_smul,
      ← pow_succ']

/-- **Witness (not trivially true)** for `MaxUnipotentSubspace`, `d ≥ 1` (Barbot's `n ≥ 2`): for
the non-nilpotent group `N = Isom(𝐌ⁿ)` no nonempty invariant unipotent affine subspace exists —
the translations force such a `U` to be `𝐌ⁿ`, and the boost `B` along `xᵢ` scales `t + eᵢ` by
`e ≠ 1`, so no power of `L(B) − id` kills it. So the hypothesis "nilpotent" is load-bearing. -/
theorem not_maxUnipotent_conclusion_top (i : Fin d) :
    ¬∃ U : AffineSubspace ℝ (Minkowski d), (U : Set (Minkowski d)).Nonempty ∧
      IsUnipotentInvariant (⊤ : Subgroup (isom d)) U := by
  rintro ⟨U, ⟨x₀, hx₀⟩, hinv, hpow⟩
  have hall : ∀ y : Minkowski d, y ∈ U := fun y => by
    have h := (hinv ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (y - x₀), constVAdd_mem_isom _⟩
      (Subgroup.mem_top _) x₀).2 hx₀
    rw [isom_smul_def] at h
    simpa using h
  obtain ⟨m, hm⟩ := hpow (boostIsom i 1) (Subgroup.mem_top _)
  have hw : timeUnit d + spaceUnit i ∈ U.direction := by
    have := AffineSubspace.vsub_mem_direction (hall (timeUnit d + spaceUnit i + x₀)) hx₀
    simpa using this
  have h0 := hm _ hw
  have hlin : linOf (boostIsom i 1) = stdBoost i 1 := rfl
  rw [hlin, pow_pOf_apply_of_eigen (stdBoost_apply_add i 1) m, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · have : Real.exp 1 - 1 ≠ 0 := sub_ne_zero.2 fun h => one_ne_zero ((Real.exp_eq_one_iff 1).1 h)
    exact this (pow_eq_zero_iff'.1 h0).1
  · have := congrArg Prod.fst h0
    simp [timeUnit, spaceUnit] at this

/-! #### Transport by an element normalising `N` -/

theorem mem_map_isom_iff (η : isom d) (U : AffineSubspace ℝ (Minkowski d)) (y : Minkowski d) :
    y ∈ U.map (η : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap ↔ η⁻¹ • y ∈ U := by
  rw [AffineSubspace.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show η⁻¹ • (η • x) ∈ U
    rwa [inv_smul_smul]
  · intro hy
    refine ⟨η⁻¹ • y, hy, ?_⟩
    show η • (η⁻¹ • y) = y
    rw [smul_inv_smul]

theorem linOf_inv_conj (η γ : isom d) : linOf (η⁻¹ * γ * η) = (linOf η)⁻¹ * linOf γ * linOf η := by
  simp only [linOf_eq_linearPart, map_mul, map_inv]
  rfl

/-- If `η⁻¹ N η ⊆ N`, the image of an `N`-invariant unipotent subspace by `η` is one. -/
theorem IsUnipotentInvariant.map {N : Subgroup (isom d)} {U : AffineSubspace ℝ (Minkowski d)}
    (h : IsUnipotentInvariant N U) {η : isom d} (hη : ∀ γ ∈ N, η⁻¹ * γ * η ∈ N) :
    IsUnipotentInvariant N (U.map (η : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap) := by
  refine ⟨fun γ hγ y => ?_, fun γ hγ => ?_⟩
  · rw [mem_map_isom_iff, mem_map_isom_iff]
    have e : η⁻¹ • (γ • y) = (η⁻¹ * γ * η) • (η⁻¹ • y) := by
      rw [mul_smul, mul_smul, smul_inv_smul]
    rw [e]; exact h.1 _ (hη γ hγ) _
  · obtain ⟨m, hm⟩ := h.2 _ (hη γ hγ)
    refine ⟨m, fun w hw => ?_⟩
    rw [AffineSubspace.map_direction] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    have hc : linOf γ = linOf η * linOf (η⁻¹ * γ * η) * (linOf η)⁻¹ := by
      rw [linOf_inv_conj]; group
    have := pow_pOf_conj (A := linOf (η⁻¹ * γ * η)) (linOf η) m
      ((η : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear w₀)
    rw [← hc] at this
    rw [show (η : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap.linear w₀ = linOf η w₀ from rfl,
      this, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hm w₀ hw₀, map_zero]

theorem map_map_isom_inv (η : isom d) (U : AffineSubspace ℝ (Minkowski d)) :
    (U.map (η : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap).map
      ((η⁻¹ : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap = U := by
  ext y
  rw [mem_map_isom_iff, mem_map_isom_iff, inv_inv, inv_smul_smul]

/-- If `η` normalises `N`, the image of a maximal unipotent subspace by `η` is one. -/
theorem IsMaxUnipotent.map {N : Subgroup (isom d)} {U : AffineSubspace ℝ (Minkowski d)}
    (h : IsMaxUnipotent N U) {η : isom d} (hη : ∀ γ ∈ N, η⁻¹ * γ * η ∈ N)
    (hη' : ∀ γ ∈ N, η * γ * η⁻¹ ∈ N) :
    IsMaxUnipotent N (U.map (η : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap) := by
  refine ⟨h.1.map hη, fun U' hU' hle => ?_⟩
  have hη'' : ∀ γ ∈ N, (η⁻¹)⁻¹ * γ * η⁻¹ ∈ N := fun γ hγ => by rw [inv_inv]; exact hη' γ hγ
  have h1 := hU'.map hη''
  have h2 : U ≤ U'.map ((η⁻¹ : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d).toAffineMap := by
    rw [← map_map_isom_inv η U]; exact AffineSubspace.map_mono _ hle
  have h3 := h.2 _ h1 h2
  rw [← h3]
  ext y
  rw [mem_map_isom_iff, mem_map_isom_iff, inv_inv, smul_inv_smul]

/-! #### `Γ_nd` is normal in `Γ`, and the consumer of `bthm:ausl` + `bthm:unip` -/

/-- Conjugation by an element of `L(Γ)` preserves `G₀` (the identity component of a closed
subgroup is invariant under the subgroup's inner automorphisms). -/
theorem conj_mem_linClosureIdentityComponent {Γ : Subgroup (isom d)} {a : lorentz d}
    (ha : a ∈ linearImage Γ) {x : lorentz d} (hx : x ∈ linClosureIdentityComponent Γ) :
    a * x * a⁻¹ ∈ linClosureIdentityComponent Γ := by
  set F := closure (linearImage Γ : Set (lorentz d)) with hF
  set c : lorentz d → lorentz d := fun y => a * y * a⁻¹ with hcdef
  have hc : Continuous c := (continuous_const.mul continuous_id).mul continuous_const
  have hcF : MapsTo c F F := fun y hy => map_mem_closure hc hy fun z hz =>
    (linearImage Γ).mul_mem ((linearImage Γ).mul_mem ha hz) ((linearImage Γ).inv_mem ha)
  have h1 : (1 : lorentz d) ∈ F := subset_closure (linearImage Γ).one_mem
  have hpre : IsPreconnected (c '' linClosureIdentityComponent Γ) :=
    isPreconnected_connectedComponentIn.image c hc.continuousOn
  have hsub : c '' linClosureIdentityComponent Γ ⊆ connectedComponentIn F 1 :=
    hpre.subset_connectedComponentIn ⟨1, mem_connectedComponentIn h1, by simp [c]⟩
      (image_subset_iff.2 fun y hy => hcF (connectedComponentIn_subset _ _ hy))
  exact hsub ⟨x, hx, rfl⟩

theorem conj_mem_closure_linClosureIdentityComponent {Γ : Subgroup (isom d)} {a : lorentz d}
    (ha : a ∈ linearImage Γ) {x : lorentz d} (hx : x ∈ Subgroup.closure (linClosureIdentityComponent Γ)) :
    a * x * a⁻¹ ∈ Subgroup.closure (linClosureIdentityComponent Γ) := by
  have : Subgroup.closure (linClosureIdentityComponent Γ) ≤
      (Subgroup.closure (linClosureIdentityComponent Γ)).comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.subset_closure (conj_mem_linClosureIdentityComponent ha hy)
  simpa using this hx

/-- **`Γ_nd` is normal in `Γ`.** -/
theorem conj_mem_nonDiscretePart {Γ : Subgroup (isom d)} {γ η : isom d} (hγ : γ ∈ Γ)
    (hη : η ∈ nonDiscretePart Γ) : γ * η * γ⁻¹ ∈ nonDiscretePart Γ := by
  refine ⟨Γ.mul_mem (Γ.mul_mem hγ hη.1) (Γ.inv_mem hγ), ?_⟩
  show linearPart (γ * η * γ⁻¹) ∈ Subgroup.closure (linClosureIdentityComponent Γ)
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_closure_linClosureIdentityComponent ⟨γ, hγ, rfl⟩ hη.2

/-- **The consumer of `bthm:ausl` and `bthm:unip`** ([10.G], l.3339–3344: "the non-discrete part
`Γ_nd` is nilpotent; and there is a unique maximal `𝐔` on which the action of `Γ_nd` is
unipotent. Being unique, `𝐔` is also preserved by `Γ`"; the same step at l.1729–1731 and in
[10.M], l.3273–3276). Proved from the two Props: the uniqueness is spent through the normality
of `Γ_nd` in `Γ`. -/
theorem exists_invariant_maxUnipotent (hA : AuslanderCarriereDalbo d)
    (hU : MaxUnipotentSubspace d) {Γ : Subgroup (isom d)} (hΓ : DiscreteTopology Γ) :
    ∃ U : AffineSubspace ℝ (Minkowski d), (U : Set (Minkowski d)).Nonempty ∧
      IsMaxUnipotent (nonDiscretePart Γ) U ∧ ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U := by
  obtain ⟨U, hne, hmax, huniq⟩ := hU _ (hA Γ hΓ).2
  refine ⟨U, hne, hmax, fun γ hγ x => ?_⟩
  have hmap := hmax.map (η := γ)
    (fun η hη => by simpa using conj_mem_nonDiscretePart (Γ.inv_mem hγ) hη)
    (fun η hη => conj_mem_nonDiscretePart hγ hη)
  have heq := huniq _ hmap
  conv_lhs => rw [← heq]
  rw [mem_map_isom_iff, inv_smul_smul]

/-! ### 3. Benoist and the nonloxodromic case — `bprop:sanloxo` -/

/-- The conclusion of `bprop:sanloxo` (l.2575–2577) for one subgroup `H ≤ SO₀(1, d)`: `H` fixes a
timelike vector — `H` lies in a conjugate of `SO(n − 1)`, the stabiliser of a point of `𝐇ⁿ⁻¹` —
or `H` fixes a nonzero null vector ("stabilizes an isotropic vector"). -/
def FixesTimelikeOrNull (H : Subgroup (lorentz d)) : Prop :=
  (∃ v : Minkowski d, minkQ v < 0 ∧ ∀ A ∈ H, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v) ∨
    ∃ v : Minkowski d, v ≠ 0 ∧ minkQ v = 0 ∧ ∀ A ∈ H, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v

variable (d) in
/-- **Prop 9.1 as an external** (`bprop:sanloxo`, l.2574–2577; DEC-36; not proved in this
module, now proved as `benoistNoLox` in `Flat/GromovProof`, DEC-111): a subgroup of
`SO₀(1, d)` with no loxodromic element has a finite-index subgroup fixing a timelike or a
nonzero null vector. Its proof (l.2580–2597) runs through the Zariski closure: Benoist's theorem
(`benoist`, l.2581–2582: no loxodromic element in `Γ` ⇒ none in its Zariski closure `G`), the
finiteness of the components of an algebraic group (l.2582–2584), and two Lie-theoretic steps on
`G₀`; mathlib has no Zariski closure of a subgroup of `GL(V)`, so the whole conclusion is the
honest unit. Strongest form: "stabilizes an isotropic vector" is read as *fixes* it (an element
of `SO₀` scaling a null vector by `λ ≠ 1` is loxodromic, so the two readings agree here). -/
def BenoistNoLox : Prop :=
  ∀ G : Subgroup (lorentz d), (∀ A ∈ G, ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) →
    ∃ H : Subgroup (lorentz d), H ≤ G ∧ H.relIndex G ≠ 0 ∧ FixesTimelikeOrNull H

theorem lorentz_pow_apply_of_eigen (A : lorentz d) {u : Minkowski d} {l : ℝ}
    (h : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) u = l • u) (n : ℕ) :
    ((A ^ n : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) u = l ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

/-- A vector fixed by a power `A ^ n`, `n ≥ 1`, of a loxodromic `A` is spacelike or zero: it is
orthogonal to both null eigenvectors, hence to a timelike vector. -/
theorem minkQ_pos_of_fixed_pow_loxodromic {A : lorentz d}
    (hA : IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {n : ℕ} (hn : n ≠ 0)
    {v : Minkowski d} (hv : ((A ^ n : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v)
    (hv0 : v ≠ 0) : 0 < minkQ v := by
  obtain ⟨-, u, u', l, -, -, -, -, -, hq, hq', huu', hl, hl1, hAu, hAu', -⟩ := hA.frame
  have hQ : ∀ w, minkQ (((A ^ n : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w) = minkQ w :=
    fun w => lorentz.minkQ_apply (A ^ n).2 w
  have h1 := minkB_map hQ u v
  rw [lorentz_pow_apply_of_eigen A hAu n, hv, minkB_smul_left] at h1
  have h2 := minkB_map hQ u' v
  rw [lorentz_pow_apply_of_eigen A hAu' n, hv, minkB_smul_left] at h2
  have hln : l ^ n ≠ 1 := fun h => hl1 ((pow_eq_one_iff_of_nonneg hl.le hn).1 h)
  have hln' : l⁻¹ ^ n ≠ 1 := fun h =>
    hl1 (inv_eq_one.1 ((pow_eq_one_iff_of_nonneg (inv_pos.2 hl).le hn).1 h))
  have e1 : minkB u v = 0 := by
    have : (l ^ n - 1) * minkB u v = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hln)
  have e2 : minkB u' v = 0 := by
    have : (l⁻¹ ^ n - 1) * minkB u' v = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hln')
  have ht : minkQ (u - minkB u u' • u') < 0 := by
    rw [sub_eq_add_neg, minkQ_add, minkQ_neg, minkQ_smul, hq', minkB_neg_right, minkB_smul_right,
      hq]
    nlinarith [mul_self_pos.2 huu']
  refine minkQ_pos_of_orth_timelike ht ?_ hv0
  rw [minkB_sub_left, minkB_smul_left, e1, e2]; ring

/-- **The hypothesis of `BenoistNoLox` cannot be dropped**: no finite-index subgroup of the cyclic
group of a loxodromic element fixes a timelike or a nonzero null vector. -/
theorem not_fixesTimelikeOrNull_of_isLoxodromic {A : lorentz d}
    (hA : IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {H : Subgroup (lorentz d)}
    (hi : H.relIndex (Subgroup.zpowers A) ≠ 0) : ¬FixesTimelikeOrNull H := by
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := H.subgroupOf (Subgroup.zpowers A)) hi ⟨A, Subgroup.mem_zpowers A⟩
  have hAn : A ^ n ∈ H := by simpa using Subgroup.mem_subgroupOf.1 hmem
  rintro (⟨v, hv, hfix⟩ | ⟨v, hv0, hv, hfix⟩)
  · have hv0 : v ≠ 0 := fun h => by rw [h, minkQ_zero] at hv; exact lt_irrefl _ hv
    have := minkQ_pos_of_fixed_pow_loxodromic hA hn.ne' (hfix _ hAn) hv0
    linarith
  · have := minkQ_pos_of_fixed_pow_loxodromic hA hn.ne' (hfix _ hAn) hv0
    linarith

/-- **Witness (not trivially true)**, `d ≥ 1` (Barbot's `n ≥ 2`): for the standard boost `B`, the
conclusion of `BenoistNoLox` fails for `⟨B⟩`, which contains the loxodromic `B`. -/
theorem not_benoist_conclusion_stdBoost (i : Fin d) :
    ¬∃ H : Subgroup (lorentz d),
      H ≤ Subgroup.zpowers (⟨stdBoost i 1, stdBoost_mem_lorentz i 1⟩ : lorentz d) ∧
      H.relIndex (Subgroup.zpowers (⟨stdBoost i 1, stdBoost_mem_lorentz i 1⟩ : lorentz d)) ≠ 0 ∧
      FixesTimelikeOrNull H :=
  fun ⟨_, _, hi, hf⟩ =>
    not_fixesTimelikeOrNull_of_isLoxodromic (stdBoost_isLoxodromic i one_ne_zero) hi hf

/-- **Witness (not false)**: `BenoistNoLox 0` holds (Barbot's `n = 1`; `SO₀(1, 0)` is trivial). -/
theorem benoistNoLox_zero : BenoistNoLox 0 := fun G _ =>
  ⟨G, le_rfl, by rw [Subgroup.relIndex_self]; exact one_ne_zero,
    Or.inl ⟨timeUnit 0, by rw [minkQ_timeUnit]; norm_num, fun A _ => by
      rw [lorentz_zero_eq_one A.2]; rfl⟩⟩

/-- **The consumer of `bprop:sanloxo`** (l.2600–2602, l.2605–2609, l.2621–2622: "the nonloxodromic
case decomposes in the elliptic case, and the parabolic case"): a group of isometries with no
loxodromic linear part has a finite-index subgroup whose linear parts all fix one timelike vector
(and are then elliptic, [9.E]) or all fix one nonzero null vector ([9.P]). -/
theorem exists_finiteIndex_fixes_of_noLox (hB : BenoistNoLox d) {Γ : Subgroup (isom d)}
    (hΓ : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ((∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v ∧ IsElliptic (linOf γ)) ∨
        ∃ v : Minkowski d, v ≠ 0 ∧ minkQ v = 0 ∧ ∀ γ ∈ Γ', linOf γ v = v) := by
  obtain ⟨H, -, hi, hfix⟩ := hB (linearImage Γ) (by
    rintro _ ⟨γ, hγ, rfl⟩; rw [← linOf_eq_linearPart]; exact hΓ γ hγ)
  refine ⟨Γ ⊓ H.comap linearPart, inf_le_left, ?_, ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]; exact hi
  · rcases hfix with ⟨v, hv, hf⟩ | ⟨v, hv0, hv, hf⟩
    · refine Or.inl ⟨v, hv, fun γ hγ => ?_⟩
      have h1 : linOf γ v = v := by rw [linOf_eq_linearPart]; exact hf _ hγ.2
      exact ⟨h1, isElliptic_of_fixed_timelike (fun w => lorentz.minkQ_apply (linOf_mem γ) w) hv h1⟩
    · exact Or.inr ⟨v, hv0, hv, fun γ hγ => by rw [linOf_eq_linearPart]; exact hf _ hγ.2⟩

/-! ### 4. The limit set — the input of `bprop:admlox` -/

/-- `u ∈ 𝒮` is a **repulsive fixed point** of `A` (l.1254–1258): `A` is loxodromic and `(1, u)` is
an eigenvector of `A` for an eigenvalue `0 < λ < 1`. -/
def IsRepulsiveFixed (A : lorentz d) (u : PenroseSphere d) : Prop :=
  IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) ∧
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = l • nullVec u

/-- The repulsive fixed points in `𝒮` of the loxodromic elements of `G`. -/
def repulsiveSet (G : Subgroup (lorentz d)) : Set (PenroseSphere d) :=
  {u | ∃ A ∈ G, IsRepulsiveFixed A u}

/-- `G` has a **global fixed point on `𝐇̄ⁿ⁻¹ = 𝐇ⁿ⁻¹ ∪ 𝒮`** (l.1212–1214): it fixes a timelike
vector, or a point of `𝒮`. -/
def HasGlobalFixedPoint (G : Subgroup (lorentz d)) : Prop :=
  (∃ v : Minkowski d, minkQ v < 0 ∧ ∀ A ∈ G, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v) ∨
    ∃ u : PenroseSphere d, ∀ A ∈ G, lorentzSphere A u = u

/-- `F ⊆ 𝒮` is invariant under the conformal action of `G` (`lorentzSphere`, l.798). -/
def IsSphereInvariant (G : Subgroup (lorentz d)) (F : Set (PenroseSphere d)) : Prop :=
  ∀ A ∈ G, ∀ u ∈ F, lorentzSphere A u ∈ F

variable (d) in
/-- **The minimality of the limit set, as an external** (the input of `bprop:admlox`, l.1246–1254;
DEC-36): for a discrete subgroup `G` of `SO₀(1, d)` without global fixed point on `𝐇̄ⁿ⁻¹` (the
standing hypothesis of l.1212–1214), every repulsive fixed point of a loxodromic element of `G`
lies in every nonempty closed `G`-invariant subset of `𝒮`. Barbot: "there is a closed subset
`Λ̂`, the limit set, contained in every `Γ`-invariant closed subset […] `Λ̂` is the closure of
repulsive fixed points of loxodromic elements" (classical, `ratcliffe` §12). **Nonempty** is
added: `∅` is closed and invariant (finding). -/
def LimitSetMinimal : Prop :=
  ∀ G : Subgroup (lorentz d), DiscreteTopology G → ¬HasGlobalFixedPoint G →
    ∀ F : Set (PenroseSphere d), IsClosed F → F.Nonempty → IsSphereInvariant G F →
      repulsiveSet G ⊆ F

theorem nullVec_injective_smul {u u' : PenroseSphere d} {c : ℝ}
    (h : nullVec u = c • nullVec u') : u = u' := by
  have h1 : (1 : ℝ) = c := by simpa [nullVec] using congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [← h1, one_smul] at h2
  exact Subtype.ext h2

/-- An eigenvector `(1, u)` of `A` gives a fixed point `u` of the action on `𝒮`. -/
theorem lorentzSphere_eq_of_eigen {A : lorentz d} {u : PenroseSphere d} {c : ℝ}
    (h : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u) :
    lorentzSphere A u = u :=
  nullVec_injective_smul (c := (lorentzScale A u)⁻¹ * c) (by
    rw [nullVec_lorentzSphere, h, smul_smul])

theorem continuous_lorentzSphere (A : lorentz d) : Continuous (lorentzSphere A) := by
  refine Continuous.subtype_mk ?_ _
  refine ((continuous_lorentzScale A).inv₀ fun u => (lorentzScale_pos A u).ne').smul ?_
  exact continuous_snd.comp
    (((A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Minkowski d →ₗ[ℝ] Minkowski d).continuous_of_finiteDimensional.comp
      continuous_nullVec)

/-- Conjugation carries repulsive fixed points: `[A]u` is repulsive for `A B A⁻¹`. -/
theorem IsRepulsiveFixed.conj {A B : lorentz d} {u : PenroseSphere d} (h : IsRepulsiveFixed B u) :
    IsRepulsiveFixed (A * B * A⁻¹) (lorentzSphere A u) := by
  obtain ⟨hB, l, hl, hl1, hBu⟩ := h
  refine ⟨by simpa using hB.conj A.2, l, hl, hl1, ?_⟩
  rw [nullVec_lorentzSphere, map_smul, smul_comm]
  congr 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply, hBu, map_smul]

theorem isSphereInvariant_repulsiveSet (G : Subgroup (lorentz d)) :
    IsSphereInvariant G (repulsiveSet G) :=
  fun A hA _ ⟨B, hB, h⟩ => ⟨A * B * A⁻¹, G.mul_mem (G.mul_mem hA hB) (G.inv_mem hA), h.conj⟩

theorem IsSphereInvariant.closure {G : Subgroup (lorentz d)} {F : Set (PenroseSphere d)}
    (hF : IsSphereInvariant G F) : IsSphereInvariant G (closure F) :=
  fun A hA _ hu => map_mem_closure (continuous_lorentzSphere A) hu fun v hv => hF A hA v hv

/-- **The consumer of `LimitSetMinimal`: `bprop:admlox` on `𝒮`** (l.1232–1238, read through
`δ`, l.1242–1251): the closure `Λ̂` of the repulsive fixed points is `G`-invariant
(unconditionally) and contained in every nonempty closed `G`-invariant subset of `𝒮`. -/
theorem limitSet_invariant_and_minimal (hL : LimitSetMinimal d) {G : Subgroup (lorentz d)}
    (hG : DiscreteTopology G) (hfix : ¬HasGlobalFixedPoint G) :
    IsSphereInvariant G (closure (repulsiveSet G)) ∧
      ∀ F : Set (PenroseSphere d), IsClosed F → F.Nonempty → IsSphereInvariant G F →
        closure (repulsiveSet G) ⊆ F :=
  ⟨(isSphereInvariant_repulsiveSet G).closure, fun F hF hne hinv =>
    closure_minimal (hL G hG hfix F hF hne hinv) hF⟩

theorem isEmpty_penroseSphere_zero : IsEmpty (PenroseSphere 0) := ⟨fun u => by
  have h := norm_penroseSphere u
  have h0 : (u : EuclideanSpace ℝ (Fin 0)) = 0 := by ext i; exact i.elim0
  rw [h0, norm_zero] at h
  exact zero_ne_one h⟩

/-- **Witness (not false)**: `LimitSetMinimal 0` holds (`𝒮 = S⁻¹ = ∅` for Barbot's `n = 1`). -/
theorem limitSetMinimal_zero : LimitSetMinimal 0 :=
  fun _ _ _ _ _ _ _ u _ => (isEmpty_penroseSphere_zero.false u).elim

/-! #### The hypothesis "no global fixed point" cannot be dropped: the cyclic group of a boost -/

theorem lorentz_zpow_apply_of_eigen (A : lorentz d) {u : Minkowski d} {l : ℝ} (hl : l ≠ 0)
    (h : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) u = l • u) (k : ℤ) :
    ((A ^ k : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) u = l ^ k • u := by
  rcases k with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact lorentz_pow_apply_of_eigen A h n
  · have hp := lorentz_pow_apply_of_eigen A h (n + 1)
    rw [zpow_negSucc, Subgroup.coe_inv, zpow_negSucc, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_eq, map_smul, hp, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl),
      one_smul]

/-- The standard boost of rapidity `1`, as an element of `SO₀(1, d)`. -/
noncomputable def stdBoostL (i : Fin d) : lorentz d := ⟨stdBoost i 1, stdBoost_mem_lorentz i 1⟩

/-- The two fixed points `±eᵢ ∈ 𝒮` of the standard boost along `i`. -/
noncomputable def boostPt (i : Fin d) (σ : ℝ) (hσ : |σ| = 1) : PenroseSphere d :=
  ⟨σ • EuclideanSpace.single i (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, norm_smul, PiLp.norm_single, Real.norm_eq_abs, hσ,
      norm_one, mul_one]⟩

theorem nullVec_boostPt_one (i : Fin d) :
    nullVec (boostPt i 1 (by norm_num)) = timeUnit d + spaceUnit i := by
  refine Prod.ext ?_ ?_ <;> simp [nullVec, boostPt, timeUnit, spaceUnit]

theorem nullVec_boostPt_neg_one (i : Fin d) :
    nullVec (boostPt i (-1) (by norm_num)) = timeUnit d - spaceUnit i := by
  refine Prod.ext ?_ ?_ <;> simp [nullVec, boostPt, timeUnit, spaceUnit]

theorem boostPt_ne (i : Fin d) : boostPt i 1 (by norm_num) ≠ boostPt i (-1) (by norm_num) := by
  intro h
  have := congrArg (fun u : PenroseSphere d => (u : EuclideanSpace ℝ (Fin d)) i) h
  simp [boostPt] at this
  norm_num at this

/-- **`⟨B⟩` is discrete**, `B` the standard boost: `A ↦ (A(1, eᵢ))₀` is continuous and takes the
value `eᵏ` on `Bᵏ`. A non-trivial inhabitant of the `DiscreteTopology` hypotheses of this file. -/
theorem discreteTopology_zpowers_stdBoostL (i : Fin d) :
    DiscreteTopology (Subgroup.zpowers (stdBoostL i)) := by
  set B := stdBoostL i
  set x : Minkowski d := timeUnit d + spaceUnit i
  set l : ℝ := Real.exp 1
  have hl : 1 < l := Real.one_lt_exp_iff.2 one_pos
  have hBx : (B : Minkowski d ≃ₗ[ℝ] Minkowski d) x = l • x := stdBoost_apply_add i 1
  set f : lorentz d → ℝ := fun A => (linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) x).1
  have hf : Continuous f :=
    continuous_fst.comp (continuous_lorentz_linToCLM.clm_apply continuous_const)
  have hx1 : x.1 = 1 := by simp [x, timeUnit, spaceUnit]
  have hval : ∀ k : ℤ, f (B ^ k) = l ^ k := fun k => by
    simp only [f, linToCLM_apply]
    rw [lorentz_zpow_apply_of_eigen B (by positivity) hBx k, Prod.smul_fst, smul_eq_mul, hx1,
      mul_one]
  refine discreteTopology_iff_isOpen_singleton.2 fun g => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine isOpen_induced_iff.2 ⟨f ⁻¹' Set.Ioo (l ^ (k - 1)) (l ^ (k + 1)),
    isOpen_Ioo.preimage hf, ?_⟩
  ext h
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h.2
  rw [← hm, hval]
  constructor
  · rintro ⟨h1, h2⟩
    rw [zpow_lt_zpow_iff_right₀ hl] at h1 h2
    have hmk : m = k := by omega
    exact Subtype.ext (by rw [← hm, ← hk, hmk])
  · rintro rfl
    have hmk : m = k := by
      have he := congrArg f (hm.trans hk.symm)
      rw [hval, hval] at he
      rcases lt_trichotomy m k with h' | h' | h'
      · have := zpow_lt_zpow_right₀ hl h'; linarith
      · exact h'
      · have := zpow_lt_zpow_right₀ hl h'; linarith
    rw [hmk, zpow_lt_zpow_iff_right₀ hl, zpow_lt_zpow_iff_right₀ hl]
    constructor <;> omega

/-- **Witness (not trivially true)** for `LimitSetMinimal`, `d ≥ 1` (Barbot's `n ≥ 2`): for the
discrete group `⟨B⟩` of a boost — which has a global fixed point, `eᵢ ∈ 𝒮` — the closed nonempty
invariant set `{eᵢ}` misses the repulsive fixed point `−eᵢ`. So the hypothesis
`¬HasGlobalFixedPoint G` is load-bearing. -/
theorem not_limitSet_conclusion_stdBoostL (i : Fin d) :
    DiscreteTopology (Subgroup.zpowers (stdBoostL i)) ∧
      HasGlobalFixedPoint (Subgroup.zpowers (stdBoostL i)) ∧
      ∃ F : Set (PenroseSphere d), IsClosed F ∧ F.Nonempty ∧
        IsSphereInvariant (Subgroup.zpowers (stdBoostL i)) F ∧
        ¬repulsiveSet (Subgroup.zpowers (stdBoostL i)) ⊆ F := by
  set B := stdBoostL i
  have hfixP : ∀ A ∈ Subgroup.zpowers B, lorentzSphere A (boostPt i 1 (by norm_num)) =
      boostPt i 1 (by norm_num) := by
    intro A hA
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hA
    refine lorentzSphere_eq_of_eigen (c := Real.exp 1 ^ k) ?_
    rw [nullVec_boostPt_one]
    exact lorentz_zpow_apply_of_eigen B (Real.exp_pos 1).ne' (stdBoost_apply_add i 1) k
  refine ⟨discreteTopology_zpowers_stdBoostL i, Or.inr ⟨_, hfixP⟩,
    {boostPt i 1 (by norm_num)}, isClosed_singleton, Set.singleton_nonempty _, ?_, fun hsub => ?_⟩
  · rintro A hA u rfl; exact hfixP A hA
  · have hrep : boostPt i (-1) (by norm_num) ∈ repulsiveSet (Subgroup.zpowers B) :=
      ⟨B, Subgroup.mem_zpowers B, stdBoost_isLoxodromic i one_ne_zero, Real.exp (-1),
        Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num), by
          rw [nullVec_boostPt_neg_one]; exact stdBoost_apply_sub i 1⟩
    exact boostPt_ne i (hsub hrep).symm

/-! ### 5. Selberg's lemma (DEC-44) -/

/-- `H` is torsion-free: its only element of finite order is `1`. -/
def IsTorsionFreeSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ g ∈ H, IsOfFinOrder g → g = 1

/-- **Selberg's lemma, as an external** (DEC-44, DEC-36): a finitely generated group of linear
automorphisms of a finite-dimensional real vector space has a torsion-free subgroup of finite
index. Not in mathlib at `fabf563a`. Consumed for Theorem A's literal family (a) under
"`π₁` finitely generated" ([10.G], finding F2). Since DEC-115 no longer an external: proved for
every finite-dimensional real `V` as `selbergLemma` (`Flat/SelbergProof`). -/
def SelbergLemma (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] : Prop :=
  ∀ G : Subgroup (V ≃ₗ[ℝ] V), G.FG →
    ∃ H : Subgroup (V ≃ₗ[ℝ] V), H ≤ G ∧ H.relIndex G ≠ 0 ∧ IsTorsionFreeSubgroup H

/-- The image of a finitely generated subgroup is finitely generated. -/
theorem fg_map_of_fg {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} (hH : H.FG)
    (f : G →* G') : (H.map f).FG := by
  classical
  obtain ⟨S, rfl⟩ := hH
  exact ⟨S.image f, by rw [Finset.coe_image, MonoidHom.map_closure]⟩

/-- **The consumer of Selberg's lemma**: a finitely generated `Γ ≤ Isom(𝐌ⁿ)` has a finite-index
subgroup whose linear part is torsion-free. -/
theorem exists_finiteIndex_torsionFree_linOf (hS : SelbergLemma (Minkowski d))
    {Γ : Subgroup (isom d)} (hΓ : Γ.FG) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∀ γ ∈ Γ', IsOfFinOrder (linOf γ) → linOf γ = 1 := by
  set φ : isom d →* (Minkowski d ≃ₗ[ℝ] Minkowski d) := (lorentz d).subtype.comp linearPart
  have hφ : ∀ γ, φ γ = linOf γ := fun γ => (linOf_eq_linearPart γ).symm
  obtain ⟨H, -, hi, htf⟩ := hS (Γ.map φ) (fg_map_of_fg hΓ φ)
  refine ⟨Γ ⊓ H.comap φ, inf_le_left, ?_, fun γ hγ hfin => ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]; exact hi
  · rw [← hφ] at hfin ⊢; exact htf _ hγ.2 hfin

/-- The positive scalars, a subgroup of `GL(ℝ)` of index `2`. -/
noncomputable def posLinEquiv : Subgroup (ℝ ≃ₗ[ℝ] ℝ) :=
  (Units.posSubgroup ℝ).comap LinearEquiv.det

theorem linEquiv_real_apply (g : ℝ ≃ₗ[ℝ] ℝ) (x : ℝ) : g x = x * g 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

theorem det_linEquiv_real (g : ℝ ≃ₗ[ℝ] ℝ) : (LinearEquiv.det g : ℝ) = g 1 := by
  rw [LinearEquiv.coe_det, LinearMap.det_ring]; rfl

theorem posLinEquiv_index_ne_zero : posLinEquiv.index ≠ 0 := by
  have hs : Function.Surjective (LinearEquiv.det : (ℝ ≃ₗ[ℝ] ℝ) →* ℝˣ) := fun u =>
    ⟨LinearEquiv.smulOfUnit u, Units.ext (by
      rw [det_linEquiv_real]; show (u • (1 : ℝ)) = u; rw [Units.smul_def, smul_eq_mul, mul_one])⟩
  rw [posLinEquiv, Subgroup.index_comap_of_surjective _ hs, Units.index_posSubgroup]
  exact two_ne_zero

theorem pow_linEquiv_real_apply (g : ℝ ≃ₗ[ℝ] ℝ) (n : ℕ) : (g ^ n) 1 = g 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, linEquiv_real_apply (g ^ n), ih, pow_succ']

/-- **Witness (not false)**: Selberg's lemma for `V = ℝ`, with `H = G ∩ {positive scalars}`. -/
theorem selbergLemma_real : SelbergLemma ℝ := by
  intro G _
  refine ⟨G ⊓ posLinEquiv, inf_le_left, ?_, fun g hg hfin => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    exact fun h => posLinEquiv_index_ne_zero (Subgroup.index_eq_zero_of_relIndex_eq_zero h)
  · obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    have hpos : 0 < g 1 := by
      have h' : g ∈ posLinEquiv := hg.2
      rw [posLinEquiv, Subgroup.mem_comap, Units.mem_posSubgroup, det_linEquiv_real] at h'
      exact h'
    have h1 : g 1 ^ n = 1 := by rw [← pow_linEquiv_real_apply, hgn]; rfl
    have h2 : g 1 = 1 := (pow_eq_one_iff_of_nonneg hpos.le hn.ne').1 h1
    exact LinearEquiv.ext fun x => by rw [linEquiv_real_apply, h2, mul_one]; rfl

/-- `H = G` will not do in `SelbergLemma`: `{±1} ≤ GL(ℝ)` is finitely generated and not
torsion-free (its conclusion still holds, with `H = ⊥` of index `2`; the witness that the
hypothesis `FG` is load-bearing is `not_selberg_conclusion_torsion`). -/
theorem not_isTorsionFree_neg_one :
    ¬IsTorsionFreeSubgroup (Subgroup.zpowers (LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ)) := fun h => by
  have h1 := h _ (Subgroup.mem_zpowers _) (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos,
    LinearEquiv.ext fun x => by simp [pow_two]⟩)
  have := congrArg (fun g : ℝ ≃ₗ[ℝ] ℝ => g 1) h1
  norm_num at this

/-- **Bridge to mathlib**: mathlib's `IsMulTorsionFree` (the `n`-th power map is injective for
every `n ≠ 0`) implies `IsTorsionFreeSubgroup`. The converse fails for non-abelian groups
(`⟨x, y ∣ x² = y²⟩` is torsion-free with `x² = y²`, `x ≠ y`), and Selberg's notion is the weaker
one, so the local definition is kept. -/
theorem IsTorsionFreeSubgroup.of_isMulTorsionFree {G : Type*} [Group G] {H : Subgroup G}
    (h : IsMulTorsionFree H) : IsTorsionFreeSubgroup H := fun g hg hfin => by
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have : (⟨g, hg⟩ : H) ^ n = 1 ^ n := Subtype.ext (by simpa using hgn)
  exact congrArg Subtype.val (h.pow_left_injective hn.ne' this)

/-- Multiplication by a unit of `ℂ`, as an `ℝ`-linear automorphism of `ℂ ≅ ℝ²`. -/
noncomputable def complexMulLin : ℂˣ →* (ℂ ≃ₗ[ℝ] ℂ) := DistribMulAction.toModuleAut ℝ ℂ

theorem complexMulLin_injective : Function.Injective complexMulLin := fun u v h => by
  have := congrArg (fun g : ℂ ≃ₗ[ℝ] ℂ => g 1) h
  exact Units.ext (by simpa [complexMulLin, Units.smul_def] using this)

/-- **Witness (not trivially true)** for `SelbergLemma`: the hypothesis `FG` is load-bearing. The
group of all rotations of `ℝ² ≅ ℂ` by roots of unity is an infinite torsion group (hence, by
Selberg's lemma itself, not finitely generated); a torsion-free subgroup of it is trivial, and
the trivial subgroup of an infinite group has infinite index. -/
theorem not_selberg_conclusion_torsion :
    ∃ G : Subgroup (ℂ ≃ₗ[ℝ] ℂ),
      ¬∃ H : Subgroup (ℂ ≃ₗ[ℝ] ℂ), H ≤ G ∧ H.relIndex G ≠ 0 ∧ IsTorsionFreeSubgroup H := by
  refine ⟨(CommGroup.torsion ℂˣ).map complexMulLin, fun ⟨H, hle, hi, htf⟩ => ?_⟩
  have hbot : H = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨u, hu, rfl⟩ := hle hg
    exact htf _ hg (complexMulLin.isOfFinOrder hu)
  rw [hbot, Subgroup.relIndex_bot_left] at hi
  have hfin : Finite ((CommGroup.torsion ℂˣ).map complexMulLin) := Nat.finite_of_card_ne_zero hi
  have hfin' : Finite (CommGroup.torsion ℂˣ) :=
    Finite.of_equiv _ ((CommGroup.torsion ℂˣ).equivMapOfInjective _ complexMulLin_injective).symm.toEquiv
  set N := Nat.card (CommGroup.torsion ℂˣ)
  haveI : NeZero (N + 1) := ⟨Nat.succ_ne_zero N⟩
  have hroots : rootsOfUnity (N + 1) ℂ ≤ CommGroup.torsion ℂˣ := fun ζ hζ =>
    isOfFinOrder_iff_pow_eq_one.2 ⟨N + 1, Nat.succ_pos N, (mem_rootsOfUnity _ ζ).1 hζ⟩
  have hcard := Subgroup.card_le_of_le hroots
  rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity] at hcard
  omega

/-! ### 6. Folklore of §9–§11, proved -/

/-- **An isometry commuting with a loxodromic element preserves its fixed points** (l.3295–3297),
on vectors: a linear map commuting with a `minkQ`-preserving `A` preserves each eigenline of `A`
for an eigenvalue `l` with `l² ≠ 1`. -/
theorem eigen_of_commute {A B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
    (hc : B * A = A * B) {l : ℝ} (hl : l * l ≠ 1) {u : Minkowski d} (hu0 : u ≠ 0)
    (hu : A u = l • u) : ∃ c : ℝ, B u = c • u :=
  eigen_line hA hl hu0 hu (w := B u) (by
    rw [← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply, hu, map_smul])

/-- The same on `𝒮`: `B` commuting with `A` fixes every point `u` with `A(1,u) = λ(1,u)`,
`0 < λ ≠ 1` — in particular the two fixed points of a loxodromic `A`. -/
theorem lorentzSphere_fixed_of_commute {A B : lorentz d} (hc : B * A = A * B)
    {u : PenroseSphere d} {l : ℝ} (hl0 : 0 < l) (hl : l ≠ 1)
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = l • nullVec u) :
    lorentzSphere B u = u := by
  have hll : l * l ≠ 1 := fun h => hl (by nlinarith)
  obtain ⟨c, hc'⟩ := eigen_of_commute (fun v => lorentz.minkQ_apply A.2 v)
    (B := (B : Minkowski d ≃ₗ[ℝ] Minkowski d)) (by rw [← Subgroup.coe_mul, hc, Subgroup.coe_mul])
    hll (nullVec_ne_zero u) hu
  exact lorentzSphere_eq_of_eigen hc'

/-- `B` commuting with `A` fixes every repulsive fixed point of `A`. -/
theorem IsRepulsiveFixed.lorentzSphere_of_commute {A B : lorentz d} (hc : B * A = A * B)
    {u : PenroseSphere d} (h : IsRepulsiveFixed A u) : lorentzSphere B u = u :=
  let ⟨_, _, hl, hl1, hu⟩ := h; lorentzSphere_fixed_of_commute hc hl hl1.ne hu

/-- **A nontrivial unipotent element preserves exactly one isotropic direction**: it fixes a
nonzero null `v₀` (in `J = I ∩ I^⊥`), and every null eigenvector is a multiple of `v₀`. -/
theorem unipotent_null_eigen_unique {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) (hn : IsUnipotent A) (h1 : A ≠ 1) :
    ∃ v₀ : Minkowski d, v₀ ≠ 0 ∧ minkQ v₀ = 0 ∧ A v₀ = v₀ ∧
      ∀ (w : Minkowski d) (c : ℝ), minkQ w = 0 → A w = c • w → ∃ c' : ℝ, w = c' • v₀ := by
  obtain ⟨v₀, hmem, hv₀⟩ := exists_mem_nullPart_ne_zero hA hn (pOf_ne_zero h1)
  have hq₀ : minkQ v₀ = 0 := minkQ_eq_zero_of_mem_nullPart hmem
  have hfix : A v₀ = v₀ := by
    have := pOf_eq_zero_of_mem_nullPart hA hmem
    rw [pOf_apply, sub_eq_zero] at this; exact this
  refine ⟨v₀, hv₀, hq₀, hfix, fun w c hw hAw => ?_⟩
  by_cases hw0 : w = 0
  · exact ⟨0, by rw [hw0, zero_smul]⟩
  obtain ⟨m, hm⟩ := hn
  have hc : c = 1 := by
    have := pow_pOf_apply_of_eigen hAw m
    rw [hm, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    rcases this with h | h
    · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h).1
    · exact absurd h hw0
  have hker : w ∈ LinearMap.ker (pOf A) := by
    rw [LinearMap.mem_ker, pOf_apply, hAw, hc, one_smul, sub_self]
  rw [ker_pOf_eq_minkOrth hA] at hker
  exact eq_smul_of_null_orth hq₀ hv₀ hw (hker v₀ hmem.1)

/-- The printed folklore of `bprop:U_timelike` (l.3356–3359): "an abelian subgroup of
`SO₀(1,n−1)` fixes a pair of isotropic directions, except if it consists only of elliptic
elements". -/
def AbelianPairAsPrinted (d : ℕ) : Prop :=
  ∀ G : Subgroup (lorentz d), (∀ A ∈ G, ∀ B ∈ G, A * B = B * A) →
    (∃ u u' : PenroseSphere d, u ≠ u' ∧ ∀ A ∈ G, lorentzSphere A u = u ∧ lorentzSphere A u' = u') ∨
      ∀ A ∈ G, IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)

/-- **The printed folklore of `bprop:U_timelike` is false for `d ≥ 2`** (Barbot's `n ≥ 3`;
DEC-27, finding): the cyclic group of a null rotation is abelian, is not elliptic, and fixes
exactly one point of `𝒮`. The proof of Prop 10.4 survives: it only needs one invariant isotropic
direction, which its hypothesis excludes. -/
theorem not_abelianPairAsPrinted {i j : Fin d} (hij : i ≠ j) : ¬AbelianPairAsPrinted d := by
  intro h
  set N : lorentz d := ⟨stdNullRot hij 1, stdNullRot_mem_lorentz hij 1⟩ with hN
  have hpar : IsParabolic (N : Minkowski d ≃ₗ[ℝ] Minkowski d) := stdNullRot_isParabolic hij one_ne_zero
  have hcomm : ∀ A ∈ Subgroup.zpowers N, ∀ B ∈ Subgroup.zpowers N, A * B = B * A := by
    rintro _ ⟨k, rfl⟩ _ ⟨m, rfl⟩
    exact (Commute.zpow_zpow_self N k m).eq
  rcases h _ hcomm with ⟨u, u', huu', hf⟩ | hell
  · have hN1 : (N : Minkowski d ≃ₗ[ℝ] Minkowski d) ≠ 1 := fun h1 =>
      hpar.not_isElliptic (h1 ▸ isElliptic_one)
    obtain ⟨v₀, -, -, -, huniq⟩ := unipotent_null_eigen_unique
      (fun v => lorentz.minkQ_apply N.2 v) (isUnipotent_nullRot
        (by rw [minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring)
        (minkQ_spaceUnit j)
        (by rw [minkB_add_left, minkB_timeUnit_spaceUnit, minkB_spaceUnit_spaceUnit hij, add_zero])
        1) hN1
    have hev : ∀ x : PenroseSphere d, lorentzSphere N x = x →
        ∃ c : ℝ, (N : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec x) = c • nullVec x := fun x hx =>
      ⟨lorentzScale N x, by
        have := nullVec_lorentzSphere N x
        rw [hx] at this
        calc (N : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec x)
            = lorentzScale N x • ((lorentzScale N x)⁻¹ •
                (N : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec x)) := by
              rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos N x).ne', one_smul]
          _ = lorentzScale N x • nullVec x := by rw [← this]⟩
    obtain ⟨c, hc⟩ := hev u (hf N (Subgroup.mem_zpowers N)).1
    obtain ⟨c', hc'⟩ := hev u' (hf N (Subgroup.mem_zpowers N)).2
    obtain ⟨a, ha⟩ := huniq _ c (minkQ_nullVec u) hc
    obtain ⟨a', ha'⟩ := huniq _ c' (minkQ_nullVec u') hc'
    have ha'0 : a' ≠ 0 := fun h0 => nullVec_ne_zero u' (by rw [ha', h0, zero_smul])
    refine huu' (nullVec_injective_smul (c := a / a') ?_)
    rw [ha, ha', smul_smul, div_mul_cancel₀ _ ha'0]
  · exact hpar.not_isElliptic (hell N (Subgroup.mem_zpowers N))

/-- **The strongest true form, on the members that decide it**: in an abelian (indeed, in any
commuting) situation, an element commuting with a nontrivial unipotent `U` preserves `U`'s
isotropic direction; with a loxodromic, both of its directions (`lorentzSphere_fixed_of_commute`).
The residual cases — a parabolic `R ∘ U` with `R ≠ id`, and the all-elliptic case — rest on the
trichotomy (SCOPE). -/
theorem fixed_null_of_commute_unipotent {U B : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hU : ∀ v, minkQ (U v) = minkQ v) (hn : IsUnipotent U) (h1 : U ≠ 1)
    (hB : ∀ v, minkQ (B v) = minkQ v) (hc : B * U = U * B) :
    ∃ v₀ : Minkowski d, v₀ ≠ 0 ∧ minkQ v₀ = 0 ∧ U v₀ = v₀ ∧ ∃ c : ℝ, B v₀ = c • v₀ := by
  obtain ⟨v₀, hv₀, hq₀, hfix, huniq⟩ := unipotent_null_eigen_unique hU hn h1
  refine ⟨v₀, hv₀, hq₀, hfix, huniq (B v₀) 1 (by rw [hB, hq₀]) ?_⟩
  rw [one_smul, ← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply, hfix]

end Causal.Flat
