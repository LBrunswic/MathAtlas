import GXScaffold.Interaction.PuncturedSphere
import GX.SingularII.Developing

/-!
# Theorem M (N4): momentum conservation at a 2+1 interaction, in holonomy form

Research target `T-3p1-theorem-m` (`papers/bbs/NOTES-3+1.md`, N4, l.316–360). No ledger label;
pseudo-labels below, **none marked** (the master records research results).

* `N4:M1` — `GX.InteractionData.holIn_eq_prod`, `GX.discHol_eq_prod`, `GX.theoremM`: proved,
  holonomy form, for every holonomy `ρ`. The sentence "Lifted to G̃, this defines the total angle"
  is not formalized (SCOPE (d)).
* `N4:M2` — `GX.InteractionData.holOut_eq_prod`, `GX.theoremM`: proved, in the orientation reading
  of SCOPE (c).
* `N4:M3` — holonomy half `GX.InteractionData.holIn_eq_holOut`: proved in the reading of SCOPE (c);
  **false** in the reading where both discs are positively oriented (`GX.m3_printed_fails`), where
  `GX.SphereData.holIn_mul_holOut` (`hol(C₋) hol(C₊) = 1`) holds instead. Real-angle half
  `Θ₋ = Θ₊`: **not stated** (SCOPE (e)).
* `N4:theorem-M` — `GX.theoremM`, `GX.theoremM_developing` (the holonomy of a `(G,X)`-manifold),
  `GX.theoremM_singular` (the regular part of a singular `(G,X)`-surface; e.g. an HS-sphere,
  once `HS²` is a `(G,X)`-model, which it is not yet at this pin: SCOPE (d));
  `GX.discP_small`: `P(pₖ)` is the holonomy of an arbitrarily small loop around `pₖ`.
  `GX.SphereData.sphere_relation`: N3's `∏ Pᵢ = 1`.

> - Σ is a **causally regular** HS-sphere (Thm `tm:thierry` type 1, TeX l.2175).
> - The past hyperbolic region D₋ is a disc carrying the incoming massive particles p₁…p_a.
> - The future disc D₊ carries the outgoing ones, q₁…q_b.
> - A de Sitter annulus A joins the photon circles C₋ = ∂D₋ and C₊ = ∂D₊.
> - In this entry: only elliptic singularities, and A and C_± regular, which is BBS's
>   `surgery-key` setting (l.2950).
> - Write P(x) ∈ PSL(2,ℝ) ≅ SO₀(1,2) for the holonomy of a small positive loop around x.
> (l.321–329)
>
> - **(M1) Incoming total.** hol(C₋) = P(p₁)⋯P(p_a). (l.338)
> […] (l.339–342: the proof sketch and the lift to G̃, quoted in `PuncturedSphere` and SCOPE (d))
> - **(M2) Outgoing total.** hol(C₊) = P(q₁)⋯P(q_b), with total angle Θ₊. The proof is the same.
> (l.343)
> - **(M3) Conservation.** Θ₋ = Θ₊, **as real numbers**, and hol(C₋) = hol(C₊). (l.344)

## Hypothesis checklist

| N4 | here |
|---|---|
| `Σ` a causally regular HS-sphere | ⚠ weakened: any space `M` (`reg Σ`), any singular `(G,X)`-surface in `theoremM_singular`; the decomposition `D₋ ∪ A ∪ D₊` is data |
| `D₋`, `D₊` discs carrying the `pᵢ`, the `qⱼ` | ✓ carried: maps of the model punctured disc (`GX.punctDisc`) |
| `A` an annulus joining `C₋`, `C₊`, `A`, `C±` regular | ✓ carried: a map of the square into `M = reg Σ` |
| only elliptic singularities | ⚠ weakened: not used |
| `P(x)` the holonomy of a small positive loop | ✓ `discP_small` |
| base point on `C₋`, arcs in the cyclic order | ⚠ read (`GXScaffold.Interaction.PuncturedSphere`, SCOPE (a)) |
| `hol` the holonomy | ⚠ weakened: every homomorphism `π₁ → G` (`theoremM`); gx's in `theoremM_developing` |
| (not in N4) | ⚠ read: `theoremM_developing` assumes `LocPathConnectedSpace M` and `SemilocallySimplyConnected M`; `theoremM_singular` assumes `LocallyConnectedSpace X`, `T2Space X`, `LocPathConnectedSpace S` and `SemilocallySimplyConnected (reg S)`. These are the standing hypotheses of gx's developing theorem and of `singular_manifold_holonomy_indeed`; the regular part of a surface and `HS²` satisfy them. `GX.theoremM` assumes none of them |

## SCOPE (disclosed)

* **(a)** The discs and the annulus are continuous maps of the models; the orders and arcs are
  the models' (`PuncturedSphere`, SCOPE (a), (c): `hol(C₋) = P(p₁)⋯P(p_a)` in mathlib's product).
* **(b)** `hol` is any homomorphism `ρ : π₁(M, x₀) → G`; loops at `y₀ ∈ C₊` are transported to
  `x₀` along the annulus (`InteractionData.transport`).
* **(c)** **Orientation: a finding.** N4 does not say how `C₊` and the loops around the `qⱼ` are
  oriented. `InteractionData` runs `C₊` in the direction of the future model's boundary across
  `A`: `C₊` is `C₋` transported across `A`, the boundary of `D₋ ∪ A`. On the oriented sphere this
  makes the future parametrisation orientation-reversing: the `P(qⱼ)` of (M2) are loops negative
  for `Σ`'s orientation. There (M1)–(M3) hold. If both discs are positive (`SphereData`), `A`
  runs `C₊` backwards and `hol(C₋) hol(C₊) = 1` — N3's `∏ Pᵢ = 1` (`sphere_relation`) — so the
  literal (M3) holds iff `hol(C₋)² = 1` (`SphereData.holIn_eq_holOut_iff`) and fails on the
  Riemann-sphere model (`m3_printed_fails`).
* **(d)** The lift to `G̃` and the total angles `Θ±` are not formalized: no universal cover of
  `PSL(2,ℝ)`, no `ℝP¹`-circle, no `HS²` as a `(G,X)` model in any library at this pin.
* **(e)** `Θ₋ = Θ₊` as real numbers (BBS l.3013) is not stated, for the same reason, and needs
  the de Sitter geometry of `A` (the left isotropic foliation of `dS̃²`).
* **(f)** `m3_printed_fails` uses the holonomies `ρ_g = g^{wind}` of `ℂ ∖ {0}`. That the link
  `𝔢(L)` of a point of a massive particle line has a holonomy of this form, `g` a rotation by
  the deficit, is the session's reasoning [r], not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GXScaffold.Interaction.PuncturedSphere`, `GX.Structure.Developing`, `GX.SingularII.Developing`,
`GX.Branched.Paths` (`cWinding`).
-/

noncomputable section

open Set Function unitInterval

namespace GX

set_option linter.unusedSectionVars false

/-! ### The holonomy of a punctured disc -/

section Disc

variable {M : Type*} [TopologicalSpace M] {a : ℕ}

/-- `hol(∂D)` in `π₁(M, φ(base))`, for a closed disc with `a` punctures `φ : D̄ ∖ {pᵢ} → M`
parametrised by the model: the class of `φ ∘ ∂`. -/
def discHol (φ : C(punctDisc a, M)) : FundamentalGroup M (φ (PunctDisc.base a)) :=
  FundamentalGroup.map φ (PunctDisc.base a) (PunctDisc.cls a (PunctDisc.boundary a))

/-- `P(pₖ)` in `π₁(M, φ(base))`: the class of `φ ∘ γₖ`, the `k`-th lasso. -/
def discP (φ : C(punctDisc a, M)) (k : Fin a) : FundamentalGroup M (φ (PunctDisc.base a)) :=
  FundamentalGroup.map φ (PunctDisc.base a) (PunctDisc.cls a (PunctDisc.lasso a k))

/-- **The disc relation** (the proof of (M1), and of (M2): "the proof is the same"):
`hol(∂D) = P(p₁) ⋯ P(p_a)` in `π₁`. -/
theorem discHol_eq_prod (φ : C(punctDisc a, M)) : discHol φ = (List.ofFn (discP φ)).prod := by
  rw [discHol, PunctDisc.cls_boundary, map_list_prod, List.map_ofFn]
  rfl

theorem discHol_eq_fromPath (φ : C(punctDisc a, M)) :
    discHol φ = FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((PunctDisc.boundary a).map φ.continuous)) := rfl

/-- **`P(pₖ)` is the holonomy of a small positive loop around `pₖ`.** For every `0 < r < 1/2`,
`P(pₖ)` is the class of the image of the counterclockwise square `sᵣ` of half-side `r` around the
`k`-th puncture, conjugated by the image of its tether. If `φ` extends to a map `ext` of the
closed disc, continuous at the puncture, then for every neighbourhood `U` of `ext(pₖ)` some such
`r` puts the loop inside `U`: `P(pₖ)` is the holonomy of an arbitrarily small loop around the
`k`-th particle. -/
theorem discP_small {Y : Type*} [TopologicalSpace Y] (φ : C(punctDisc a, M)) (ι : C(M, Y))
    (ext : ℝ × ℝ → Y) (hext : ∀ z : punctDisc a, ι (φ z) = ext z) (k : Fin a)
    (hc : ContinuousAt ext (PunctDisc.puncture a k)) {U : Set Y}
    (hU : U ∈ nhds (ext (PunctDisc.puncture a k))) :
    ∃ (r : ℝ) (hr0 : 0 < r) (hr : r < 1 / 2),
      (∀ t, ι (φ (PunctDisc.smallSq (PunctDisc.geom_lt k) hr0 hr t)) ∈ U) ∧
      discP φ k = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((PunctDisc.smallTether (PunctDisc.geom_lt k) hr0 hr).map φ.continuous).trans
          (((PunctDisc.smallSq (PunctDisc.geom_lt k) hr0 hr).map φ.continuous).trans
            ((PunctDisc.smallTether (PunctDisc.geom_lt k) hr0 hr).map φ.continuous).symm))) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds hU)
  set r : ℝ := min (ε / 2) (1 / 4) with hr_def
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hr : r < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨r, hr0, hr, fun t => ?_, ?_⟩
  · rw [hext]
    exact hball (lt_of_le_of_lt (PunctDisc.dist_smallSq_le k hr0 hr t) hrε)
  · rw [discP, PunctDisc.cls_lasso_eq_small k hr0 hr]
    show FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.map _ φ.continuous)) = _
    rw [Path.map_trans, Path.map_trans, Path.map_symm]

end Disc

/-! ### The topological data of a causally regular interaction -/

/-- **The topological data of a causally regular interaction** (N4, "Setting"), in a space `M`
standing for the regular part of the link `Σ`: the closed past disc `D̄₋` with its `a` incoming
particles removed and the closed future disc `D̄₊` with its `b` outgoing particles removed, both
parametrised by the model `punctDisc` (`GX.PunctDisc`), and the de Sitter annulus `Ā` joining
`C₋ = ∂D₋` to `C₊ = ∂D₊`: a map of the square, periodic in its second variable, whose inner circle
is `C₋` and whose outer circle is `C₊`, **both run in the direction of the models' boundary
loops**. On an oriented sphere `D₋ ∪ A ∪ D₊` this is the convention in which `C₊` is oriented as
`C₋` transported across `A` (as the boundary of `D₋ ∪ A`); `GX.SphereData` is the other one. -/
structure InteractionData (M : Type*) [TopologicalSpace M] (a b : ℕ) where
  /-- `D̄₋ ∖ {p₁,…,p_a}`. -/
  past : C(punctDisc a, M)
  /-- `D̄₊ ∖ {q₁,…,q_b}`. -/
  future : C(punctDisc b, M)
  /-- `Ā`, from `C₋` (`s = 0`) to `C₊` (`s = 1`). -/
  annulus : C(I × I, M)
  annulus_zero : ∀ t, annulus (0, t) = past (PunctDisc.boundary a t)
  annulus_one : ∀ t, annulus (1, t) = future (PunctDisc.boundary b t)
  annulus_periodic : ∀ s, annulus (s, 0) = annulus (s, 1)

namespace InteractionData

variable {M : Type*} [TopologicalSpace M] {a b : ℕ} (D : InteractionData M a b)

/-- The base point, on `C₋`: the image of the model's base point. -/
abbrev x₀ : M := D.past (PunctDisc.base a)

/-- The base point of the future disc, on `C₊`. -/
abbrev y₀ : M := D.future (PunctDisc.base b)

/-- `C₋`, as a loop at `x₀`. -/
def cMinus : Path D.x₀ D.x₀ := (PunctDisc.boundary a).map D.past.continuous

/-- `C₊`, as a loop at `y₀`. -/
def cPlus : Path D.y₀ D.y₀ := (PunctDisc.boundary b).map D.future.continuous

/-- The arc of the annulus from `x₀` to `y₀` (the track `s ↦ Ā(s,0)` of the base point). -/
def tether : Path D.x₀ D.y₀ where
  toFun s := D.annulus (s, 0)
  continuous_toFun := by fun_prop
  source' := by rw [D.annulus_zero, Path.source]
  target' := by rw [D.annulus_one, Path.source]

/-- Transport of loops at `y₀` to loops at `x₀` along the tether: `[β] ↦ [τ · β · τ⁻¹]`. -/
def transport : FundamentalGroup M D.y₀ ≃* FundamentalGroup M D.x₀ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath D.tether).symm

/-- `hol(C₋)` in `π₁(M, x₀)`. -/
def holIn : FundamentalGroup M D.x₀ := discHol D.past

/-- `P(pₖ)` in `π₁(M, x₀)`. -/
def pIn (k : Fin a) : FundamentalGroup M D.x₀ := discP D.past k

/-- `hol(C₊)` in `π₁(M, x₀)`: the class of `C₊`, transported to `x₀` across the annulus. -/
def holOut : FundamentalGroup M D.x₀ := D.transport (discHol D.future)

/-- `P(qⱼ)` in `π₁(M, x₀)`, transported to `x₀` across the annulus. -/
def pOut (j : Fin b) : FundamentalGroup M D.x₀ := D.transport (discP D.future j)

/-- **(M1), in `π₁`.** `[C₋] = P(p₁) ⋯ P(p_a)`. -/
theorem holIn_eq_prod : D.holIn = (List.ofFn D.pIn).prod := discHol_eq_prod D.past

/-- **(M2), in `π₁`.** `[C₊] = P(q₁) ⋯ P(q_b)` (transported to `x₀`). -/
theorem holOut_eq_prod : D.holOut = (List.ofFn D.pOut).prod := by
  rw [holOut, discHol_eq_prod, map_list_prod, List.map_ofFn]
  rfl

theorem transport_fromPath (β : Path D.y₀ D.y₀) :
    D.transport (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (D.tether.trans (β.trans D.tether.symm))) := rfl

/-- **(M3), in `π₁`.** `[C₋] = [τ C₊ τ⁻¹]`: across the annulus, `hol(C₋) = hol(C₊)`. -/
theorem holIn_eq_holOut : D.holIn = D.holOut := by
  rw [holIn, holOut, discHol_eq_fromPath, discHol_eq_fromPath, transport_fromPath]
  congr 1
  exact mk_eq_conj_of_annulus D.annulus D.cMinus D.cPlus D.tether D.annulus_zero D.annulus_one
    (fun _ => rfl) (fun s => (D.annulus_periodic s).symm)

end InteractionData

/-- **Theorem M, holonomy form** (N4 (M1)–(M3) at the level of holonomy): for every
homomorphism `ρ : π₁(M, x₀) → G` — in particular the holonomy of a `(G,X)`-structure on `M`
(`GX.theoremM_developing`, `GX.theoremM_singular`) —
(M1) `ρ(C₋) = ρ(P(p₁)) ⋯ ρ(P(p_a))`, (M2) `ρ(C₊) = ρ(P(q₁)) ⋯ ρ(P(q_b))`, (M3) `ρ(C₋) = ρ(C₊)`,
hence the conservation law `ρ(P(p₁)) ⋯ ρ(P(p_a)) = ρ(P(q₁)) ⋯ ρ(P(q_b))`. -/
theorem theoremM {M : Type*} [TopologicalSpace M] {a b : ℕ} (D : InteractionData M a b)
    {G : Type*} [Group G] (ρ : FundamentalGroup M D.x₀ →* G) :
    ρ D.holIn = (List.ofFn fun k => ρ (D.pIn k)).prod ∧
      ρ D.holOut = (List.ofFn fun j => ρ (D.pOut j)).prod ∧
      ρ D.holIn = ρ D.holOut ∧
      (List.ofFn fun k => ρ (D.pIn k)).prod = (List.ofFn fun j => ρ (D.pOut j)).prod := by
  have h1 : ρ D.holIn = (List.ofFn fun k => ρ (D.pIn k)).prod := by
    rw [D.holIn_eq_prod, map_list_prod, List.map_ofFn]; rfl
  have h2 : ρ D.holOut = (List.ofFn fun j => ρ (D.pOut j)).prod := by
    rw [D.holOut_eq_prod, map_list_prod, List.map_ofFn]; rfl
  have h3 : ρ D.holIn = ρ D.holOut := by rw [D.holIn_eq_holOut]
  exact ⟨h1, h2, h3, h1.symm.trans (h3.trans h2)⟩

/-! ### Theorem M in gx's terms: the holonomy of a `(G,X)`-structure -/

section Developing

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [IsAnalyticAction G X]

/-- **Theorem M for the holonomy of a `(G,X)`-manifold.** Let `M` be a `(G,X)`-manifold (the
regular part of the link), locally path-connected and semilocally simply connected, carrying the
topological data `D` of a causally regular interaction. Then `M` has a developing pair
`(dev, ρ)` (`GX.developing_theorem_fundamentalGroup`), and for its holonomy `ρ`, (M1), (M2),
(M3) and the conservation law hold. (By `GX.developing_unique`, every other developing pair is
`(g • dev, g ρ g⁻¹)`, for which they hold as well: `GX.theoremM` holds for every `ρ`.) -/
theorem theoremM_developing {M : Type*} [TopologicalSpace M] [ChartedSpace X M]
    [HasGroupoid M (gxGroupoid G X)] [LocPathConnectedSpace M] (hM : SemilocallySimplyConnected M)
    {a b : ℕ} (D : InteractionData M a b) :
    letI := coverChartedSpace X hM D.x₀
    ∃ (dev : UniversalCover M D.x₀ → X) (ρ : FundamentalGroup M D.x₀ →* G),
      IsGXMorphism G X dev ∧
      (∀ (γ : FundamentalGroup M D.x₀) (z : UniversalCover M D.x₀),
        dev ((UniversalCover.deckHom γ).1 z) = ρ γ • dev z) ∧
      ρ D.holIn = (List.ofFn fun k => ρ (D.pIn k)).prod ∧
      ρ D.holOut = (List.ofFn fun j => ρ (D.pOut j)).prod ∧
      ρ D.holIn = ρ D.holOut ∧
      (List.ofFn fun k => ρ (D.pIn k)).prod = (List.ofFn fun j => ρ (D.pOut j)).prod := by
  letI := coverChartedSpace X hM D.x₀
  obtain ⟨dev, ρ, hdev, hρ⟩ := developing_theorem_fundamentalGroup (G := G) (X := X) hM D.x₀
  exact ⟨dev, ρ, hdev, hρ, theoremM D ρ⟩

/-- **Theorem M for a singular `(G,X)`-surface** `Σ` (BBS: a singular HS-sphere, `G = SO₀(1,2)`,
`X = HS²`): the data `D` of a causally regular interaction lives in the regular part
`reg Σ = (Sing Σ)ᶜ`, a `(G,X)`-manifold (`GX.regChartedSpace`); for the holonomy `ρ` of any
developing pair of `reg Σ` — the holonomy of `Σ` itself, by
`GX.singular_manifold_holonomy_indeed` — (M1), (M2), (M3) and the conservation law hold. -/
theorem theoremM_singular [LocallyConnectedSpace X] [T2Space X] {S : Type*} [TopologicalSpace S]
    [SingularGXStructure G X S] [LocPathConnectedSpace S]
    (hreg : SemilocallySimplyConnected ((Sing G X S)ᶜ : Set S)) {a b : ℕ}
    (D : InteractionData ((Sing G X S)ᶜ : Set S) a b) :
    letI := regChartedSpace G X S
    letI : LocPathConnectedSpace ((Sing G X S)ᶜ : Set S) :=
      (isClosed_sing G X S).isOpen_compl.locPathConnectedSpace
    letI := coverChartedSpace X hreg D.x₀
    ∃ (dev : UniversalCover ((Sing G X S)ᶜ : Set S) D.x₀ → X)
      (ρ : FundamentalGroup ((Sing G X S)ᶜ : Set S) D.x₀ →* G),
      IsGXMorphism G X dev ∧
      (∀ (γ : FundamentalGroup ((Sing G X S)ᶜ : Set S) D.x₀) z,
        dev ((UniversalCover.deckHom γ).1 z) = ρ γ • dev z) ∧
      ρ D.holIn = (List.ofFn fun k => ρ (D.pIn k)).prod ∧
      ρ D.holOut = (List.ofFn fun j => ρ (D.pOut j)).prod ∧
      ρ D.holIn = ρ D.holOut ∧
      (List.ofFn fun k => ρ (D.pIn k)).prod = (List.ofFn fun j => ρ (D.pOut j)).prod := by
  letI := regChartedSpace G X S
  haveI := hasGroupoid_regChartedSpace (G := G) (X := X) (M := S)
  letI : LocPathConnectedSpace ((Sing G X S)ᶜ : Set S) :=
    (isClosed_sing G X S).isOpen_compl.locPathConnectedSpace
  exact theoremM_developing (G := G) (X := X) hreg D

end Developing

/-! ### The other orientation convention: both discs positively oriented

On an oriented sphere `Σ = D₋ ∪ A ∪ D₊`, parametrise both discs positively. The positive
boundary of `D₊` is then run backwards by the annulus coming from `C₋`: the annulus joins `C₋` to
`C₊⁻¹`. In that convention `hol(C₋) hol(C₊) = 1` — N3's relation `∏ Pᵢ = 1` over all the
particles — and `hol(C₋) = hol(C₊)` fails as soon as `hol(C₋)² ≠ 1` (`GX.m3_printed_fails`). -/

/-- The data of `GX.InteractionData` with the annulus running `C₊` **backwards**: the convention in
which the future disc is positively oriented for the orientation of the sphere, like the past
disc. -/
structure SphereData (M : Type*) [TopologicalSpace M] (a b : ℕ) where
  past : C(punctDisc a, M)
  future : C(punctDisc b, M)
  annulus : C(I × I, M)
  annulus_zero : ∀ t, annulus (0, t) = past (PunctDisc.boundary a t)
  annulus_one : ∀ t, annulus (1, t) = future (PunctDisc.boundary b (σ t))
  annulus_periodic : ∀ s, annulus (s, 0) = annulus (s, 1)

namespace SphereData

variable {M : Type*} [TopologicalSpace M] {a b : ℕ} (D : SphereData M a b)

/-- The base point, on `C₋`. -/
abbrev x₀ : M := D.past (PunctDisc.base a)

/-- The base point of the future disc, on `C₊`. -/
abbrev y₀ : M := D.future (PunctDisc.base b)

/-- The arc of the annulus from `x₀` to `y₀`. -/
def tether : Path D.x₀ D.y₀ where
  toFun s := D.annulus (s, 0)
  continuous_toFun := by fun_prop
  source' := by rw [D.annulus_zero, Path.source]
  target' := by rw [D.annulus_one, unitInterval.symm_zero, Path.target]

/-- Transport of loops at `y₀` to `x₀` along the tether. -/
def transport : FundamentalGroup M D.y₀ ≃* FundamentalGroup M D.x₀ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath D.tether).symm

/-- `hol(C₋)`. -/
def holIn : FundamentalGroup M D.x₀ := discHol D.past

/-- `P(pₖ)`. -/
def pIn (k : Fin a) : FundamentalGroup M D.x₀ := discP D.past k

/-- `hol(C₊)`, `C₊` positively oriented as the boundary of `D₊`, transported to `x₀`. -/
def holOut : FundamentalGroup M D.x₀ := D.transport (discHol D.future)

/-- `P(qⱼ)`, positively oriented in `D₊`, transported to `x₀`. -/
def pOut (j : Fin b) : FundamentalGroup M D.x₀ := D.transport (discP D.future j)

theorem holOut_eq_prod : D.holOut = (List.ofFn D.pOut).prod := by
  rw [holOut, discHol_eq_prod, map_list_prod, List.map_ofFn]
  rfl

/-- **In the positive–positive convention, `hol(C₋) hol(C₊) = 1`.** -/
theorem holIn_mul_holOut : D.holIn * D.holOut = 1 := by
  have key := mk_eq_conj_of_annulus D.annulus ((PunctDisc.boundary a).map D.past.continuous)
    ((PunctDisc.boundary b).map D.future.continuous).symm D.tether D.annulus_zero D.annulus_one
    (fun _ => rfl) (fun s => (D.annulus_periodic s).symm)
  have e1 : D.holIn = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((PunctDisc.boundary a).map D.past.continuous)) := rfl
  have e2 : D.holOut = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (D.tether.trans (((PunctDisc.boundary b).map D.future.continuous).trans D.tether.symm))) :=
    rfl
  rw [e1, e2, key, mul_eq_one_iff_eq_inv]
  show _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _).symm
  rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.trans_symm, Path.symm_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

/-- **N3's sphere relation** `∏ Pᵢ = 1`: in the positive–positive convention,
`P(p₁) ⋯ P(p_a) · P(q₁) ⋯ P(q_b) = 1`. -/
theorem sphere_relation : (List.ofFn D.pIn).prod * (List.ofFn D.pOut).prod = 1 := by
  rw [← D.holOut_eq_prod, show (List.ofFn D.pIn).prod = D.holIn from
    (discHol_eq_prod D.past).symm]
  exact D.holIn_mul_holOut

/-- In the positive–positive convention, (M3) read literally, `hol(C₋) = hol(C₊)`, holds iff
`hol(C₋)² = 1`; likewise for any holonomy `ρ`. -/
theorem holIn_eq_holOut_iff {G : Type*} [Group G] (ρ : FundamentalGroup M D.x₀ →* G) :
    ρ D.holIn = ρ D.holOut ↔ ρ D.holIn * ρ D.holIn = 1 := by
  have h : ρ D.holIn * ρ D.holOut = 1 := by rw [← map_mul, D.holIn_mul_holOut, map_one]
  constructor
  · intro e; rw [← h, e]
  · intro e; exact mul_left_cancel (e.trans h.symm)

end SphereData

/-! ### The literal reading of (M3) fails in the positive–positive convention

A model on the Riemann sphere `ℂ ∪ {∞}` with its complex orientation: the incoming particle at
`0`, the outgoing one at `∞`, `D₋ = {|z| ≤ 1}`, `A = {1 ≤ |z| ≤ 2}`, `D₊ = {|z| ≥ 2} ∪ {∞}`, so
that `reg Σ = ℂ ∖ {0}`. Both boundary circles are positively oriented for their discs — witnessed
by their winding numbers, `+1` around `0` in the chart `z` and `+1` around `∞` in the chart
`w = 1/z` — and the annulus joins `C₋` to `C₊⁻¹`. For every holonomy of the form `ρ_g = g^{wind}`
with `g² ≠ 1`, `ρ_g(C₋) ≠ ρ_g(τ C₊ τ⁻¹)`. -/

section Counterexample

/-- The winding number around `0`, a homomorphism `π₁(ℂ ∖ {0}, z) → ℤ`. -/
def windingHom (z : CStar) : FundamentalGroup CStar z →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Quotient.lift (fun γ : Path z z => cWinding γ)
    (fun _ _ h => cWinding_homotopic h) (FundamentalGroup.toPath g))
  map_one' := by
    show Multiplicative.ofAdd (cWinding (Path.refl z)) = 1
    rw [show cWinding (Path.refl z) = 0 from
      cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log z))
        (fun t => by simp [Complex.exp_log z.2]) (by simp)]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (Quotient.lift _ _ ((FundamentalGroup.toPath b).trans
      (FundamentalGroup.toPath a))) = Multiplicative.ofAdd (Quotient.lift _ _ _) *
        Multiplicative.ofAdd (Quotient.lift _ _ _)
    induction FundamentalGroup.toPath a using Quotient.inductionOn with | h α =>
    induction FundamentalGroup.toPath b using Quotient.inductionOn with | h β =>
    show Multiplicative.ofAdd (cWinding (β.trans α)) =
      Multiplicative.ofAdd (cWinding α) * Multiplicative.ofAdd (cWinding β)
    rw [cWinding_trans, ← ofAdd_add, add_comm]

theorem windingHom_mk {z : CStar} (γ : Path z z) :
    windingHom z (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (cWinding γ) := rfl

/-- The point `1` of `ℂ ∖ {0}`. -/
abbrev rsOne : CStar := ⟨1, one_ne_zero⟩

/-- The point `2` of `ℂ ∖ {0}`. -/
abbrev rsTwo : CStar := ⟨2, two_ne_zero⟩

/-- `C₋ = ∂D₋`: the unit circle, counterclockwise. -/
def rsCMinus : Path rsOne rsOne := cLoop rsOne 1

/-- `C₊ = ∂D₊`: the circle of radius `2`, clockwise in `ℂ`: the positive boundary of
`D₊ = {|z| ≥ 2} ∪ {∞}`. -/
def rsCPlus : Path rsTwo rsTwo := cLoop rsTwo (-1)

theorem rs_ne_zero (s t : ℝ) (hs : 0 ≤ s) :
    ((1 + s : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (by linarith : (1 + s : ℝ) ≠ 0)) (Complex.exp_ne_zero _)

/-- The annulus `A = {1 ≤ |z| ≤ 2}`, `Φ(s,t) = (1+s) e^{2πit}`. -/
def rsAnnulus : C(I × I, CStar) :=
  ⟨fun w => ⟨((1 + (w.1 : ℝ) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (w.2 : ℝ)),
    rs_ne_zero _ _ w.1.2.1⟩, by fun_prop⟩

/-- The tether `s ↦ 1 + s` across the annulus. -/
def rsTether : Path rsOne rsTwo where
  toFun s := ⟨((1 + (s : ℝ) : ℝ) : ℂ), by exact_mod_cast (by linarith [s.2.1] : (1 + (s : ℝ)) ≠ 0)⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by push_cast; norm_num)

/-- The chart `w = 1/z` at `∞`. -/
def rsInv : C(CStar, CStar) :=
  ⟨fun z => ⟨(z : ℂ)⁻¹, inv_ne_zero z.2⟩, (continuous_subtype_val.inv₀ fun z => z.2).subtype_mk _⟩

/-- `C₋` winds once positively around the incoming particle `0`. -/
theorem cWinding_rsCMinus : cWinding rsCMinus = 1 := cWinding_cLoop _ _

/-- `C₊` winds once positively around the outgoing particle `∞`, read in the chart `w = 1/z`. -/
theorem cWinding_rsCPlus_inv : cWinding (rsCPlus.map rsInv.continuous) = 1 := by
  have e : rsCPlus.map rsInv.continuous = cLoop (rsInv rsTwo) 1 := by
    ext t
    show ((2 : ℂ) * Complex.exp (((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((t : ℝ) : ℂ)))⁻¹ =
      (2 : ℂ)⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((t : ℝ) : ℂ))
    rw [mul_inv, ← Complex.exp_neg]
    congr 2
    push_cast; ring
  rw [e, cWinding_cLoop]

theorem rsAnnulus_zero (t : I) : rsAnnulus (0, t) = rsCMinus t := by
  apply Subtype.ext
  show (((1 + ((0 : I) : ℝ) : ℝ) : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) =
    (1 : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((t : ℝ) : ℂ))
  push_cast; ring_nf

theorem rsAnnulus_one (t : I) : rsAnnulus (1, t) = rsCPlus.symm t := by
  apply Subtype.ext
  show (((1 + ((1 : I) : ℝ) : ℝ) : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) =
    (2 : ℂ) * Complex.exp (((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * (((σ t : I) : ℝ) : ℂ))
  have h : Complex.exp (((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * (((σ t : I) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
    rw [unitInterval.coe_symm_eq, show ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
      ((1 - (t : ℝ) : ℝ) : ℂ) = 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) - 2 * Real.pi * Complex.I
      by push_cast; ring, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [h]; push_cast; ring

theorem rsAnnulus_bottom (s : I) : rsAnnulus (s, 0) = rsTether s := by
  apply Subtype.ext
  show (((1 + (s : ℝ) : ℝ) : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * ((((0 : I) : ℝ)) : ℂ)) =
    ((1 + (s : ℝ) : ℝ) : ℂ)
  simp

theorem rsAnnulus_top (s : I) : rsAnnulus (s, 1) = rsTether s := by
  apply Subtype.ext
  show (((1 + (s : ℝ) : ℝ) : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * ((((1 : I) : ℝ)) : ℂ)) =
    ((1 + (s : ℝ) : ℝ) : ℂ)
  simp [Complex.exp_two_pi_mul_I]

/-- In the model, `[C₋] · [τ C₊ τ⁻¹] = 1` in `π₁(ℂ ∖ {0}, 1)`. -/
theorem rs_mul_eq_one :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rsCMinus) *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (rsTether.trans (rsCPlus.trans rsTether.symm))) = 1 := by
  have key := mk_eq_conj_of_annulus rsAnnulus rsCMinus rsCPlus.symm rsTether rsAnnulus_zero
    rsAnnulus_one rsAnnulus_bottom rsAnnulus_top
  rw [key, mul_eq_one_iff_eq_inv]
  show _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _).symm
  rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.trans_symm, Path.symm_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

/-- **The literal (M3) fails when both discs are positively oriented.** On the Riemann sphere,
with the incoming particle at `0`, the outgoing one at `∞`, `C₋` the positive boundary of
`D₋ = {|z| ≤ 1}` (winding `+1` around `0`) and `C₊` the positive boundary of
`D₊ = {|z| ≥ 2} ∪ {∞}` (winding `+1` around `∞` in the chart `1/z`), joined by the annulus
`{1 ≤ |z| ≤ 2}` (`Φ(0,·) = C₋`, `Φ(1,·) = C₊⁻¹`, `Φ(·,0) = Φ(·,1) = τ`): for every group `G`
and `g ∈ G` with `g² ≠ 1`, the holonomy `ρ_g = g^{wind} : π₁(ℂ ∖ {0}) → G` gives
`ρ_g(C₋) = g ≠ g⁻¹ = ρ_g(τ C₊ τ⁻¹)`. -/
theorem m3_printed_fails {G : Type*} [Group G] (g : G) (hg : g * g ≠ 1) :
    cWinding rsCMinus = 1 ∧ cWinding (rsCPlus.map rsInv.continuous) = 1 ∧
      (∀ t, rsAnnulus (0, t) = rsCMinus t) ∧ (∀ t, rsAnnulus (1, t) = rsCPlus.symm t) ∧
      (∀ s, rsAnnulus (s, 0) = rsTether s) ∧ (∀ s, rsAnnulus (s, 1) = rsTether s) ∧
      ((zpowersHom G g).comp (windingHom rsOne)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rsCMinus)) = g ∧
        (zpowersHom G g).comp (windingHom rsOne)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (rsTether.trans (rsCPlus.trans rsTether.symm)))) = g⁻¹) ∧
      (zpowersHom G g).comp (windingHom rsOne)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rsCMinus)) ≠
        (zpowersHom G g).comp (windingHom rsOne)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (rsTether.trans (rsCPlus.trans rsTether.symm)))) := by
  set ρ := (zpowersHom G g).comp (windingHom rsOne)
  have h1 : ρ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rsCMinus)) = g := by
    simp only [ρ, MonoidHom.comp_apply, windingHom_mk, cWinding_rsCMinus, zpowersHom_apply,
      toAdd_ofAdd, zpow_one]
  have h2 : ρ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (rsTether.trans (rsCPlus.trans rsTether.symm)))) = g⁻¹ := by
    have := congrArg ρ rs_mul_eq_one
    rw [map_mul, map_one, h1] at this
    exact (eq_inv_of_mul_eq_one_right this)
  refine ⟨cWinding_rsCMinus, cWinding_rsCPlus_inv, rsAnnulus_zero, rsAnnulus_one,
    rsAnnulus_bottom, rsAnnulus_top, ⟨h1, h2⟩, ?_⟩
  rw [h1, h2]
  intro e
  exact hg (by rw [mul_eq_one_iff_eq_inv]; exact e)

end Counterexample

end GX
