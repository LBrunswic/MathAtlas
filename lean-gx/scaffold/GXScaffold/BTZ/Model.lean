import GXScaffold.Lorentz.Bridge
import GXScaffold.SingularII.SpreadTop

/-!
# `GXScaffold.BTZ.Model` — the BTZ model space `𝔼₀` as a singular `(Isom(𝐌³), 𝐌³)`-manifold

Package WP-41b (WAVE5-PLAN.md, WP-39b). `papers/gx`, §4.4 "Some complements on the BTZ model"
(`RamcovGX.tex:2234–2300`) and the motivational example `sec:mot_BTZ` (l.1942–1958) it relies
on. `𝔼₀` is built by the construction of gx's white hole (`ex:quotient_base`: `quotientBase`, the
quotient `Γ_α\(𝔻_∞ × ℝ)` with the structure developed by gx's `btzDev`), redone over `lean-causal`'s
`Causal.Minkowski 2` and `Causal.Flat.isom 2 = Isom₀(𝔼^{1,2})` through the bridge's linear isometry
`nullToMink` (`GXScaffold.Lorentz.Bridge`, WP-41a); no theorem here identifies it with the strict
library's `NullIsom0` white hole `GX.btz_whitehole_isom0`. Its metric content is proved:
`D^*(−dt² + dx² + dy²) = −2dτdr + dr² + r²dθ²` (`GX.btzPaperDev_pullback`).

* **`prop:BTZ_virt_tame`** — `RamcovGX.tex:2252`: `GX.btz_virt_tame` (every structure making
  `Γ_α\(𝔻_∞ × ℝ)` the BTZ model, every `x₀`, every `⟨v|u⟩ < 0`, every `α ≠ 0`), and for the paper's
  `𝔼₀` itself `GX.btzE0_virt_tame` (`α = 2π`, `x₀ = 0`, `v = (−1,1,0)`, `GX.btzE0Structure`). The
  tamifying topology is `T_BTZ`, `GX.btz_isTamifyingTopology`; the proof's last step is repaired
  (D-6, see SCOPE (a)).

Infrastructure (unlabelled facts of l.2234–2300 and l.1942–1958, nothing else marked):
`𝔼₀ = GX.BTZModel α`, the developing map `GX.btzDevM`, the structure exists and is unique
`GX.btz_existsUnique` (`GX.IsBTZStructure`, `GX.exists_isBTZStructure`, `GX.isBTZStructure_unique`); `Sing(𝔼₀) = {r=0}`
`GX.btz_sing`, `Reg(𝔼₀) = {r>0}` `GX.btz_reg`; `\widetilde{𝔼₀} ≅ 𝔻_∞ × ℝ` over `𝔼₀`
`GX.btz_exists_homeomorph`; `D` injective with `D(\widetilde{𝔼₀}) = J⁺(Δ)` (`lean-causal`'s causal
future of the lightlike line `GX.btzLine`) `GX.btz_dev_injective_range`, `GX.range_btzDevM`,
`GX.mem_jplus_btzLine_iff`; `Γ(\widetilde{𝔼₀}/𝔼₀) ≅ ℤ` `GX.btzDeckEquiv`, `GX.btz_deck_equiv_int`; `Γ` fixes `p⁻¹(Sing)` pointwise `GX.btz_deck_fix_sing`;
every `ρ(γ)`, `γ ≠ 1` (either generator included), is parabolic and fixes `Δ` `GX.btzHolonomy_isParabolic`;
the holonomy `GX.btzHolonomy`, `GX.btz_holonomy`, `GX.btzHolonomy_generator` — `ρ(γ) = GX.btzHol`
fixes `Δ` pointwise `GX.btzHol_smul_of_mem_btzLine` and is parabolic `GX.btzHol_isParabolic`
(`Causal.Flat.IsParabolic` of its linear part, which fixes the null direction of `Δ`); `T_BTZ`
(`GX.hornTop`) is `T_nat ⊓ D^*T_{𝐌³}` `GX.hornTop_eq_inf_induced`, `GX.btzTop_eq`; `D` is
`T_BTZ`-continuous `GX.continuous_btzDevM_hornTop`; `Aut(\widetilde{𝔼₀})` acts `T_BTZ`-continuously
`GX.btz_aut_continuous`, `GX.continuous_hornTop_of_isAEMorphismOf`, hence
`GX.btz_hasAutContinuousTamifying` (the model hypothesis of `theo:local_virt_tame`); the cluster
values of `D` at the axis `GX.btzDev_cluster` (l.1949); the cylinder's regular locus
`GX.support_btzCyl`; the paper's coordinates `GX.btzDevM_paper_coords`; the paper's `D` verbatim `GX.btzPaperDev`
`= btzDevM 0 btzV0 ∘ ((τ,r,θ) ↦ (r,−θ,2τ))` `GX.btzPaperDev_eq_btzDevM`, `GX.btzPaperDev_axis`, and
its pullback metric `GX.btzPaperDev_pullback_minkB`, `GX.btzPaperDev_pullback`.
`GX.btz_dev_injective_range` and `GX.btzTop_eq` hold for **every** homeomorphism
`Φ : \widetilde{𝔼₀} ≃ₜ 𝔻_∞ × ℝ` (no `hΦ` needed); `D` is tied to the developing map of
`\widetilde{𝔼₀}` by `GX.btz_isRegDevelopingOnReg`, which uses `hΦ`.

> We did not quite prove that $\BTZ$ is virtually tame, let us correct this.
> \begin{prop} The $\BTZ$ model space is virtually tame. \end{prop}
> \begin{proof} From the motivational example given in section \ref{sec:mot_BTZ}, the only
> missing property is that the induced quotient topology on $\BTZ$ is indeed the natural one.
> For any $\lambda>0$, the image of $\U_\lambda$ in $\BTZ$ contains
> $\left\{(\tau,\r,\theta)~|~ \r < \frac{\lambda}{4\pi^2} \right\}$ and is thus open. Therefore,
> the quotient topology on $\BTZ$ is the natural topology. \end{proof} (l.2252–2260)
>
> The image of this map is the causal future of a lightlike line $\Delta$ ie
> $\D(\BTZtilde)=J^+(\Delta)$. […] The Galois group $\Gamma:=\Gamma(\BTZtilde/\BTZ)$ is isomorphic
> to $\ZZ$ and stabilizes point-wise the singular locus; taking $\gamma$ a generator […], the
> holonomy $\rho$ sends $\gamma$ to $\phi:=\rho(\gamma)$ which thus stabilizes point-wise […]
> $\Delta$. Since $\Delta$ is lightlike, $\phi$ is parabolic. (l.2249–2250)
>
> Then $\D:(\BTZtilde,\T)\rightarrow \mass{}$ is continuous and element of $\Aut(\BTZtilde)$ are
> $\T$-continuous, furthermore the quotient topology induced on $\BTZ$ is the usual topology.
> Finally, we note that $\reg(\BTZtilde)$ is $\T$-portly. (l.1955–1956)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝔼₀` = `ℝ³` with `−2dτdr + dr² + r²dθ²` (l.1944) | ✓ `Γ_{2π}\(𝔻_∞ × ℝ)` (`≅ ℂ × ℝ`, `GX.cylHomeomorph`) with the structure developed on `{r>0}` by the paper's `D` (`GX.IsBTZStructure`; unique, `GX.btz_existsUnique`), and `D^*(−dt²+dx²+dy²) = −2dτdr + dr² + r²dθ²` **proved** at every point (`GX.btzPaperDev_pullback`, `GX.btzPaperDev_pullback_minkB`; `D` in the paper's coordinates `GX.btzPaperDev_eq_btzDevM`): the charts of the structure are local isometries of the printed metric (printed `r²dθ` read `r²dθ²`) |
| `G = Isom₀(𝔼^{1,2})` (l.668), `X = 𝔼^{1,2}` | ✓ `Causal.Flat.isom 2`, `Causal.Minkowski 2` (bridge: `GX.nullIsom0EquivIsom`, `GX.nullToMink`) |
| `D(τ,r,θ/2π)` (l.2237) | ✓ corrected (D-5): `θ ∈ ℝ`; the printed `D` verbatim is `GX.btzPaperDev = btzDevM 0 btzV0 ∘ ((τ,r,θ) ↦ (r,−θ,2τ))` (`GX.btzPaperDev_eq_btzDevM`; `θ ↦ −θ` conjugates `Γ_α` by `k ↦ k⁻¹`) |
| the paper's `x₀ = 0`, `v`, period `2π` | ⚠ weakened: every `x₀`, every `v` with `⟨v|u⟩ < 0`, every `α ≠ 0`; the paper's instance `GX.btzE0_virt_tame` |
| "virtually tame" (`def:singular_manifold_virtually_tame`) | ✓ `GX.IsVirtuallyTame` of `GXScaffold.SingularII.Models` |
| `T` generated by the natural topology and `U_λ` (l.1953) | ✓ `GX.hornTop = GX.btzGenTop` (SpreadTop), transported by `Φ` |

## SCOPE (disclosed)

* **(a) D-6.** The printed proof's "contains `{r < λ/4π²}` and is thus open" is a non sequitur. The
  repaired step (A): a `Γ`-invariant `T`-open set is open — at an axis point, translate a point of
  a small natural box by the `k ∈ Γ` bringing its angle into `[−α/2, α/2]`
  (`GX.isOpen_of_isOpen_tamTop_of_invariant`, `GX.coinduced_orbitMk_tamTop`, SpreadTop); the
  statement stands, the row is closed.
* **(b)** "the motivational example" (B), (C), (D) are proved here, not assumed: (B) `D` is
  `T`-continuous and a developing map over `p⁻¹(reg)`; (C) `Γ = Γ_α`; (D) `{r>0}` is `T`-portly.
* **(c)** "parabolic" is `lean-causal`'s `IsParabolic` of the linear part (D-1's corrected
  classification); `ρ(γ)` is moreover `≠ 1` (`GX.btzHol_ne_one`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `731ed99`.
-/

namespace GX

open Set Filter Topology Function
open scoped Real

/-! ### The developing map and the holonomy, in Minkowski coordinates -/

section BTZDev

/-- **The developing map of the BTZ model** in `lean-causal`'s Minkowski coordinates: gx's white
hole developing map `btzDev x₀ v` (`P_θ(x₀ + r v + t u)`, null coordinates) followed by the bridge
isometry `nullToMink`. On the axis it is `(apex, t) ↦ x₀ + t u` (the paper's `(τ, 0, ·) ↦ (τ, τ, 0)`). -/
noncomputable def btzDevM (x₀ v : ℝ × ℝ × ℝ) (y : DInfty × ℝ) : Causal.Minkowski 2 :=
  nullToMink (btzDev x₀ v y)

/-- **The holonomy of the BTZ model**: the parabolic `P_α` (fixing `x₀ + ℝu` pointwise) as an
element of `Isom(𝐌³)`. -/
noncomputable def btzHol (x₀ : ℝ × ℝ × ℝ) (α : ℝ) : Causal.Flat.isom 2 :=
  nullIsom0EquivIsom ⟨parabAff x₀ α, parab_mem x₀ α⟩

/-- **The singular line** `Δ = nullToMink (x₀ + ℝ u)`, a lightlike line of `𝐌³`. -/
def btzLine (x₀ : ℝ × ℝ × ℝ) : Set (Causal.Minkowski 2) :=
  range fun s : ℝ => nullToMink (x₀ + s • nullU)

theorem btzDev_apex (x₀ v : ℝ × ℝ × ℝ) (t : ℝ) :
    btzDev x₀ v (DInfty.apex, t) = x₀ + t • nullU := by
  rw [btzDev_eq]; simp

theorem btzDevM_apex (x₀ v : ℝ × ℝ × ℝ) (t : ℝ) :
    btzDevM x₀ v (DInfty.apex, t) = nullToMink (x₀ + t • nullU) := by
  rw [btzDevM, btzDev_apex]

/-- The coordinates of `btzDev`, as functions of `r`, `rθ`, `rθ²` and `t`. -/
theorem btzDev_coords (x₀ v : ℝ × ℝ × ℝ) (y : DInfty × ℝ) :
    btzDev x₀ v y = (x₀.1 + y.1.r * v.1 + 2 * (y.1.r * y.1.θ) * v.2.2 +
        y.1.r * y.1.θ ^ 2 * v.2.1 + y.2, x₀.2.1 + y.1.r * v.2.1,
      x₀.2.2 + y.1.r * v.2.2 + y.1.r * y.1.θ * v.2.1) := by
  rw [btzDev_eq]
  simp only [parab_apply, nullU]
  ext <;> simp <;> ring

theorem isLocalHomeomorphOn_btzDevM (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    IsLocalHomeomorphOn (btzDevM x₀ v) (cylPos ℝ) :=
  nullToMinkHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn.comp
    (isLocalHomeomorphOn_btzDev x₀ hv) (mapsTo_univ _ _)

theorem gammaA_smul_r {α : ℝ} (k : GammaA α) (y : DInfty × ℝ) : (k • y).1.r = y.1.r := by
  rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_r]

/-- `D(k · y) = P_α^k · D(y)` in null coordinates, on the **whole** cylinder (on the axis both sides
are `x₀ + t u`, `P_α` fixing the line). -/
theorem btzDev_smul_all (x₀ v : ℝ × ℝ × ℝ) {α : ℝ} (k : GammaA α) (y : DInfty × ℝ) :
    btzDev x₀ v (k • y) = (parabAff x₀ α ^ k.toInt) • btzDev x₀ v y := by
  rcases y.1.pos_or_eq_apex with hy | hy
  · exact btzDev_smul x₀ v k hy
  · obtain ⟨p, t⟩ := y
    simp only at hy
    subst hy
    have hk : k • ((DInfty.apex, t) : DInfty × ℝ) = (DInfty.apex, t) := by
      rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_apex]
    rw [hk, btzDev_apex, parabAff_zpow, add_sub_cancel_left, map_smul, parab_nullU]

theorem btzHol_zpow_smul (x₀ : ℝ × ℝ × ℝ) (α : ℝ) (n : ℤ) (y : ℝ × ℝ × ℝ) :
    btzHol x₀ α ^ n • nullToMink y = nullToMink ((parabAff x₀ α ^ n) • y) := by
  rw [btzHol, ← map_zpow, ← nullToMink_smul]
  rfl

/-- **Equivariance of the developing map**, on the whole cylinder: `D(k · y) = ρ(k) · D(y)` with
`ρ(k) = btzHol^k`. -/
theorem btzDevM_smul (x₀ v : ℝ × ℝ × ℝ) {α : ℝ} (k : GammaA α) (y : DInfty × ℝ) :
    btzDevM x₀ v (k • y) = btzHol x₀ α ^ k.toInt • btzDevM x₀ v y := by
  rw [btzDevM, btzDevM, btzDev_smul_all, btzHol_zpow_smul]

/-- `Γ_α` acts by a.e. morphisms of the pulled-back structure of the cylinder. -/
theorem isAEMorphismOf_btzCyl_smul (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) {α : ℝ}
    (k : GammaA α) :
    IsAEMorphismOf (Causal.Flat.isom 2)
      (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
      (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
      fun x => k • x :=
  isAEMorphismOf_devStructure (DInfty.isPortly_pos ℝ) (isLocalHomeomorphOn_btzDevM x₀ hv)
    (DInfty.continuous_smul_prod k) (fun x hx => by show 0 < (k • x).1.r; rw [gammaA_smul_r]; exact hx)
    fun _ _ => ⟨btzHol x₀ α ^ k.toInt, Eventually.of_forall fun y => btzDevM_smul x₀ v k y⟩

end BTZDev

/-! ### `𝔼₀` as a singular `(Isom(𝐌³), 𝐌³)`-manifold -/

section Model

/-- **The BTZ model space** `𝔼₀ = Γ_α\(𝔻_∞ × ℝ)` as a type (the paper's `α = 2π`, `BTZE0`); the
same type as `GX.MassCyl α`, with a different structure. -/
abbrev BTZModel (α : ℝ) : Type := Orbits (GammaA α) (DInfty × ℝ)

/-- **The BTZ structure exists and is unique** (`ex:quotient_base`'s white hole transported by the
bridge): `𝔼₀` carries a unique maximal a.e. `(Isom(𝐌³), 𝐌³)`-atlas for which the projection
from the cylinder (with the structure pulled back by `btzDevM`) is an a.e. morphism. -/
theorem btz_existsUnique (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) {α : ℝ} (hα : α ≠ 0) :
    ∃! B : Set (OpenPartialHomeomorph (BTZModel α) (Causal.Minkowski 2)),
      IsMaximalAEAtlas (Causal.Flat.isom 2) B ∧ IsAEMorphismOf (Causal.Flat.isom 2)
        (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
        B (orbitMk (GammaA α)) :=
  quotientBase hα (isLocalHomeomorphOn_btzDevM x₀ hv) (isAEMorphismOf_btzCyl_smul x₀ hv)

variable {x₀ v : ℝ × ℝ × ℝ} {α : ℝ}

/-- The structure of `BTZModel α` is the BTZ one: the projection is an a.e. morphism from the
structure `btzDevM x₀ v` pulls back on `{r > 0}`. -/
def IsBTZStructure (x₀ v : ℝ × ℝ × ℝ) (α : ℝ)
    [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)] : Prop :=
  IsAEMorphismOf (Causal.Flat.isom 2)
    (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) (orbitMk (GammaA α))

theorem exists_isBTZStructure (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) (hα : α ≠ 0) :
    ∃ s : SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α),
      @IsBTZStructure x₀ v α s := by
  obtain ⟨B, ⟨hB, hπ⟩, -⟩ := btz_existsUnique x₀ hv hα
  exact ⟨⟨B, hB⟩, hπ⟩


/-- **The BTZ structure is unique**: two singular structures on `𝔼₀` making it the BTZ model
coincide. -/
theorem isBTZStructure_unique (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) (hα : α ≠ 0)
    (s s' : SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))
    (h : @IsBTZStructure x₀ v α s) (h' : @IsBTZStructure x₀ v α s') : s = s' := by
  obtain ⟨B, hB⟩ := s
  obtain ⟨B', hB'⟩ := s'
  obtain ⟨B₀, -, huniq⟩ := btz_existsUnique x₀ hv hα
  have e1 := huniq B ⟨hB, h⟩
  have e2 := huniq B' ⟨hB', h'⟩
  subst e1; subst e2
  rfl

/-- The deck generator moves every value of `btzDevM` on `{r > 0}`. -/
theorem btzDevM_ofInt_one_smul_ne (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    (hα : α ≠ 0) {y : DInfty × ℝ} (hy : y ∈ cylPos ℝ) :
    btzDevM x₀ v ((GammaA.ofInt 1 : GammaA α) • y) ≠ btzDevM x₀ v y := fun h =>
  btzDev_ofInt_one_smul_ne x₀ hv hα hy (nullToMink.injective h)

theorem btz_instances (hα : α ≠ 0) :
    T2Space (BTZModel α) ∧ LocPathConnectedSpace (BTZModel α) ∧ FirstCountableTopology (BTZModel α) ∧
      ConnectedSpace (BTZModel α) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := cyl_instances (V := ℝ) hα
  exact ⟨h1, h2, h3, h4⟩

section Instances

variable [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]

/-- **`Sing(𝔼₀) = {r = 0}`**: the singular locus of the BTZ model is the whole axis. -/
theorem btz_sing (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) =
      orbitMk (GammaA α) '' {x : DInfty × ℝ | x.1 = DInfty.apex} := by
  have hD := isLocalHomeomorphOn_btzDevM x₀ hv
  have hB := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)
  refine Subset.antisymm ?_ ?_
  · rw [← setOf_r_eq_zero_cyl]; exact quotientBase_sing_subset hα hD hB hπ
  · rintro _ ⟨⟨p, z⟩, hx, rfl⟩
    simp only [mem_setOf_eq] at hx
    subst hx
    exact apex_notMem_support_of_smul_ne hD hB hπ
      (fun y hy => btzDevM_ofInt_one_smul_ne x₀ hv hα hy) z

/-- **`Reg(𝔼₀) = {r > 0}`**. -/
theorem btz_reg (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) = orbitMk (GammaA α) '' cylPos ℝ := by
  rw [← compl_image_axis (V := ℝ) α, ← btz_sing hv hα hπ, Sing, compl_compl]

theorem btz_slsc (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    SemilocallySimplyConnected
      ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α)) := by
  rw [btz_sing hv hα hπ]
  exact (previous_examples_maxBranched.{0} (V := ℝ) hα).2.1

/-- **`\widetilde{𝔼₀}` is the cylinder `𝔻_∞ × ℝ`**, over `𝔼₀`, for every base point. -/
theorem btz_exists_homeomorph (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α)
    (y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α))) :
    ∃ Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) y₀ ≃ₜ
      DInfty × ℝ, ∀ e, orbitMk (GammaA α) (Φ e) = e.base := by
  have key : ∀ (S' : Set (BTZModel α))
      (_ : S' = orbitMk (GammaA α) '' {x : DInfty × ℝ | x.1 = DInfty.apex}) (y₀ : (S'ᶜ : Set _)),
      ∃ Φ : MaxBranchedCover S' y₀ ≃ₜ DInfty × ℝ, ∀ e, orbitMk (GammaA α) (Φ e) = e.base := by
    rintro S' rfl y₀
    exact (previous_examples_maxBranched.{0} (V := ℝ) hα).2.2.2 y₀
  exact key _ (btz_sing hv hα hπ) y₀

/-- Near a point of `{r > 0}`, a chart of `𝔼₀` read through the projection is a translate of the
developing map. -/
theorem btz_eventually_chart (hv : 0 < v.2.1) (hπ : IsBTZStructure x₀ v α) {y : DInfty × ℝ}
    (hy : y ∈ cylPos ℝ) {c : OpenPartialHomeomorph (BTZModel α) (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))
    (hyc : orbitMk (GammaA α) y ∈ c.source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ y' in 𝓝 y, btzDevM x₀ v y' = g • c (orbitMk (GammaA α) y') := by
  have hP := DInfty.isPortly_pos ℝ
  have hD := isLocalHomeomorphOn_btzDevM x₀ hv
  have hB := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)
  have hdev := isAEAtlas_devAtlas (G := Causal.Flat.isom 2) hP hD
  have hreg := hπ.regLocusOf_eq hdev.maximalAEAtlas hB.1
  have hyR : y ∈ regLocusOf (Causal.Flat.isom 2)
      (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) (orbitMk (GammaA α)) := by
    rw [hreg]
    exact ⟨subset_support_devStructure hP hD hy, mem_support.2 ⟨c, hc, hyc⟩⟩
  have hys : y ∈ support (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)) := by
    rw [support_devAtlas hP.isOpen hD]; exact hy
  obtain ⟨e, he, hye⟩ := mem_support.1 hys
  obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := Causal.Flat.isom 2) _ _ _).exists_smul_eq y hyR e
    (hdev.subset_maximalAEAtlas he) c hc hye hyc
  obtain ⟨h, hh⟩ := he.2 y hye
  refine ⟨h * g⁻¹, ?_⟩
  filter_upwards [hg, hh] with y' h1 h2
  rw [h2, h1, mul_smul, inv_smul_smul]

end Instances

end Model

/-! ### The developing map: injective, image `J⁺(Δ)` -/

section Image

/-- **`D` is injective** on the whole cylinder (`⟨v | u⟩ < 0`). -/
theorem btzDev_injective (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    Injective (btzDev x₀ v) := by
  intro y y' h
  rw [btzDev_coords, btzDev_coords] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨ha, hb, hx⟩ := h
  have hr : y.1.r = y'.1.r := mul_right_cancel₀ hv.ne' (add_left_cancel hb)
  rcases y.1.pos_or_eq_apex with h0 | h0
  · have hr' : 0 < y'.1.r := hr ▸ h0
    have hθ : y.1.θ = y'.1.θ := by
      rw [hr] at hx
      have h1 : y'.1.r * y.1.θ * v.2.1 = y'.1.r * y'.1.θ * v.2.1 := by linarith
      exact mul_left_cancel₀ hr'.ne' (mul_right_cancel₀ hv.ne' h1)
    have ht : y.2 = y'.2 := by rw [hr, hθ] at ha; linarith
    exact Prod.ext (DInfty.ext hr hθ) ht
  · have h0' : y'.1 = DInfty.apex := DInfty.eq_apex_of_not_pos (by rw [← hr, h0]; simp)
    rw [h0, h0'] at ha
    simp only [DInfty.apex_r, DInfty.apex_θ, zero_mul, mul_zero, add_zero] at ha
    exact Prod.ext (h0.trans h0'.symm) (add_left_cancel ha)

/-- **`D` is injective** (Minkowski coordinates). -/
theorem btzDevM_injective (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    Injective (btzDevM x₀ v) :=
  nullToMink.injective.comp (btzDev_injective x₀ hv)

/-- The image of `btzDev`: the open half-space `{b > b(x₀)}` and the line `x₀ + ℝu`. -/
theorem range_btzDev (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    range (btzDev x₀ v) = {y | 0 < (y - x₀).2.1} ∪ {y | ∃ s : ℝ, y = x₀ + s • nullU} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rcases z.1.pos_or_eq_apex with h0 | h0
    · left
      show 0 < (btzDev x₀ v z - x₀).2.1
      rw [btzDev_coords]
      simp only [Prod.snd_sub, Prod.fst_sub, add_sub_cancel_left]
      exact mul_pos h0 hv
    · right
      obtain ⟨p, t⟩ := z
      simp only at h0
      subst h0
      exact ⟨t, btzDev_apex x₀ v t⟩
  · rintro (hb | ⟨s, rfl⟩)
    · set w := (btzCoord hv).symm ⟨y - x₀, hb⟩
      have hw : Real.exp w.1.re • parab w.1.im v + w.2 • nullU = y - x₀ :=
        congrArg Subtype.val ((btzCoord hv).apply_symm_apply ⟨y - x₀, hb⟩)
      refine ⟨(DInfty.posEmb ⟨(Real.exp w.1.re, w.1.im), Real.exp_pos _⟩, w.2), ?_⟩
      rw [btzDev_eq]
      simp only [DInfty.posEmb_r, DInfty.posEmb_θ]
      rw [hw, add_sub_cancel]
    · exact ⟨(DInfty.apex, s), btzDev_apex x₀ v s⟩

theorem btz_exists_jplus_aux (a b x : ℝ) :
    (∃ s : ℝ, 0 ≤ a - s + b ∧ x ^ 2 - (a - s) * b ≤ 0) ↔ 0 < b ∨ (b = 0 ∧ x = 0) := by
  constructor
  · rintro ⟨s, h1, h2⟩
    by_contra hc
    simp only [not_or, not_lt, not_and] at hc
    rcases lt_or_eq_of_le hc.1 with hb | hb
    · nlinarith [sq_nonneg x]
    · subst hb
      exact hc.2 rfl (by nlinarith [sq_nonneg x])
  · rintro (hb | ⟨rfl, rfl⟩)
    · refine ⟨a - x ^ 2 / b, ?_, ?_⟩
      · have : 0 ≤ x ^ 2 / b := div_nonneg (sq_nonneg x) hb.le
        linarith
      · rw [sub_sub_cancel, div_mul_cancel₀ _ hb.ne', sub_self]
    · exact ⟨a, by simp, by simp⟩

/-- **The causal future of the lightlike line `Δ`** (`lean-causal`'s causality of `𝐌³`): the line
together with the open half-space above the null plane `u^⊥` through `x₀` (`RamcovGX.tex:2249`). -/
theorem mem_jplus_btzLine_iff (x₀ y : ℝ × ℝ × ℝ) :
    nullToMink y ∈ (Causal.minkowski 2).Jplus ⊤ (btzLine x₀) ↔
      0 < (y - x₀).2.1 ∨ ∃ s : ℝ, y = x₀ + s • nullU := by
  have hline : (∃ s : ℝ, y = x₀ + s • nullU) ↔ (y - x₀).2.1 = 0 ∧ (y - x₀).2.2 = 0 := by
    constructor
    · rintro ⟨s, rfl⟩; simp [nullU]
    · rintro ⟨h1, h2⟩
      simp only [Prod.snd_sub, Prod.fst_sub] at h1 h2
      refine ⟨(y - x₀).1, ?_⟩
      rw [← sub_eq_iff_eq_add']
      ext <;> simp [nullU] <;> linarith
  rw [hline, ← btz_exists_jplus_aux (y - x₀).1]
  simp only [Causal.Precausality.Jplus, btzLine, mem_setOf_eq, exists_range_iff,
    Causal.Flat.le_top_iff_minkQ, ← map_sub, Causal.Flat.IsFutureCausal, fst_nullToMink,
    minkQ_nullToMink, nullτ_apply, nullQ]
  refine exists_congr fun s => ?_
  have e1 : (y - (x₀ + s • nullU)).1 = (y - x₀).1 - s := by simp [nullU]; ring
  have e2 : (y - (x₀ + s • nullU)).2.1 = (y - x₀).2.1 := by simp [nullU]
  have e3 : (y - (x₀ + s • nullU)).2.2 = (y - x₀).2.2 := by simp [nullU]
  rw [e1, e2, e3]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **`D(\widetilde{𝔼₀}) = J⁺(Δ)`** (`RamcovGX.tex:2249`), on the cylinder. -/
theorem range_btzDevM (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    range (btzDevM x₀ v) = (Causal.minkowski 2).Jplus ⊤ (btzLine x₀) := by
  ext q
  obtain ⟨y, rfl⟩ := nullToMink.surjective q
  rw [mem_jplus_btzLine_iff]
  constructor
  · rintro ⟨z, hz⟩
    have : btzDev x₀ v z = y := nullToMink.injective hz
    have hmem : y ∈ range (btzDev x₀ v) := ⟨z, this⟩
    rw [range_btzDev x₀ hv] at hmem
    exact hmem
  · intro h
    have hmem : y ∈ range (btzDev x₀ v) := by rw [range_btzDev x₀ hv]; exact h
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, by rw [btzDevM, hz]⟩

end Image

/-! ### The cylinder's structure: its regular locus is `{r > 0}` -/

section CylSupport

/-- **The regular locus of the cylinder's structure is `{r > 0}`**: no chart of the maximal atlas
contains an axis point (a chart there would be, on a connected punctured neighbourhood, a translate
of `D`, which is unbounded along the paper's sequence `(t, 1/n, n)` of `ex:WTame`). -/
theorem support_btzCyl (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    support (maximalAEAtlas (Causal.Flat.isom 2)
      (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ))) = cylPos ℝ := by
  have hP := DInfty.isPortly_pos ℝ
  have hD := isLocalHomeomorphOn_btzDevM x₀ hv
  have hdev := isAEAtlas_devAtlas (G := Causal.Flat.isom 2) hP hD
  refine Subset.antisymm (fun x hx => ?_) (subset_support_devStructure hP hD)
  by_contra hr
  obtain ⟨p, t⟩ := x
  have hp : p = DInfty.apex := DInfty.eq_apex_of_not_pos hr
  subst hp
  obtain ⟨e, he, hxe⟩ := mem_support.1 hx
  have hO : e.source ∈ 𝓝 (DInfty.apex, t) := e.open_source.mem_nhds hxe
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 hO
  obtain ⟨ε, hε, hεu⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 hu
  obtain ⟨δ, hδ, hδw⟩ := Metric.mem_nhds_iff.1 hw
  set S : Set (DInfty × ℝ) := {p : DInfty | 0 < p.r ∧ p.r < ε} ×ˢ Metric.ball t δ
  have hSc : IsPreconnected S :=
    (DInfty.isPreconnected_pos_r_lt ε).prod (convex_ball t δ).isPreconnected
  have hSP : S ⊆ cylPos ℝ := fun y hy => hy.1.1
  have hSe : S ⊆ e.source := fun y hy => huw ⟨hεu hy.1.2, hδw hy.2⟩
  have hloc : ∀ y ∈ S, ∃ g : Causal.Flat.isom 2, ∀ᶠ y' in 𝓝 y, e y' = g • btzDevM x₀ v y' := by
    intro y hy
    have hys : y ∈ support (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)) := by
      rw [support_devAtlas hP.isOpen hD]; exact hSP hy
    obtain ⟨d, hd, hyd⟩ := mem_support.1 hys
    obtain ⟨a, ha⟩ := hdev.maximalAEAtlas.1.eventually_smul_eq (hdev.subset_maximalAEAtlas hd) he
      hyd (hSe hy)
    obtain ⟨h, hh⟩ := hd.2 y hyd
    refine ⟨a * h⁻¹, ?_⟩
    filter_upwards [ha, hh] with y' h1 h2
    rw [h1, h2, mul_smul, inv_smul_smul]
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn hP.isOpen hD hSc hSP hloc
  have hev : ∀ᶠ n in atTop, wtameSeq t n ∈ S := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn
    exact ⟨⟨show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity, hn⟩, Metric.mem_ball_self hδ⟩
  have hlim : Tendsto (fun n => nullToMink.symm (g⁻¹ • e (wtameSeq t n))) atTop
      (𝓝 (nullToMink.symm (g⁻¹ • e (DInfty.apex, t)))) := by
    have h1 := ((e.continuousAt hxe).tendsto).comp (tendsto_wtameSeq t)
    have h2 := (((continuous_const_smul (g⁻¹ : Causal.Flat.isom 2) :
      Continuous fun q : Causal.Minkowski 2 => g⁻¹ • q)).tendsto _).comp h1
    exact (nullToMinkHomeomorph.symm.continuous.tendsto _).comp h2
  have heq : (fun n => nullToMink.symm (g⁻¹ • e (wtameSeq t n))) =ᶠ[atTop]
      fun n => btzDev x₀ v (wtameSeq t n) := by
    filter_upwards [hev] with n hn
    rw [hg _ hn, inv_smul_smul, btzDevM, LinearEquiv.symm_apply_apply]
  exact not_tendsto_atTop_of_tendsto_nhds (hlim.congr' heq).norm
    (tendsto_norm_btzDev_wtameSeq x₀ hv t)

end CylSupport

/-! ### The BTZ topology `T_BTZ` on the cylinder: `D` is continuous -/

section CylTop

/-- The four functions `(r, rθ, rθ², t)` of the cylinder through which `btzDev` factors. -/
def btzCylCoords (y : DInfty × ℝ) : ℝ × ℝ × ℝ × ℝ := (y.1.r, y.1.r * y.1.θ, hornFn y, y.2)

/-- The affine map through which `btzDev` factors. -/
def btzAff (x₀ v : ℝ × ℝ × ℝ) (c : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x₀.1 + c.1 * v.1 + 2 * c.2.1 * v.2.2 + c.2.2.1 * v.2.1 + c.2.2.2, x₀.2.1 + c.1 * v.2.1,
    x₀.2.2 + c.1 * v.2.2 + c.2.1 * v.2.1)

theorem continuous_btzAff (x₀ v : ℝ × ℝ × ℝ) : Continuous (btzAff x₀ v) := by
  unfold btzAff; fun_prop

theorem btzDev_eq_btzAff (x₀ v : ℝ × ℝ × ℝ) (y : DInfty × ℝ) :
    btzDev x₀ v y = btzAff x₀ v (btzCylCoords y) := by
  rw [btzDev_coords]; rfl

theorem btz_abs_r_mul_θ_le (p : DInfty) : |p.r * p.θ| ≤ p.r * (1 + p.θ ^ 2) := by
  rw [abs_mul, abs_of_nonneg p.r_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ p.r_nonneg
  nlinarith [sq_nonneg (|p.θ| - 1), sq_abs p.θ, abs_nonneg p.θ]

/-- At an axis point, `(r, rθ, rθ², t) → (0, 0, 0, t)` for the BTZ topology. -/
theorem tendsto_btzCylCoords_hornTop (t : ℝ) :
    Tendsto btzCylCoords (@nhds _ hornTop (DInfty.apex, t)) (𝓝 (0, 0, 0, t)) := by
  have hb := hasBasis_nhds_hornTop_apex t
  have key : ∀ f : DInfty × ℝ → ℝ, ∀ c : ℝ, (∀ y, |f y - c| ≤ max (y.1.r * (1 + y.1.θ ^ 2))
      |y.2 - t|) → Tendsto f (@nhds _ hornTop (DInfty.apex, t)) (𝓝 c) := by
    intro f c hf
    refine hb.tendsto_iff Metric.nhds_basis_ball |>.2 fun ε hε => ⟨ε, hε, fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_le_of_lt (hf y) (max_lt hy.1 hy.2)
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_))
  · refine key _ 0 fun y => le_max_of_le_left ?_
    rw [sub_zero, abs_of_nonneg y.1.r_nonneg]
    nlinarith [y.1.r_nonneg, sq_nonneg y.1.θ]
  · exact key _ 0 fun y => le_max_of_le_left (by rw [sub_zero]; exact btz_abs_r_mul_θ_le y.1)
  · refine key _ 0 fun y => le_max_of_le_left ?_
    rw [sub_zero, abs_of_nonneg (hornFn_nonneg y), hornFn]
    nlinarith [y.1.r_nonneg, sq_nonneg y.1.θ]
  · exact key _ t fun y => le_max_right _ _

/-- **`D` is `T_BTZ`-continuous** on the cylinder (`sec:mot_BTZ`, `RamcovGX.tex:1955`; in null
coordinates). -/
theorem continuous_btzDev_hornTop (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    Continuous[hornTop, inferInstance] (btzDev x₀ v) := by
  refine (@continuous_iff_continuousAt _ _ hornTop _ _).2 fun y => ?_
  show Tendsto _ (@nhds _ hornTop y) _
  rcases y.1.pos_or_eq_apex with hr | hr
  · rw [nhds_hornTop_of_pos hr]
    exact ((isLocalHomeomorphOn_btzDev x₀ hv).continuousOn.continuousAt
      ((DInfty.isOpen_pos.preimage continuous_fst).mem_nhds hr))
  · obtain ⟨p, t⟩ := y
    simp only at hr
    subst hr
    have h := ((continuous_btzAff x₀ v).tendsto _).comp (tendsto_btzCylCoords_hornTop t)
    have he : btzDev x₀ v = btzAff x₀ v ∘ btzCylCoords := funext (btzDev_eq_btzAff x₀ v)
    rw [he]
    convert h using 2
    simp [btzCylCoords, hornFn]

/-- **`D` is `T_BTZ`-continuous** (Minkowski coordinates). -/
theorem continuous_btzDevM_hornTop (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    Continuous[hornTop, inferInstance] (btzDevM x₀ v) :=
  @Continuous.comp _ _ _ hornTop _ _ _ _ nullToMinkHomeomorph.continuous
    (continuous_btzDev_hornTop x₀ hv)

theorem tendsto_r_apex_cyl (t : ℝ) :
    Tendsto (fun y : DInfty × ℝ => y.1.r) (𝓝 (DInfty.apex, t)) (𝓝 0) := by
  refine (hasBasis_nhds_apex_prod t).tendsto_iff Metric.nhds_basis_ball |>.2 fun ε hε =>
    ⟨ε, hε, fun y hy => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg y.1.r_nonneg]
  exact hy.1

/-- `rθ` and `rθ²` read off `btzDev` (`v.2.1 ≠ 0`). -/
theorem btz_r_mul_θ_eq (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) (y : DInfty × ℝ) :
    y.1.r * y.1.θ = ((btzDev x₀ v y).2.2 - x₀.2.2 - y.1.r * v.2.2) / v.2.1 := by
  rw [btzDev_coords]; field_simp; ring

theorem btz_hornFn_eq (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) (y : DInfty × ℝ) :
    hornFn y = ((btzDev x₀ v y).1 - x₀.1 - y.1.r * v.1 -
      2 * (((btzDev x₀ v y).2.2 - x₀.2.2 - y.1.r * v.2.2) / v.2.1) * v.2.2 - y.2) / v.2.1 := by
  rw [← btz_r_mul_θ_eq x₀ hv, btzDev_coords, hornFn]; field_simp; ring

/-- Along any filter converging naturally to an axis point `(apex, t)` on which `btzDev` converges
to `w`: `rθ → c` and `rθ² → L`, with the explicit limits. -/
theorem btz_tendsto_r_mul_θ_of (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    {F : Filter (DInfty × ℝ)} {t : ℝ} (hF : F ≤ 𝓝 (DInfty.apex, t)) {w : ℝ × ℝ × ℝ}
    (hw : Tendsto (btzDev x₀ v) F (𝓝 w)) :
    Tendsto (fun y : DInfty × ℝ => y.1.r * y.1.θ) F (𝓝 ((w.2.2 - x₀.2.2) / v.2.1)) ∧
    Tendsto hornFn F
      (𝓝 ((w.1 - x₀.1 - 2 * ((w.2.2 - x₀.2.2) / v.2.1) * v.2.2 - t) / v.2.1)) ∧
    Tendsto (fun y : DInfty × ℝ => y.1.r) F (𝓝 0) ∧ Tendsto (fun y : DInfty × ℝ => y.2) F (𝓝 t) := by
  have hr : Tendsto (fun y : DInfty × ℝ => y.1.r) F (𝓝 0) := (tendsto_r_apex_cyl t).mono_left hF
  have ht : Tendsto (fun y : DInfty × ℝ => y.2) F (𝓝 t) :=
    (continuous_snd.tendsto (DInfty.apex, t)).mono_left hF
  have h1 : Tendsto (fun y => (btzDev x₀ v y).1) F (𝓝 w.1) := (continuous_fst.tendsto _).comp hw
  have h3 : Tendsto (fun y => (btzDev x₀ v y).2.2) F (𝓝 w.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hw
  have hm : Tendsto (fun y : DInfty × ℝ => ((btzDev x₀ v y).2.2 - x₀.2.2 - y.1.r * v.2.2) / v.2.1)
      F (𝓝 ((w.2.2 - x₀.2.2 - 0 * v.2.2) / v.2.1)) :=
    ((h3.sub tendsto_const_nhds).sub (hr.mul tendsto_const_nhds)).div_const _
  rw [zero_mul, sub_zero] at hm
  refine ⟨hm.congr fun y => (btz_r_mul_θ_eq x₀ hv y).symm, ?_, hr, ht⟩
  have hh : Tendsto (fun y : DInfty × ℝ => ((btzDev x₀ v y).1 - x₀.1 - y.1.r * v.1 -
      2 * (((btzDev x₀ v y).2.2 - x₀.2.2 - y.1.r * v.2.2) / v.2.1) * v.2.2 - y.2) / v.2.1) F
      (𝓝 ((w.1 - x₀.1 - 0 * v.1 - 2 * ((w.2.2 - x₀.2.2) / v.2.1) * v.2.2 - t) / v.2.1)) :=
    ((((h1.sub tendsto_const_nhds).sub (hr.mul tendsto_const_nhds)).sub
      ((tendsto_const_nhds.mul hm).mul tendsto_const_nhds)).sub ht).div_const v.2.1
  rw [zero_mul, sub_zero] at hh
  exact hh.congr fun y => (btz_hornFn_eq x₀ hv y).symm

/-- **The cluster values of `D` at the axis** (`sec:mot_BTZ`, `RamcovGX.tex:1949`: the
intersection of the `\overline{D(reg U)}` is the future ray `{(λ,λ,0) : λ ≥ τ}`): along any
non-trivial filter converging naturally to `(apex, t)`, every limit of `btzDev` lies on the ray
`x₀ + [t, ∞) u`. -/
theorem btzDev_cluster (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    {F : Filter (DInfty × ℝ)} [F.NeBot] {t : ℝ} (hF : F ≤ 𝓝 (DInfty.apex, t)) {w : ℝ × ℝ × ℝ}
    (hw : Tendsto (btzDev x₀ v) F (𝓝 w)) : ∃ s, t ≤ s ∧ w = x₀ + s • nullU := by
  obtain ⟨hm, hh, hr, ht⟩ := btz_tendsto_r_mul_θ_of x₀ hv hF hw
  set c := (w.2.2 - x₀.2.2) / v.2.1
  set L := (w.1 - x₀.1 - 2 * c * v.2.2 - t) / v.2.1
  have hsq1 : Tendsto (fun y : DInfty × ℝ => (y.1.r * y.1.θ) ^ 2) F (𝓝 (c ^ 2)) := hm.pow 2
  have hsq2 : Tendsto (fun y : DInfty × ℝ => (y.1.r * y.1.θ) ^ 2) F (𝓝 (0 * L)) := by
    refine (hr.mul hh).congr fun y => ?_
    simp only [hornFn]; ring
  have hc : c = 0 := by
    have := tendsto_nhds_unique hsq1 hsq2
    rw [zero_mul] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hL : 0 ≤ L := ge_of_tendsto hh (Eventually.of_forall hornFn_nonneg)
  have hb : Tendsto (fun y => (btzDev x₀ v y).2.1) F (𝓝 w.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hw
  have hb' : Tendsto (fun y => (btzDev x₀ v y).2.1) F (𝓝 (x₀.2.1 + 0 * v.2.1)) := by
    refine (tendsto_const_nhds.add (hr.mul tendsto_const_nhds)).congr fun y => ?_
    rw [btzDev_coords]
  rw [zero_mul, add_zero] at hb'
  have hw2 : w.2.1 = x₀.2.1 := tendsto_nhds_unique hb hb'
  have hw3 : w.2.2 = x₀.2.2 := by
    have : (w.2.2 - x₀.2.2) / v.2.1 = 0 := hc
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · exact absurd h hv.ne'
  refine ⟨t + L * v.2.1, by nlinarith, ?_⟩
  have hw1 : w.1 = x₀.1 + 2 * c * v.2.2 + t + L * v.2.1 := by
    simp only [L]; field_simp; ring
  rw [hc] at hw1
  ext
  · simp [nullU, hw1]; ring
  · simp [nullU, hw2]
  · simp [nullU, hw3]

/-- **`T_BTZ` is the coarsest topology finer than the natural one making `D` continuous**:
`hornTop = T_natural ⊓ D^*T_{𝐌³}` (Minkowski coordinates; equivalently null coordinates). -/
theorem hornTop_eq_inf_induced (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    hornTop = (inferInstance : TopologicalSpace (DInfty × ℝ)) ⊓
      TopologicalSpace.induced (btzDevM x₀ v) inferInstance := by
  refine le_antisymm (le_inf hornTop_le
    (continuous_iff_le_induced.1 (continuous_btzDevM_hornTop x₀ hv))) ?_
  refine le_of_nhds_le_nhds fun y => ?_
  rw [nhds_hornTop, nhds_inf, nhds_induced]
  refine le_inf inf_le_left (Tendsto.le_comap ?_)
  rcases y.1.pos_or_eq_apex with hr | hr
  · exact (continuousAt_hornFn_of_pos hr).tendsto.mono_left inf_le_left
  · obtain ⟨p, t⟩ := y
    simp only at hr
    subst hr
    have hw : Tendsto (btzDev x₀ v) (𝓝 (DInfty.apex, t) ⊓
        comap (btzDevM x₀ v) (𝓝 (btzDevM x₀ v (DInfty.apex, t)))) (𝓝 (x₀ + t • nullU)) := by
      have h := ((nullToMinkHomeomorph.symm.continuous.tendsto
        (btzDevM x₀ v (DInfty.apex, t))).comp tendsto_comap).mono_left
          (inf_le_right : 𝓝 (DInfty.apex, t) ⊓ comap (btzDevM x₀ v)
            (𝓝 (btzDevM x₀ v (DInfty.apex, t))) ≤ _)
      have he : (nullToMinkHomeomorph.symm ∘ btzDevM x₀ v) = btzDev x₀ v := funext fun y => by
        simp [btzDevM]
      rw [he] at h
      convert h using 2
      simp [btzDevM, btzDev_apex]
    have hh := (btz_tendsto_r_mul_θ_of x₀ hv inf_le_left hw).2.1
    rw [hornFn_apex]
    convert hh using 2
    simp [nullU]

end CylTop

/-! ### `\widetilde{𝔼₀}`: the developing map, the topology `T_BTZ`, virtual tameness -/

section Cover

variable [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]
  {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α))}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) y₀ ≃ₜ
    DInfty × ℝ}

/-- **`D ∘ Φ` is a developing map of `\widetilde{𝔼₀}` over its regular part**
(`def:singular_manifold_virtually_tame` (B), the regular half): it induces a `(G,X)`-morphism on
`p⁻¹(reg 𝔼₀)` for the structure `p^*B`. -/
theorem btz_isRegDevelopingOnReg (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    IsRegDevelopingOnReg (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) y₀
      (btzDevM x₀ v ∘ Φ) := by
  obtain ⟨h1, h2, h3, h4⟩ := btz_instances (α := α) hα
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  obtain ⟨hA, hβR⟩ := isRegularOn_base_maxBranched (btz_slsc hv hα hπ) y₀
  refine isRegularOn_model_of_eventually_comp hA hβR fun e he => ?_
  have hR := btz_reg hv hα hπ
  have hy : Φ e ∈ cylPos ℝ := by
    have : orbitMk (GammaA α) (Φ e) ∈ orbitMk (GammaA α) '' cylPos ℝ := by
      rw [hΦ e, ← hR]; exact he
    rw [← preimage_image_cylPos (Z := ℝ) α]; exact this
  obtain ⟨c, hc, hec⟩ := mem_support.1 (show e.base ∈ Reg (Causal.Flat.isom 2)
    (Causal.Minkowski 2) (BTZModel α) from he)
  obtain ⟨g, hg⟩ := btz_eventually_chart hv hπ hy hc (by rw [hΦ e]; exact hec)
  refine ⟨c, hc, hec, g, ?_⟩
  filter_upwards [(Φ.continuous.tendsto e).eventually hg] with e' he'
  rw [comp_apply, he', hΦ e']

/-- **`T_BTZ` on `\widetilde{𝔼₀}` is a tamifying topology** (`def:singular_manifold_virtually_tame`):
the topology `T_BTZ = hornTop` of `sec:mot_BTZ` (generated by the natural one and the
`U_λ = {rθ² < λ}`, `hornTop_eq_btzGenTop`), transported to `\widetilde{𝔼₀}` along `Φ`. (A) is the
corrected argument of `prop:BTZ_virt_tame` (D-6: a `Γ`-invariant `T`-open set is open,
`coinduced_orbitMk_tamTop`); (B) `D ∘ Φ` is `T`-continuous (`continuous_btzDevM_hornTop`) and a
developing map on the regular part (`btz_isRegDevelopingOnReg`); (C) `Γ(\widetilde{𝔼₀}/𝔼₀) = Γ_α`
(`exists_gamma_eq_of_over`) acts `T`-continuously; (D) `isPortly_cylPos_tamTop`. -/
theorem btz_isTamifyingTopology (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) y₀
      (TopologicalSpace.induced Φ hornTop) := by
  have hW : IsOpen (univ : Set ℝ) := isOpen_univ
  have key : IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) y₀
      (pullTamTop Φ univ) := by
    have hle : (pullTamTop Φ univ) ≤ weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2)
        (BTZModel α) y₀ :=
      (induced_mono (tamTop_le hW)).trans_eq Φ.induced_eq
    have hbase : (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
        (BTZModel α)) y₀ → BTZModel α) = orbitMk (GammaA α) ∘ Φ := funext fun e => (hΦ e).symm
    have hΦc : Continuous[pullTamTop Φ univ, tamTop univ] Φ := continuous_induced_dom
    have hΦsc : Continuous[tamTop univ, pullTamTop Φ univ] Φ.symm := continuous_induced_rng.2 (by
      have : (Φ : _ → DInfty × ℝ) ∘ Φ.symm = id := funext Φ.apply_symm_apply
      rw [this]; exact @continuous_id _ (tamTop univ))
    refine ⟨hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact @TopologicalSpace.firstCountableTopology_induced _ _ (tamTop univ) (firstCountable_tamTop hW) Φ
    · have hemb : @IsOpenEmbedding _ _ (pullTamTop Φ univ) (tamTop univ) Φ :=
        @IsOpenEmbedding.mk _ _ (pullTamTop Φ univ) (tamTop univ) Φ
          (@IsEmbedding.mk _ _ (pullTamTop Φ univ) (tamTop univ) Φ
            (@IsInducing.mk _ _ (pullTamTop Φ univ) (tamTop univ) Φ rfl) Φ.injective)
          (by rw [Φ.range_coe]; exact @isOpen_univ _ (tamTop univ))
      exact @IsOpenEmbedding.locPathConnectedSpace _ _ (tamTop univ) (pullTamTop Φ univ)
        (locPathConnected_tamTop hW) Φ hemb
    · rw [hbase, ← @coinduced_compose _ _ _ (pullTamTop Φ univ) Φ (orbitMk (GammaA α)),
        coinduced_induced_of_surjective Φ.surjective, coinduced_orbitMk_tamTop hα hW]
    · refine ⟨btzDevM x₀ v ∘ Φ, ?_, btz_isRegDevelopingOnReg hv hα hπ hΦ⟩
      have hD : Continuous[tamTop univ, inferInstance] (btzDevM x₀ v) := by
        rw [tamTop_univ]; exact continuous_btzDevM_hornTop x₀ hv
      exact @Continuous.comp _ _ _ (pullTamTop Φ univ) (tamTop univ) _ _ _ hD hΦc
    · rintro _ ⟨γ, hγ, rfl⟩
      set ψ : DInfty × ℝ ≃ₜ DInfty × ℝ := (Φ.symm.trans γ).trans Φ
      have hψ : ∀ y, orbitMk (GammaA α) (ψ y) = orbitMk (GammaA α) y := fun y => by
        show orbitMk (GammaA α) (Φ (γ (Φ.symm y))) = _
        rw [hΦ (γ (Φ.symm y)), deck_apply (p := SpreadEnd.base) hγ (Φ.symm y), ← hΦ (Φ.symm y),
          Φ.apply_symm_apply]
      obtain ⟨k, hk⟩ := exists_gamma_eq_of_over hα ψ hψ
      refine continuous_induced_rng.2 ?_
      have : (Φ : _ → DInfty × ℝ) ∘ γ = (fun y => k • y) ∘ Φ := funext fun e => by
        show Φ (γ e) = k • Φ e
        rw [← hk]
        show Φ (γ e) = Φ (γ (Φ.symm (Φ e)))
        rw [Φ.symm_apply_apply]
      rw [this]
      exact @Continuous.comp _ _ _ (pullTamTop Φ univ) (tamTop univ) (tamTop univ) _ _
        (continuous_smul_tamTop k) hΦc
    · have hpre : (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
          (BTZModel α)) y₀ → BTZModel α) ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2)
            (BTZModel α) = Φ.symm '' cylPos ℝ := by
        rw [Φ.image_symm]
        ext e
        simp only [mem_preimage, btz_reg hv hα hπ, ← hΦ e]
        rw [← mem_preimage (f := orbitMk (GammaA α)), preimage_image_cylPos]
      rw [hpre]
      have hopen : @IsOpenMap _ _ (tamTop univ) (pullTamTop Φ univ) Φ.symm := fun V hV =>
        ⟨V, hV, by rw [Φ.image_symm]⟩
      exact @IsPortly.image_of_isOpenMap _ _ (tamTop univ) (pullTamTop Φ univ)
        (locallyConnectedSpace_of_lpc_sptop (locPathConnected_tamTop hW)) Φ.symm hΦsc hopen
        Φ.symm.surjective _ (isPortly_cylPos_tamTop hW)
  rw [pullTamTop, tamTop_univ] at key
  exact key

end Cover

/-- A regular base point of `𝔼₀`. -/
theorem btz_exists_reg [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]
    (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    Nonempty ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α)) := by
  refine ⟨⟨orbitMk (GammaA α) (DInfty.posEmb ⟨(1, 0), one_pos⟩, 0), ?_⟩⟩
  show _ ∈ (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ
  rw [Sing, compl_compl, btz_reg hv hα hπ]
  exact ⟨_, show (0 : ℝ) < 1 from one_pos, rfl⟩

/-- **`prop:BTZ_virt_tame`** (`RamcovGX.tex:2252`): **the BTZ model space is virtually tame**, for
every structure making it the BTZ model (`IsBTZStructure`; one exists and it is unique,
`btz_existsUnique`), every `x₀`, every `v` with `⟨v | u⟩ < 0` and every angle `α ≠ 0` (the paper's
`α = 2π`, `x₀ = 0`, `v = (−1, 1, 0)`: `btzE0_virt_tame`). The tamifying topology is `T_BTZ`
(`btz_isTamifyingTopology`). -/
theorem btz_virt_tame [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]
    (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    IsVirtuallyTame (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) := by
  obtain ⟨y₀⟩ := btz_exists_reg hv hα hπ
  obtain ⟨Φ, hΦ⟩ := btz_exists_homeomorph hv hα hπ y₀
  exact ⟨y₀, _, btz_isTamifyingTopology hv hα hπ hΦ⟩

/-! ### The holonomy `ρ(γ) = btzHol`: parabolic, fixing `Δ` pointwise -/

section Holonomy

/-- `btzHol` fixes the singular line `Δ` pointwise (`RamcovGX.tex:2250`). -/
theorem btzHol_smul_of_mem_btzLine (x₀ : ℝ × ℝ × ℝ) (α : ℝ) {q : Causal.Minkowski 2}
    (hq : q ∈ btzLine x₀) : btzHol x₀ α • q = q := by
  obtain ⟨s, rfl⟩ := hq
  exact nullIsom0EquivIsom_parab_smul x₀ α s

/-- The linear part of `btzHol`: `nullToMink ∘ P_α ∘ nullToMink⁻¹`. -/
theorem linearPart_btzHol_apply (x₀ : ℝ × ℝ × ℝ) (α : ℝ) (z : ℝ × ℝ × ℝ) :
    ((Causal.Flat.linearPart (btzHol x₀ α) : Causal.Flat.lorentz 2) :
      Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) (nullToMink z) = nullToMink (parab α z) := by
  rw [Causal.Flat.linearPart_apply, btzHol, coe_nullIsom0EquivIsom, nullAffConj_linear]
  show nullToMink ((parabAff x₀ α).linear (nullToMink.symm (nullToMink z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem pOf_btzHol_apply (x₀ : ℝ × ℝ × ℝ) (α : ℝ) (z : ℝ × ℝ × ℝ) :
    Causal.Flat.pOf ((Causal.Flat.linearPart (btzHol x₀ α) : Causal.Flat.lorentz 2) :
      Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) (nullToMink z) = nullToMink (parab α z - z) := by
  rw [Causal.Flat.pOf_apply, linearPart_btzHol_apply, map_sub]

/-- The linear part of `btzHol` is not the identity (`α ≠ 0`). -/
theorem linearPart_btzHol_ne_one (x₀ : ℝ × ℝ × ℝ) {α : ℝ} (hα : α ≠ 0) :
    ((Causal.Flat.linearPart (btzHol x₀ α) : Causal.Flat.lorentz 2) :
      Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) ≠ 1 := by
  intro h1
  have h := congrArg (fun A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2 =>
    A (nullToMink (0, 0, 1))) h1
  simp only [linearPart_btzHol_apply, LinearEquiv.coe_one, id] at h
  have h2 := congrArg Prod.fst (nullToMink.injective h)
  simp [parab_apply] at h2
  exact hα h2

/-- **The holonomy is parabolic** (`RamcovGX.tex:2250`, in the corrected classification D-1:
read on the linear part): the linear part of `btzHol` is a non-trivial unipotent element of
`SO₀(1,2)`, hence parabolic in `lean-causal`'s sense (`Causal.Flat.IsParabolic`); it fixes the
lightlike direction of `Δ` (`linearPart_btzHol_nullU`). -/
theorem btzHol_isParabolic (x₀ : ℝ × ℝ × ℝ) {α : ℝ} (hα : α ≠ 0) :
    Causal.Flat.IsParabolic ((Causal.Flat.linearPart (btzHol x₀ α) : Causal.Flat.lorentz 2) :
      Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) := by
  refine Causal.Flat.IsUnipotent.isParabolic (Causal.Flat.linearPart (btzHol x₀ α)).2
    ⟨3, LinearMap.ext fun x => ?_⟩ (linearPart_btzHol_ne_one x₀ hα)
  obtain ⟨z, rfl⟩ := nullToMink.surjective x
  rw [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply, pOf_btzHol_apply,
    pOf_btzHol_apply, pOf_btzHol_apply, LinearMap.zero_apply]
  rw [← map_zero nullToMink]
  congr 1
  simp only [parab_apply]
  ext <;> simp

/-- The linear part of `btzHol` fixes the lightlike direction `nullToMink u` of `Δ`. -/
theorem linearPart_btzHol_nullU (x₀ : ℝ × ℝ × ℝ) (α : ℝ) :
    ((Causal.Flat.linearPart (btzHol x₀ α) : Causal.Flat.lorentz 2) :
      Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) (nullToMink nullU) = nullToMink nullU ∧
    Causal.Flat.minkQ (nullToMink nullU) = 0 ∧ nullToMink nullU ≠ 0 := by
  refine ⟨by rw [linearPart_btzHol_apply, parab_nullU], by rw [minkQ_nullToMink]; simp [nullQ, nullU],
    fun h => ?_⟩
  have := congrArg Prod.fst h
  rw [fst_nullToMink] at this
  simp [nullU] at this

/-- `btzHol ≠ 1` (`α ≠ 0`). -/
theorem btzHol_ne_one (x₀ : ℝ × ℝ × ℝ) {α : ℝ} (hα : α ≠ 0) : btzHol x₀ α ≠ 1 := fun h =>
  linearPart_btzHol_ne_one x₀ hα (by rw [h, map_one]; rfl)

/-- `btzHol^n = btzHol` at angle `nα`. -/
theorem btzHol_zpow (x₀ : ℝ × ℝ × ℝ) (α : ℝ) (n : ℤ) :
    btzHol x₀ α ^ n = btzHol x₀ (n * α) := by
  refine Subtype.ext (AffineEquiv.ext fun p => ?_)
  obtain ⟨z, rfl⟩ := nullToMink.surjective p
  show (btzHol x₀ α ^ n) • nullToMink z = btzHol x₀ (n * α) • nullToMink z
  have h2 := btzHol_zpow_smul x₀ (n * α) 1 z
  rw [zpow_one] at h2
  rw [btzHol_zpow_smul, h2, parabAff_zpow, parabAff_zpow, Int.cast_one, one_mul]

end Holonomy

/-! ### `Γ(\widetilde{𝔼₀}/𝔼₀) ≅ ℤ` and the holonomy of `\widetilde{𝔼₀}` -/

section Deck

variable [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]
  {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α))}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) y₀ ≃ₜ
    DInfty × ℝ}

/-- The deck transformation of `\widetilde{𝔼₀}` induced by `k ∈ Γ_α`: `Φ⁻¹ ∘ (k ·) ∘ Φ`. -/
noncomputable def btzDeckOf (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) (k : GammaA α) :
    deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
      (BTZModel α)) y₀ → BTZModel α) :=
  ⟨(Φ.trans (Homeomorph.smul k)).trans Φ.symm, funext fun e => by
    show (Φ.symm (k • Φ e)).base = e.base
    rw [← hΦ, Φ.apply_symm_apply, orbitMk_smul, hΦ]⟩

theorem btzDeckOf_apply (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) (k : GammaA α) (e) :
    (btzDeckOf hΦ k : _ ≃ₜ _) e = Φ.symm (k • Φ e) := rfl

/-- `k ↦ Φ⁻¹ ∘ (k ·) ∘ Φ` as a group homomorphism `Γ_α → Γ(\widetilde{𝔼₀}/𝔼₀)`. -/
noncomputable def btzDeckHom (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    GammaA α →* deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α) where
  toFun := btzDeckOf hΦ
  map_one' := Subtype.ext (Homeomorph.ext fun e => by
    show Φ.symm ((1 : GammaA α) • Φ e) = e
    rw [one_smul, Φ.symm_apply_apply])
  map_mul' a b := Subtype.ext (Homeomorph.ext fun e => by
    show Φ.symm ((a * b) • Φ e) = Φ.symm (a • Φ (Φ.symm (b • Φ e)))
    rw [mul_smul, Φ.apply_symm_apply])

theorem btzDeckOf_eq_one (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base)
    {k : GammaA α} (hk : btzDeckOf hΦ k = 1) : k = 1 := by
  have h : Φ.symm (k • Φ (Φ.symm (DInfty.posEmb ⟨(1, 0), one_pos⟩, (0 : ℝ)))) =
      Φ.symm (DInfty.posEmb ⟨(1, 0), one_pos⟩, (0 : ℝ)) :=
    DFunLike.congr_fun (congrArg Subtype.val hk) _
  rw [Φ.apply_symm_apply] at h
  have h' := congrArg Φ h
  rw [Φ.apply_symm_apply, Φ.apply_symm_apply] at h'
  exact DInfty.free_pos hα _ (show (0 : ℝ) < 1 from one_pos) k h'

theorem btzDeckOf_surjective (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base)
    (γ : deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α)) : ∃ k, btzDeckOf hΦ k = γ := by
  obtain ⟨γ, hγ⟩ := γ
  have hψ : ∀ y, orbitMk (GammaA α) (((Φ.symm.trans γ).trans Φ) y) = orbitMk (GammaA α) y :=
    fun y => by
      show orbitMk (GammaA α) (Φ (γ (Φ.symm y))) = _
      rw [hΦ (γ (Φ.symm y)), deck_apply (p := SpreadEnd.base) hγ (Φ.symm y), ← hΦ (Φ.symm y),
        Φ.apply_symm_apply]
  obtain ⟨k, hk⟩ := exists_gamma_eq_of_over hα _ hψ
  refine ⟨k, Subtype.ext (Homeomorph.ext fun e => ?_)⟩
  show Φ.symm (k • Φ e) = γ e
  rw [← hk]
  show Φ.symm (Φ (γ (Φ.symm (Φ e)))) = γ e
  rw [Φ.symm_apply_apply, Φ.symm_apply_apply]

theorem btzDeckHom_bijective (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    Bijective (btzDeckHom hΦ) :=
  ⟨(injective_iff_map_eq_one _).2 fun _ hk => btzDeckOf_eq_one hα hΦ hk,
    btzDeckOf_surjective hα hΦ⟩

/-- **`Γ(\widetilde{𝔼₀}/𝔼₀) ≅ Γ_α ≅ ℤ`** (`RamcovGX.tex:2250`). -/
noncomputable def btzDeckEquiv (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    GammaA α ≃* deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α) :=
  MulEquiv.ofBijective (btzDeckHom hΦ) (btzDeckHom_bijective hα hΦ)

/-- `Γ_α ≅ ℤ`. -/
def gammaAEquivInt : GammaA α ≃* Multiplicative ℤ where
  toFun k := Multiplicative.ofAdd k.toInt
  invFun n := GammaA.ofInt (Multiplicative.toAdd n)
  left_inv k := rfl
  right_inv n := rfl
  map_mul' a b := by rw [GammaA.toInt_mul, ofAdd_add]

/-- **`Γ(\widetilde{𝔼₀}/𝔼₀) ≅ ℤ`**. -/
theorem btz_deck_equiv_int (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    Nonempty (deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α) ≃* Multiplicative ℤ) :=
  ⟨(btzDeckEquiv hα hΦ).symm.trans gammaAEquivInt⟩

/-- `k ↦ btzHol^k`, the holonomy on `Γ_α`. -/
noncomputable def btzHolHom (x₀ : ℝ × ℝ × ℝ) (α : ℝ) : GammaA α →* Causal.Flat.isom 2 where
  toFun k := btzHol x₀ α ^ k.toInt
  map_one' := by simp
  map_mul' a b := by rw [GammaA.toInt_mul, zpow_add]

/-- **The holonomy of `\widetilde{𝔼₀}`**: `ρ : Γ(\widetilde{𝔼₀}/𝔼₀) → Isom(𝐌³)`. -/
noncomputable def btzHolonomy (x₀ : ℝ × ℝ × ℝ) (hα : α ≠ 0)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α) →* Causal.Flat.isom 2 :=
  (btzHolHom x₀ α).comp (btzDeckEquiv hα hΦ).symm.toMonoidHom

/-- **The holonomy**: `D(γ e) = ρ(γ) · D(e)` on `\widetilde{𝔼₀}` (everywhere, axis included), and
`ρ` of the generator is `btzHol`, parabolic and fixing `Δ` pointwise. -/
theorem btz_holonomy (x₀ v : ℝ × ℝ × ℝ) (hα : α ≠ 0) (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base)
    (γ : deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α)) (e) :
    btzDevM x₀ v (Φ (γ.1 e)) = btzHolonomy x₀ hα hΦ γ • btzDevM x₀ v (Φ e) := by
  obtain ⟨k, rfl⟩ := btzDeckOf_surjective hα hΦ γ
  have hk : (btzDeckEquiv hα hΦ).symm (btzDeckOf hΦ k) = k :=
    (btzDeckEquiv hα hΦ).symm_apply_apply k
  show btzDevM x₀ v (Φ (Φ.symm (k • Φ e))) =
    btzHolHom x₀ α ((btzDeckEquiv hα hΦ).symm (btzDeckOf hΦ k)) • btzDevM x₀ v (Φ e)
  rw [hk, Φ.apply_symm_apply, btzDevM_smul]
  rfl

theorem btzHolonomy_generator (x₀ : ℝ × ℝ × ℝ) (hα : α ≠ 0)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    btzHolonomy x₀ hα hΦ (btzDeckOf hΦ (GammaA.ofInt 1)) = btzHol x₀ α := by
  have hk : (btzDeckEquiv hα hΦ).symm (btzDeckHom hΦ (GammaA.ofInt 1)) = GammaA.ofInt 1 :=
    (btzDeckEquiv hα hΦ).symm_apply_apply _
  show btzHolHom x₀ α ((btzDeckEquiv hα hΦ).symm (btzDeckHom hΦ (GammaA.ofInt 1))) = _
  rw [hk]
  show btzHol x₀ α ^ (1 : ℤ) = _
  rw [zpow_one]

/-- `ρ` of the deck transformation of `k ∈ Γ_α` is `btzHol^k`. -/
theorem btzHolonomy_deckOf (x₀ : ℝ × ℝ × ℝ) (hα : α ≠ 0)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) (k : GammaA α) :
    btzHolonomy x₀ hα hΦ (btzDeckOf hΦ k) = btzHol x₀ α ^ k.toInt := by
  have hk : (btzDeckEquiv hα hΦ).symm (btzDeckHom hΦ k) = k :=
    (btzDeckEquiv hα hΦ).symm_apply_apply _
  show btzHolHom x₀ α ((btzDeckEquiv hα hΦ).symm (btzDeckHom hΦ k)) = _
  rw [hk]
  rfl

/-- The deck transformation of `1` is the identity. -/
theorem btzDeckOf_one (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) :
    btzDeckOf hΦ (1 : GammaA α) = 1 :=
  Subtype.ext (Homeomorph.ext fun e => by
    show Φ.symm ((1 : GammaA α) • Φ e) = e
    rw [one_smul, Φ.symm_apply_apply])

/-- **Every non-trivial `ρ(γ)` is parabolic and fixes `Δ` pointwise** (`RamcovGX.tex:2250`), in
particular `ρ` of **either** generator `γ^{±1}` of `Γ ≅ ℤ` (`ρ(γ^{-1}) = btzHol⁻¹ = btzHol` at angle
`−α`, `btzHol_zpow`): `ρ(γ) = btzHol` at angle `kα ≠ 0`. -/
theorem btzHolonomy_isParabolic (x₀ : ℝ × ℝ × ℝ) (hα : α ≠ 0)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base)
    {γ : deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α)} (hγ : γ ≠ 1) :
    Causal.Flat.IsParabolic ((Causal.Flat.linearPart (btzHolonomy x₀ hα hΦ γ) :
      Causal.Flat.lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) ∧
    ∀ q ∈ btzLine x₀, btzHolonomy x₀ hα hΦ γ • q = q := by
  have hs := btzDeckOf_surjective hα hΦ γ
  obtain ⟨k, hkγ⟩ := hs
  have hk : k.toInt ≠ 0 := by
    intro h
    have h1 : k = 1 := by rw [← GammaA.ofInt_toInt k, h]; rfl
    apply hγ
    rw [← hkγ, h1, btzDeckOf_one]
  rw [← hkγ, btzHolonomy_deckOf, btzHol_zpow]
  exact ⟨btzHol_isParabolic x₀ (mul_ne_zero (Int.cast_ne_zero.2 hk) hα),
    fun q hq => btzHol_smul_of_mem_btzLine x₀ _ hq⟩

/-- **`Γ(\widetilde{𝔼₀}/𝔼₀)` stabilizes the singular locus pointwise** (`RamcovGX.tex:2250`): every
deck transformation fixes every point of `p⁻¹(Sing 𝔼₀)` (on the cylinder, `Γ_α` rotates the angle
and fixes the axis). -/
theorem btz_deck_fix_sing (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base)
    (γ : deckGroup (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) (BTZModel α)) y₀ → BTZModel α)) {e}
    (he : SpreadEnd.base e ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) :
    γ.1 e = e := by
  have key : ∀ (k : GammaA α) (y : DInfty × ℝ), y.1 = DInfty.apex → k • y = y := by
    rintro k ⟨p, t⟩ hp
    simp only at hp
    subst hp
    rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_apex]
  have he' : orbitMk (GammaA α) (Φ e) ∈
      orbitMk (GammaA α) '' {x : DInfty × ℝ | x.1 = DInfty.apex} := by
    rw [← btz_sing hv hα hπ, hΦ e]; exact he
  obtain ⟨x, hx, hxe⟩ := he'
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq hxe
  have hax : (Φ e).1 = DInfty.apex := by rw [← hk, key k x hx]; exact hx
  obtain ⟨k', rfl⟩ := btzDeckOf_surjective hα hΦ γ
  show Φ.symm (k' • Φ e) = e
  rw [key k' _ hax, Φ.symm_apply_apply]

end Deck

/-! ### `Aut(\widetilde{𝔼₀})` acts `T_BTZ`-continuously -/

section Aut

theorem dense_cylPos_hornTop : @Dense _ hornTop (cylPos ℝ) := by
  have := dense_cylPos_tamTop (W := univ) isOpen_univ
  rwa [tamTop_univ] at this

/-- `btzDevM` on the axis: `t ↦ nullToMink x₀ + t • nullToMink u`. -/
theorem btzDevM_apex_eq (x₀ v : ℝ × ℝ × ℝ) (t : ℝ) :
    btzDevM x₀ v (DInfty.apex, t) = nullToMink x₀ + t • nullToMink nullU := by
  rw [btzDevM_apex, map_add, map_smul]

theorem btzDevM_apex_injective (x₀ v : ℝ × ℝ × ℝ) {t t' : ℝ}
    (h : btzDevM x₀ v (DInfty.apex, t) = btzDevM x₀ v (DInfty.apex, t')) : t = t' := by
  rw [btzDevM_apex, btzDevM_apex] at h
  have h' := congrArg Prod.fst (nullToMink.injective h)
  simp only [Prod.fst_add, Prod.smul_fst, nullU, smul_eq_mul, mul_one] at h'
  linarith

/-- **The axis values of a `D`-equivariant homeomorphism** (one half): if `D ∘ ψ = g D` on
`{r > 0}` and `ψ(apex, t) = (apex, t')`, then `g D(apex, t) = D(apex, s)` for some `s ≥ t'` (a
cluster value of `D` at `(apex, t')`, `btzDev_cluster`). -/
theorem btzDevM_axis_of (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (g : Causal.Flat.isom 2)
    (hg : ∀ y ∈ cylPos ℝ, btzDevM x₀ v (ψ y) = g • btzDevM x₀ v y) {t t' : ℝ}
    (hψt : ψ (DInfty.apex, t) = (DInfty.apex, t')) :
    ∃ s, t' ≤ s ∧ g • btzDevM x₀ v (DInfty.apex, t) = btzDevM x₀ v (DInfty.apex, s) := by
  set p : DInfty × ℝ := (DInfty.apex, t)
  have hF₀ : (@nhdsWithin _ hornTop p (cylPos ℝ)).NeBot :=
    (@mem_closure_iff_nhdsWithin_neBot _ hornTop p (cylPos ℝ)).1 (dense_cylPos_hornTop p)
  haveI := hF₀
  have hDF : Tendsto (btzDevM x₀ v) (@nhdsWithin _ hornTop p (cylPos ℝ))
      (𝓝 (btzDevM x₀ v p)) :=
    (@Continuous.tendsto _ _ hornTop _ _ (continuous_btzDevM_hornTop x₀ hv) p).mono_left
      inf_le_left
  have hgDF : Tendsto (btzDevM x₀ v ∘ ψ) (@nhdsWithin _ hornTop p (cylPos ℝ))
      (𝓝 (g • btzDevM x₀ v p)) := by
    have h1 : Tendsto (fun y => g • btzDevM x₀ v y) (@nhdsWithin _ hornTop p (cylPos ℝ))
        (𝓝 (g • btzDevM x₀ v p)) :=
      (((continuous_const_smul g : Continuous fun q : Causal.Minkowski 2 => g • q).tendsto _)).comp
        hDF
    refine h1.congr' ?_
    filter_upwards [@self_mem_nhdsWithin _ hornTop p (cylPos ℝ)] with y hy
    exact (hg y hy).symm
  have hFle : map ψ (@nhdsWithin _ hornTop p (cylPos ℝ)) ≤ 𝓝 (DInfty.apex, t') := by
    rw [← hψt]
    refine (map_mono (inf_le_left.trans (nhds_mono hornTop_le))).trans ?_
    exact ψ.continuous.tendsto p
  have hF : Tendsto (btzDev x₀ v) (map ψ (@nhdsWithin _ hornTop p (cylPos ℝ)))
      (𝓝 (nullToMink.symm (g • btzDevM x₀ v p))) := by
    rw [tendsto_map'_iff]
    have := ((nullToMinkHomeomorph.symm.continuous.tendsto _)).comp hgDF
    refine this.congr fun y => ?_
    simp [btzDevM]
  obtain ⟨s, hs, hw⟩ := btzDev_cluster x₀ hv hFle hF
  refine ⟨s, hs, ?_⟩
  rw [btzDevM_apex x₀ v s, ← hw, LinearEquiv.apply_symm_apply]

/-- `nullToMink u` is future causal. -/
theorem isFutureCausal_nullToMink_nullU : Causal.Flat.IsFutureCausal (nullToMink nullU) := by
  refine ⟨?_, ?_⟩
  · rw [fst_nullToMink]; simp [nullU]
  · rw [minkQ_nullToMink]; simp [nullQ, nullU]

/-- **A `D`-equivariant homeomorphism is `D`-equivariant on the axis too**: if `ψ` is a
homeomorphism of the cylinder preserving `{r > 0}` with `D ∘ ψ = g D` there, then
`D ∘ ψ = g D` everywhere. (`g` preserves `Δ` and its future orientation; the cluster values of
`D` at the axis, `btzDevM_axis_of`, for `ψ` and `ψ⁻¹`, pin `g D(apex, t)` to `D(ψ(apex, t))`.) -/
theorem btzDevM_comp_eq_of (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ) (hψP : ψ ⁻¹' cylPos ℝ = cylPos ℝ) (g : Causal.Flat.isom 2)
    (hg : ∀ y ∈ cylPos ℝ, btzDevM x₀ v (ψ y) = g • btzDevM x₀ v y) (y : DInfty × ℝ) :
    btzDevM x₀ v (ψ y) = g • btzDevM x₀ v y := by
  rcases y.1.pos_or_eq_apex with hy | hy
  · exact hg y hy
  obtain ⟨p, t⟩ := y
  simp only at hy
  subst hy
  -- `ψ` and `ψ⁻¹` preserve the axis
  have haxis : ∀ z : DInfty × ℝ, z.1 = DInfty.apex → (ψ z).1 = DInfty.apex := fun z hz =>
    DInfty.eq_apex_of_not_pos fun h => by
      have : z ∈ ψ ⁻¹' cylPos ℝ := h
      rw [hψP] at this
      have h' : (0 : ℝ) < z.1.r := this
      rw [hz] at h'; exact lt_irrefl _ h'
  have hψsP : ψ.symm ⁻¹' cylPos ℝ = cylPos ℝ := by
    rw [← ψ.image_eq_preimage_symm]
    conv_lhs => rw [← hψP]
    rw [ψ.image_preimage]
  have hgs : ∀ y ∈ cylPos ℝ, btzDevM x₀ v (ψ.symm y) = g⁻¹ • btzDevM x₀ v y := fun y hy => by
    have hy' : ψ.symm y ∈ cylPos ℝ := by
      have : y ∈ ψ.symm ⁻¹' cylPos ℝ := by rw [hψsP]; exact hy
      exact this
    rw [eq_inv_smul_iff, ← hg _ hy', ψ.apply_symm_apply]
  set t' := (ψ (DInfty.apex, t)).2
  have hψt : ψ (DInfty.apex, t) = (DInfty.apex, t') := Prod.ext (haxis _ rfl) rfl
  -- `g` maps `Δ` to itself, affinely and preserving the orientation
  set q₀ := nullToMink x₀
  set u := nullToMink nullU
  have hline : ∀ τ : ℝ, ∃ s, g • btzDevM x₀ v (DInfty.apex, τ) = btzDevM x₀ v (DInfty.apex, s) :=
    fun τ => by
      obtain ⟨s, -, hs⟩ := btzDevM_axis_of x₀ hv ψ g hg
        (Prod.ext (haxis (DInfty.apex, τ) rfl) rfl : ψ (DInfty.apex, τ) = (DInfty.apex, _))
      exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := hline 0
  obtain ⟨s₁, hs₁⟩ := hline 1
  have hq : ∀ τ : ℝ, btzDevM x₀ v (DInfty.apex, τ) = q₀ + τ • u := btzDevM_apex_eq x₀ v
  have hg0 : g • q₀ = q₀ + s₀ • u := by
    have := hs₀; rw [hq, hq, zero_smul, add_zero] at this; exact this
  have hg1 : g • (q₀ + u) = q₀ + s₁ • u := by
    have := hs₁; rw [hq, hq, one_smul] at this; exact this
  have hsub : ∀ a b : Causal.Minkowski 2, g • b - g • a =
      (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear (b - a) := fun a b =>
    Causal.Flat.isom_sub _ a b
  have hL : (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear u = (s₁ - s₀) • u := by
    have := hsub q₀ (q₀ + u)
    rw [hg0, hg1, add_sub_cancel_left] at this
    rw [← this, sub_smul]; abel
  have haff : ∀ τ : ℝ, g • btzDevM x₀ v (DInfty.apex, τ) =
      btzDevM x₀ v (DInfty.apex, s₀ + τ * (s₁ - s₀)) := by
    intro τ
    have := hsub q₀ (q₀ + τ • u)
    rw [add_sub_cancel_left, map_smul, hL, hg0, sub_eq_iff_eq_add] at this
    rw [hq, hq, this, add_smul, mul_smul]; abel
  set lam := s₁ - s₀
  have hlam : 0 < lam := by
    have hLm := (Causal.Flat.mem_isom_iff.1 g.2).2.1
    have hfc := hLm u isFutureCausal_nullToMink_nullU
    rw [hL] at hfc
    have h1 : 0 ≤ (lam • u).1 := hfc.1
    have hu1 : u.1 = 1 / 2 := by simp [u, fst_nullToMink, nullU]
    simp only [Prod.smul_fst, smul_eq_mul, hu1] at h1
    refine lt_of_le_of_ne (by linarith) fun h0 => ?_
    rw [← h0, zero_smul] at hL
    have hu0 : u = 0 := (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective
      (by rw [hL, map_zero])
    have := congrArg Prod.fst hu0
    rw [hu1] at this; norm_num at this
  -- both halves
  obtain ⟨s, hs, hgs_eq⟩ := btzDevM_axis_of x₀ hv ψ g hg hψt
  have hψst : ψ.symm (DInfty.apex, t') = (DInfty.apex, t) := by
    rw [← hψt, ψ.symm_apply_apply]
  obtain ⟨s', hs', hgs'⟩ := btzDevM_axis_of x₀ hv ψ.symm g⁻¹ hgs hψst
  have h1 : s = s₀ + t * lam := btzDevM_apex_injective x₀ v (hgs_eq.symm.trans (haff t))
  have h2 : t' = s₀ + s' * lam := by
    have : btzDevM x₀ v (DInfty.apex, t') = g • btzDevM x₀ v (DInfty.apex, s') := by
      rw [← hgs', smul_inv_smul]
    exact btzDevM_apex_injective x₀ v (this.trans (haff s'))
  have h3 : s = t' := by nlinarith
  rw [hψt, hgs_eq, h3]

/-- **`Aut` of the cylinder is `T_BTZ`-continuous**, on the cylinder: every homeomorphism which is
an a.e. automorphism of its BTZ structure is `hornTop`-continuous. -/
theorem continuous_hornTop_of_isAEMorphismOf (x₀ : ℝ × ℝ × ℝ) {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1)
    (ψ : DInfty × ℝ ≃ₜ DInfty × ℝ)
    (hψ : IsAEMorphismOf (Causal.Flat.isom 2)
      (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
      (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
      ψ) :
    Continuous[hornTop, hornTop] ψ := by
  have hP := DInfty.isPortly_pos ℝ
  have hD := isLocalHomeomorphOn_btzDevM x₀ hv
  have hdev := isAEAtlas_devAtlas (G := Causal.Flat.isom 2) hP hD
  have hA := hdev.isMaximalAEAtlas_maximalAEAtlas
  have hsupp := support_btzCyl x₀ hv
  have hpre : ψ ⁻¹' cylPos ℝ = cylPos ℝ := by
    have := (hψ.preimage_support_eq hA hA ψ.isLocalHomeomorph).1
    rwa [hsupp] at this
  have hreg := hψ.regLocusOf_eq hA.1 hA.1
  rw [hsupp, hpre, inter_self] at hreg
  have hloc : ∀ y ∈ cylPos ℝ, ∃ g : Causal.Flat.isom 2,
      ∀ᶠ y' in 𝓝 y, btzDevM x₀ v (ψ y') = g • btzDevM x₀ v y' := by
    intro y hy
    have hψy : ψ y ∈ cylPos ℝ := by
      have : y ∈ ψ ⁻¹' cylPos ℝ := by rw [hpre]; exact hy
      exact this
    have hys : y ∈ support (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)) := by
      rw [support_devAtlas hP.isOpen hD]; exact hy
    have hψys : ψ y ∈ support (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)) := by
      rw [support_devAtlas hP.isOpen hD]; exact hψy
    obtain ⟨d, hd, hyd⟩ := mem_support.1 hys
    obtain ⟨d', hd', hψyd'⟩ := mem_support.1 hψys
    have hyR : y ∈ regLocusOf (Causal.Flat.isom 2)
        (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
        (maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v) (cylPos ℝ)))
        ψ := by rw [hreg]; exact hy
    obtain ⟨a, ha⟩ := (isRegularOn_regLocusOf (G := Causal.Flat.isom 2) _ _ _).exists_smul_eq y
      hyR d (hdev.subset_maximalAEAtlas hd) d' (hdev.subset_maximalAEAtlas hd') hyd hψyd'
    obtain ⟨h, hh⟩ := hd.2 y hyd
    obtain ⟨h', hh'⟩ := hd'.2 (ψ y) hψyd'
    refine ⟨h' * a * h⁻¹, ?_⟩
    filter_upwards [ha, hh, (ψ.continuous.tendsto y).eventually hh'] with y' h1 h2 h3
    rw [h3, h1, h2, mul_smul, mul_smul, inv_smul_smul]
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn hP.isOpen hD hP.isPreconnected
    subset_rfl hloc
  have hall := btzDevM_comp_eq_of x₀ hv ψ hpre g hg
  rw [hornTop_eq_inf_induced x₀ hv]
  refine continuous_inf_rng.2 ⟨continuous_le_dom inf_le_left ψ.continuous,
    continuous_induced_rng.2 ?_⟩
  have : btzDevM x₀ v ∘ ψ = (fun q => g • q) ∘ btzDevM x₀ v := funext hall
  rw [this]
  have hDc : Continuous[(inferInstance : TopologicalSpace (DInfty × ℝ)) ⊓
      TopologicalSpace.induced (btzDevM x₀ v) inferInstance, inferInstance] (btzDevM x₀ v) :=
    continuous_le_dom inf_le_right continuous_induced_dom
  exact @Continuous.comp _ _ _ ((inferInstance : TopologicalSpace (DInfty × ℝ)) ⊓
      TopologicalSpace.induced (btzDevM x₀ v) inferInstance) _ _ _ _
    (continuous_const_smul g) hDc

end Aut

/-! ### `\widetilde{𝔼₀}`: `D` injective onto `J⁺(Δ)`, `T_BTZ`, and `Aut(\widetilde{𝔼₀})` -/

section CoverFacts

variable [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)]
  {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α))ᶜ : Set (BTZModel α))}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α)) y₀ ≃ₜ
    DInfty × ℝ}

/-- **`D` is injective on `\widetilde{𝔼₀}` and `D(\widetilde{𝔼₀}) = J⁺(Δ)`** (`RamcovGX.tex:2249`). -/
theorem btz_dev_injective_range (hv : 0 < v.2.1) :
    Injective (btzDevM x₀ v ∘ Φ) ∧
      range (btzDevM x₀ v ∘ Φ) = (Causal.minkowski 2).Jplus ⊤ (btzLine x₀) :=
  ⟨(btzDevM_injective x₀ hv).comp Φ.injective, by
    rw [range_comp, Φ.range_coe, image_univ, range_btzDevM x₀ hv]⟩

/-- **`T_BTZ` on `\widetilde{𝔼₀}` is the coarsest topology finer than the natural one making `D`
continuous**, and it is the topology generated by the natural one and the sets
`U_λ = {rθ² < λ}` (`sec:mot_BTZ`, `RamcovGX.tex:2245`). -/
theorem btzTop_eq (hv : 0 < v.2.1) :
    TopologicalSpace.induced Φ hornTop = weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2)
      (BTZModel α) y₀ ⊓ TopologicalSpace.induced (btzDevM x₀ v ∘ Φ) inferInstance ∧
    TopologicalSpace.induced Φ hornTop = weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2)
      (BTZModel α) y₀ ⊓ TopologicalSpace.generateFrom
        {s | ∃ l : ℝ, 0 < l ∧ s = Φ ⁻¹' {y | hornFn y < l}} := by
  constructor
  · rw [hornTop_eq_inf_induced x₀ hv, induced_inf, Φ.induced_eq, induced_compose]
  · rw [hornTop_eq_btzGenTop, induced_inf, Φ.induced_eq, induced_generateFrom_eq]
    congr 2
    ext s
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨_, ⟨l, hl, rfl⟩, rfl⟩

/-- **`Aut(\widetilde{𝔼₀})` acts `T_BTZ`-continuously** (`sec:mot_BTZ`, `RamcovGX.tex:1955`, "elements
of `Aut(\widetilde{BTZ})` are `T`-continuous"): every homeomorphism of `\widetilde{𝔼₀}` which is an
a.e. automorphism of `p^*B` (`aeAutMapsMax`). Transported to the cylinder it is an a.e. automorphism
of the BTZ structure there, hence `D`-equivariant (`btzDevM_comp_eq_of`) and `hornTop`-continuous
(`continuous_hornTop_of_isAEMorphismOf`). -/
theorem btz_aut_continuous (hv : 0 < v.2.1) (hπ : IsBTZStructure x₀ v α)
    (hΦ : ∀ e, orbitMk (GammaA α) (Φ e) = e.base) {f}
    (hf : f ∈ aeAutMapsMax (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) y₀) :
    Continuous[TopologicalSpace.induced Φ hornTop, TopologicalSpace.induced Φ hornTop] f := by
  obtain ⟨φ, rfl, hφ⟩ := hf
  haveI : LocPathConnectedSpace (DInfty × ℝ) := locPathConnectedSpace_prod_of
  haveI : LocPathConnectedSpace (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
    (BTZModel α)) y₀) := Φ.isOpenEmbedding.locPathConnectedSpace
  have hD := isLocalHomeomorphOn_btzDevM x₀ hv
  have hP := DInfty.isPortly_pos ℝ
  set A := maximalAEAtlas (Causal.Flat.isom 2) (devAtlas (Causal.Flat.isom 2) (btzDevM x₀ v)
    (cylPos ℝ))
  have hdevA : IsMaximalAEAtlas (Causal.Flat.isom 2) A :=
    (isAEAtlas_devAtlas (G := Causal.Flat.isom 2) hP hD).isMaximalAEAtlas_maximalAEAtlas
  have hloc : IsAELocalHomeomorph A Φ := by
    refine ⟨Φ ⁻¹' support A, support A, ?_, hdevA.1.2, subset_rfl, fun x hx => hx,
      Φ.isLocalHomeomorph.isLocalHomeomorphOn⟩
    rw [← Φ.image_symm]
    exact hdevA.1.2.image_of_isOpenMap Φ.symm.continuous Φ.symm.isOpenMap Φ.symm.surjective
  have hspec := aePullback_spec_of_isAELocalHomeomorph hdevA.1 Φ.continuous hloc
  have hbase : (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
      (BTZModel α)) y₀ → BTZModel α) = orbitMk (GammaA α) ∘ Φ := funext fun e => (hΦ e).symm
  have hb := hπ.comp hspec.2
  rw [← hbase] at hb
  have heq := eq_aePullback hspec.1 hb
  rw [← heq] at hφ
  have hsymm := IsAEMorphismOf.symm_of_homeomorph hspec.1 hdevA hspec.2
  set ψ : DInfty × ℝ ≃ₜ DInfty × ℝ := (Φ.symm.trans φ).trans Φ
  have hψ : IsAEMorphismOf (Causal.Flat.isom 2) A A ψ := hspec.2.comp (hφ.comp hsymm)
  have hcont := continuous_hornTop_of_isAEMorphismOf x₀ hv ψ hψ
  refine continuous_induced_rng.2 ?_
  have : (Φ : _ → DInfty × ℝ) ∘ φ = ψ ∘ Φ := funext fun e => by
    show Φ (φ e) = Φ (φ (Φ.symm (Φ e)))
    rw [Φ.symm_apply_apply]
  rw [this]
  exact @Continuous.comp _ _ _ (TopologicalSpace.induced Φ hornTop) hornTop hornTop _ _ hcont
    continuous_induced_dom

/-- **The BTZ model satisfies the model hypothesis of `theo:local_virt_tame`**: `\widetilde{𝔼₀}`
carries a tamifying topology (`T_BTZ`) for which `Aut(\widetilde{𝔼₀})` acts continuously. -/
theorem btz_hasAutContinuousTamifying (hv : 0 < v.2.1) (hα : α ≠ 0) (hπ : IsBTZStructure x₀ v α) :
    HasAutContinuousTamifying (Causal.Flat.isom 2) (Causal.Minkowski 2) (BTZModel α) := by
  obtain ⟨y₀⟩ := btz_exists_reg hv hα hπ
  obtain ⟨Φ, hΦ⟩ := btz_exists_homeomorph hv hα hπ y₀
  exact ⟨y₀, _, btz_isTamifyingTopology hv hα hπ hΦ, fun f hf => btz_aut_continuous hv hπ hΦ hf⟩

end CoverFacts

/-! ### The paper's `𝔼₀`: `α = 2π`, `x₀ = 0`, `v = (−1, 1, 0)` -/

section E0

/-- The paper's `v = (−1, 1, 0)` (null coordinates): `btzDev 0 btzV0` is the paper's `D` of
`sec:mot_BTZ` (`btzDev_paper_coords`). -/
def btzV0 : ℝ × ℝ × ℝ := (-1, 1, 0)

theorem btzV0_pos : 0 < btzV0.2.1 := one_pos

/-- **The paper's developing map** (`RamcovGX.tex:1947`, `2237`, with D-5's `θ ∈ ℝ`), in
`lean-causal`'s Minkowski coordinates `(t, (x, y))`: at the cylinder point `(r, θ, 2τ)`,
`D = (τ + ½rθ², (τ + ½rθ² − r, rθ))` — the printed `(τ + ½rθ², τ + ½rθ² − r, −rθ)` after the
cylinder map `θ ↦ −θ` (`btzPaperDev_eq_btzDevM`; not a spatial reflection, which `Isom₀` lacks) — and
on the axis `D(τ, 0, ·) = (τ, (τ, 0))`. -/
theorem btzDevM_paper_coords {r : ℝ} (hr : 0 < r) (θ τ : ℝ) :
    btzDevM 0 btzV0 (DInfty.posEmb ⟨(r, θ), hr⟩, 2 * τ) =
      (τ + 1 / 2 * r * θ ^ 2, WithLp.toLp 2 ![τ + 1 / 2 * r * θ ^ 2 - r, r * θ]) ∧
    btzDevM 0 btzV0 (DInfty.apex, 2 * τ) = (τ, WithLp.toLp 2 ![τ, 0]) := by
  refine ⟨?_, ?_⟩
  · rw [btzDevM, btzDev_coords, nullToMink_apply]
    simp only [DInfty.posEmb_r, DInfty.posEmb_θ, btzV0, Prod.fst_zero, Prod.snd_zero]
    refine Prod.ext (by ring) ?_
    ext i; fin_cases i
    · simp; ring
    · simp
  · rw [btzDevM_apex, nullToMink_apply]
    simp only [nullU]
    refine Prod.ext (by simp) ?_
    ext i; fin_cases i <;> simp

/-! ### The metric of `𝔼₀`: `D^*(−dt² + dx² + dy²) = −2dτdr + dr² + r²dθ²`

The paper defines `𝔼₀` as `ℝ³` with the singular structure *induced by the flat metric*
`−2dτdr + dr² + r²dθ²` in cylindrical coordinates (`RamcovGX.tex:1944`), and gives the developing
map `D` (l.1947). Here `D` is written in the paper's own coordinates `(τ, r, θ)` (`btzPaperDev`), it is
the formal developing map `btzDevM 0 btzV0` read through the cylinder map `(τ, r, θ) ↦ (r, −θ, 2τ)`
(`btzPaperDev_eq_btzDevM`, `btzPaperDev_axis`), and its derivative pulls the Minkowski form back to the
printed metric at **every** point (`btzPaperDev_pullback_minkB`, `btzPaperDev_pullback`): the
structure developed by `D` on `{r > 0}` (`IsBTZStructure`) is the one whose charts are local
isometries of the printed metric. -/

/-- **The paper's developing map in its own cylindrical coordinates** `p = (τ, r, θ)`
(`RamcovGX.tex:1947`, `2237`, with D-5's `θ ∈ ℝ`): `(t, (x, y)) = (τ + ½rθ², (τ + ½rθ² − r, −rθ))`,
verbatim, a polynomial map `ℝ³ → 𝐌³`. -/
noncomputable def btzPaperDev (p : ℝ × ℝ × ℝ) : Causal.Minkowski 2 :=
  (p.1 + 1 / 2 * p.2.1 * p.2.2 ^ 2,
    WithLp.toLp 2 ![p.1 + 1 / 2 * p.2.1 * p.2.2 ^ 2 - p.2.1, -(p.2.1 * p.2.2)])

/-- `btzPaperDev` in gx's null coordinates (`btzPaperDev_eq_nullToMink`). -/
def btzPaperNull (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (2 * p.1 + p.2.1 * p.2.2 ^ 2 - p.2.1, p.2.1, -(p.2.1 * p.2.2))

theorem btzPaperDev_eq_nullToMink (p : ℝ × ℝ × ℝ) :
    btzPaperDev p = nullToMink (btzPaperNull p) := by
  rw [nullToMink_apply, btzPaperDev, btzPaperNull]
  refine Prod.ext (by simp only; ring) ?_
  ext i; fin_cases i
  · simp; ring
  · simp

/-- **The paper's `D` is the formal developing map** read through the cylinder map
`(τ, r, θ) ↦ (r, −θ, 2τ)` (on `{r > 0}`; on the axis `btzPaperDev_axis`). The map `θ ↦ −θ` conjugates
`Γ_α` to itself (`k ↦ k⁻¹`), so the printed sign of `y` is the orientation of `θ`; no choice of `v`
realises it with `θ` unchanged (`Isom₀` has no reflection `y ↦ −y`). -/
theorem btzPaperDev_eq_btzDevM {r : ℝ} (hr : 0 < r) (θ τ : ℝ) :
    btzPaperDev (τ, r, θ) = btzDevM 0 btzV0 (DInfty.posEmb ⟨(r, -θ), hr⟩, 2 * τ) := by
  rw [(btzDevM_paper_coords hr (-θ) τ).1, btzPaperDev]
  refine Prod.ext (by simp only; ring) ?_
  ext i; fin_cases i
  · simp
  · simp

/-- On the axis: `D(τ, 0, θ) = (τ, (τ, 0))` (`RamcovGX.tex:1947`). -/
theorem btzPaperDev_axis (θ τ : ℝ) :
    btzPaperDev (τ, 0, θ) = btzDevM 0 btzV0 (DInfty.apex, 2 * τ) := by
  rw [(btzDevM_paper_coords one_pos θ τ).2, btzPaperDev]
  refine Prod.ext (by simp) ?_
  ext i; fin_cases i <;> simp

/-- The derivative of `btzPaperNull`, explicitly. -/
theorem hasFDerivAt_btzPaperNull (p : ℝ × ℝ × ℝ) :
    ∃ L : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ), HasFDerivAt btzPaperNull L p ∧ ∀ h, L h =
      (2 * h.1 + h.2.1 * p.2.2 ^ 2 + 2 * p.2.1 * p.2.2 * h.2.2 - h.2.1, h.2.1,
        -(h.2.1 * p.2.2 + p.2.1 * h.2.2)) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hr : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.fst
  have hθ : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.snd
  have H := (((h1.const_mul 2).add (hr.mul (hθ.pow 2))).sub hr).prodMk (hr.prodMk (hr.mul hθ).neg)
  refine ⟨_, H, fun h => ?_⟩
  ext <;> simp <;> ring

/-- `dD_p(h)`, explicitly (in null coordinates). -/
theorem fderiv_btzPaperDev_apply (p h : ℝ × ℝ × ℝ) :
    fderiv ℝ btzPaperDev p h = nullToMink
      (2 * h.1 + h.2.1 * p.2.2 ^ 2 + 2 * p.2.1 * p.2.2 * h.2.2 - h.2.1, h.2.1,
        -(h.2.1 * p.2.2 + p.2.1 * h.2.2)) := by
  obtain ⟨L, hL, hLh⟩ := hasFDerivAt_btzPaperNull p
  have hfun : btzPaperDev = (LinearMap.toContinuousLinearMap
      (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)) ∘ btzPaperNull :=
    funext fun q => btzPaperDev_eq_nullToMink q
  have H := (LinearMap.toContinuousLinearMap
      (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).hasFDerivAt.comp p hL
  rw [hfun, H.fderiv, ContinuousLinearMap.comp_apply, hLh]
  rfl

/-- **`D^*⟨·|·⟩` is the printed metric tensor** (`RamcovGX.tex:1944`): at `p = (τ, r, θ)`, for
`h, k` tangent vectors `(dτ, dr, dθ)`, `⟨dD h | dD k⟩ = −(dτ_h dr_k + dr_h dτ_k) + dr_h dr_k +
r² dθ_h dθ_k`. -/
theorem btzPaperDev_pullback_minkB (p h k : ℝ × ℝ × ℝ) :
    Causal.Flat.minkB (fderiv ℝ btzPaperDev p h) (fderiv ℝ btzPaperDev p k) =
      -(h.1 * k.2.1 + h.2.1 * k.1) + h.2.1 * k.2.1 + p.2.1 ^ 2 * (h.2.2 * k.2.2) := by
  rw [fderiv_btzPaperDev_apply, fderiv_btzPaperDev_apply, nullToMink_apply, nullToMink_apply]
  simp [Causal.Flat.minkB, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **`D^*(−dt² + dx² + dy²) = −2dτdr + dr² + r²dθ²`** (`RamcovGX.tex:1944`, read `r²dθ²`: the
printed `r²dθ` is not a quadratic form). -/
theorem btzPaperDev_pullback (p h : ℝ × ℝ × ℝ) :
    Causal.Flat.minkQ (fderiv ℝ btzPaperDev p h) =
      -2 * h.1 * h.2.1 + h.2.1 ^ 2 + p.2.1 ^ 2 * h.2.2 ^ 2 := by
  rw [Causal.Flat.minkQ_eq_minkB, btzPaperDev_pullback_minkB]; ring

theorem btz_two_pi_ne_zero : (2 * π : ℝ) ≠ 0 := by positivity

/-- **The BTZ model space `𝔼₀`** (`sec:mot_BTZ`, `RamcovGX.tex:1944`): `Γ_{2π}\(𝔻_∞ × ℝ)` with the
structure developed by the paper's `D`, whose pullback of the Minkowski metric is the printed
`−2dτdr + dr² + r²dθ²` (`btzPaperDev_pullback`). -/
abbrev BTZE0 : Type := BTZModel (2 * π)

/-- The structure of `𝔼₀` (the unique one making it the BTZ model, `btz_existsUnique`). -/
@[reducible] noncomputable def btzE0Structure :
    SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
  Classical.choose (exists_isBTZStructure (α := 2 * π) 0 btzV0_pos btz_two_pi_ne_zero)

theorem isBTZStructure_btzE0 : @IsBTZStructure 0 btzV0 (2 * π) btzE0Structure :=
  Classical.choose_spec (exists_isBTZStructure (α := 2 * π) 0 btzV0_pos btz_two_pi_ne_zero)

/-- **`prop:BTZ_virt_tame`** (`RamcovGX.tex:2252`) for the paper's `𝔼₀` itself. -/
theorem btzE0_virt_tame :
    letI := btzE0Structure
    IsVirtuallyTame (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
  letI := btzE0Structure
  btz_virt_tame (x₀ := 0) btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0

end E0

end GX
