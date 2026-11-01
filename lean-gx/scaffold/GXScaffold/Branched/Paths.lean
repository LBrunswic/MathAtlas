import GX.Branched.Universality

/-!
# Paths and the maximal branched covering possibly branched over `S` (§3.3)

Package WP-26e. `papers/gx`, `RamcovGX.tex:1189–1416`. Every label from `def:almost_trivial_loop`
to `prop:general_fiber_path_universal` is proved under the homotopy reading of "connected
component of `Ω(x,x,U)`" (SCOPE (a)) or the readings (b)–(g); none of them is marked except the
remark, because those readings await a ruling. The last example uses none of them.

* `def:almost_trivial_loop` — `RamcovGX.tex:1210`: `GX.MemOmega` (`Ω(x,y,U)`),
  `GX.OmegaHomotopic`, `GX.AlmostTrivial`; the literal form `GX.AlmostTrivialCC` (compact-open
  `GX.OmegaSet`) is implied, `GX.AlmostTrivial.almostTrivialCC`.
* `ex:consider_carthesian_coordinates_usual` — `RamcovGX.tex:1214` (partial): `GX.cartS₁`,
  `GX.cartS₂`, `GX.IsHomTrivial`, `GX.IsHomTrivial.almostTrivial`; proved: the second claim
  `GX.carthesian_S₁_trivial` and the first for `S₁`, `GX.carthesian_piOne_S₁` (the winding number
  `GX.cartDeg`, through `GX.cWinding` on `ℂ ∖ {0}`); stated with tagged `sorry`: the first for
  `S₂`, the third and the fourth (`GX.carthesian_piOne_S₂`, `GX.carthesian_S₂_almostTrivial`,
  `GX.carthesian_S₂_not_trivial`).
* `def:almost_homotopic_paths` — `RamcovGX.tex:1262`: `GX.AlmostHomotopic` (`GX.AlmostHomotopic.mem`).
* **`rem:implicitely_two_almost_homotopic`** — `RamcovGX.tex:1268`: `GX.AlmostHomotopic.ends`.
* `lem:almost_homotopic_carac` — `RamcovGX.tex:1271`: `GX.almost_homotopic_carac` (with
  `GX.splice`), the strong form the later proofs use `GX.AlmostTrivial.exists_mid`.
* `lem:hausdorff_first_countable_connected` — `RamcovGX.tex:1290`:
  `GX.hausdorff_first_countable_connected` (`GX.almostHomotopic_refl`, `.symm`, `.trans`), through
  the germ form `GX.GermEquiv`, `GX.almostHomotopic_iff_germEquiv`.
* `lem:almost_homotopic_carac2` — `RamcovGX.tex:1306`: `GX.almost_homotopic_carac2`, for any
  maximal covering `GX.almost_homotopic_carac2_of_isMaximal`; lifts `GX.maxBranched_existsUnique_lift`;
  the two halves in general `GX.lift_end_eq_of_almostHomotopic`, `GX.almostHomotopic_of_lift_end_eq`;
  standard neighbourhoods `GX.IsStandardNbhd`, `GX.IsSpread.hasBasis_standardNbhd`.
* `theo:ramified_covering_path` — `RamcovGX.tex:1322`: `GX.ramified_covering_path`,
  `GX.omegaEnd_isBranchedCovering` (`GX.OmegaSpace`, `GX.OmegaRel`, `GX.OmegaQuot`, `GX.omegaEnd`;
  `ψ` continuous, open, onto: `GX.continuous_omegaLift_one`, `GX.isOpenMap_omegaLift_one`,
  `GX.surjective_omegaLift_one`); `Y ∖ S` semilocally simply connected added (finding).
* `def:covering_branched_two_paths` — `RamcovGX.tex:1385`: `GX.PHomotopic`, `GX.FreePath`.
* `prop:general_fiber_path` — `RamcovGX.tex:1390`: `GX.general_fiber_path` (`GX.PiOneP`,
  `GX.piOnePMap`, `GX.compOfClass`).
* `prop:general_fiber_path_universal` — `RamcovGX.tex:1399`: `GX.general_fiber_path_universal`
  (`GX.PiOneU`, `GX.FreeHomotopic`, `GX.piOneUMap`).
* **`ex:consider_fiber_above_homeomorphic`** — `RamcovGX.tex:1409`: `GX.fiber_above_homeomorphic`
  (`GX.fibS`, `GX.fibD`; the system `GX.fibS_tower`; limits of towers `GX.towerHomeomorph`;
  `GX.not_locallyCompactSpace_nat_pi`).

> A loop $\gamma\in \Omega(x,x,\U)$ is almost trivial with respect to $\U$ if its connected
> component in $\Omega(x,x,\U)$ intersects $\Omega(x,x,\V\cap \U)$ for all neighborhood $\V$ of $x$.
>
> Two paths $\gamma_1,\gamma_2 \in \Omega(x,y,\U)$ are almost homotopic with respect to $\U$ if
> the loop $(\gamma_2)^{-1}*\gamma_1$ is almost trivial with respect to $\U$.
>
> Then, $\varphi$ induces a branched covering $X \xrightarrow{\overline\varphi} Y$ isomorphic to
> $\widetilde Y^S \xrightarrow{p} Y$.
>
> Consider $Y = \RR^2$ and $S=\{(\frac{1}{n},0)~:~n\in \N^*\cup\{\infty\}\}$. The fiber above
> $(0,0)$ in $\widetilde Y^S$ is homeomorphic to $\mathbb Z^\N$ endowed with the weak topology;
> hence is not locally compact.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `def`/`lem:almost_homotopic_carac`/`lem:hausdorff…`: `X` Hausdorff, first countable, connected, LPC | ⚠ weakened: not used |
| `lem:almost_homotopic_carac`, `lem:hausdorff…`: `U` open | ⚠ weakened: not used |
| `lem:hausdorff…`: `(x,y) ∈ U × closure U` | ✓ `x ∈ U` carried; `y ∈ closure U` not used |
| `lem:almost_homotopic_carac2`: `\widetilde Y^S` maximal possibly branched over `S` | ⚠ `S` skeletal and `Y ∖ S` slsc (where `\widetilde Y^S` is defined, `prop:universality`); `Y` T2, LPC, first countable, connected |
| `theo:ramified_covering_path`: `Y` first countable, connected, LPC, Hausdorff; `S` skeletal | ✓ carried |
| `theo:ramified_covering_path`: (absent) | ⚠ strengthened: `Y ∖ S` semilocally simply connected (finding) |
| `prop:general_fiber_path`: `p` a covering branched over `S` | ✓ branched covering, a covering over `Y ∖ S` (`GX.isCoveringMap_restrict_compl`), `S` skeletal (as the branching locus is); `X` T2, LPC; `Y` T1, loc. connected |
| `prop:general_fiber_path_universal` | ✓ carried |
| `ex:consider_fiber_above_homeomorphic`: `Y = ℝ²` | ✓ `ℂ`; `S` skeletal and `ℂ ∖ S` slsc proved, not assumed |

## SCOPE (disclosed)

(a) "Same connected component of `Ω(x,y,U)`" is read as "homotopic with respect to `U`" (the
paper's "or, equivalently", l.1201; the proofs use homotopies). Only homotopic ⇒ same component
is proved (`GX.OmegaHomotopic.mem_connectedComponentIn`). (b) `*` is "any parameterization":
`GX.splice` keeps `γ` on `[0,t₀] ∪ [t₁,1]`. (c) "Standard neighbourhood" (l.1311): `GX.IsStandardNbhd`.
(d) `X` of `theo:ramified_covering_path` carries the quotient of the compact-open topology. (e)
The paths of `def:covering_branched_two_paths` and of `π₁(a,U)` lie in `Y ∖ S`; "up to homotopy"
is homotopy in `Y ∖ S` with free end in `U` (`GX.FreeHomotopic`). (f) `≃` of the fibre
propositions: an embedding onto the limit, the `π₁` discrete. (g) "Homotopically trivial"
(l.1219): `GX.IsHomTrivial`; `S₂` is read with `z = 0` on the sine graph.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X]

/-! ### Paths with interior in `U` -/

/-- `Ω_X(x, y, U)`: a path `γ : x ⇝ y` with `γ(]0,1[) ⊆ U`. -/
def MemOmega (U : Set X) {x y : X} (γ : Path x y) : Prop :=
  ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∈ U

/-- Two paths of `Ω(x,y,U)` are *homotopic with respect to `U`* (`RamcovGX.tex:1201`): a
homotopy `H` with fixed ends with `H([0,1] × ]0,1[) ⊆ U`. -/
def OmegaHomotopic (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∃ F : Path.Homotopy γ₁ γ₂, ∀ s t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → F (s, t) ∈ U

/-- Homotopic *in* `U`: a homotopy with fixed ends all of whose values lie in `U`. -/
def HomotopicIn (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∃ F : Path.Homotopy γ₁ γ₂, ∀ z, F z ∈ U

section Basic

variable {U : Set X} {x y z : X}

theorem OmegaHomotopic.memOmega_left {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    MemOmega U γ₁ := by
  obtain ⟨F, hF⟩ := h
  intro t h0 h1
  have := hF 0 t h0 h1
  rwa [F.apply_zero] at this

theorem OmegaHomotopic.memOmega_right {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    MemOmega U γ₂ := by
  obtain ⟨F, hF⟩ := h
  intro t h0 h1
  have := hF 1 t h0 h1
  rwa [F.apply_one] at this

theorem OmegaHomotopic.refl {γ : Path x y} (h : MemOmega U γ) : OmegaHomotopic U γ γ :=
  ⟨Path.Homotopy.refl γ, fun s t h0 h1 => by simpa using h t h0 h1⟩

theorem OmegaHomotopic.symm {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    OmegaHomotopic U γ₂ γ₁ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.symm, fun s t h0 h1 => by simpa using hF (σ s) t h0 h1⟩

theorem OmegaHomotopic.trans {γ₁ γ₂ γ₃ : Path x y} (h : OmegaHomotopic U γ₁ γ₂)
    (h' : OmegaHomotopic U γ₂ γ₃) : OmegaHomotopic U γ₁ γ₃ := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := h'
  refine ⟨F.trans G, fun s t h0 h1 => ?_⟩
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _ t h0 h1
  · exact hG _ t h0 h1

theorem HomotopicIn.omegaHomotopic {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) :
    OmegaHomotopic U γ₁ γ₂ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun s t _ _ => hF (s, t)⟩

theorem HomotopicIn.mem_left {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (t : I) :
    γ₁ t ∈ U := by
  obtain ⟨F, hF⟩ := h
  have := hF (0, t)
  rwa [F.apply_zero] at this

theorem HomotopicIn.mem_right {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (t : I) :
    γ₂ t ∈ U := by
  obtain ⟨F, hF⟩ := h
  have := hF (1, t)
  rwa [F.apply_one] at this

theorem HomotopicIn.refl {γ : Path x y} (h : ∀ t, γ t ∈ U) : HomotopicIn U γ γ :=
  ⟨Path.Homotopy.refl γ, fun z => by simpa using h z.2⟩

theorem HomotopicIn.symm {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) :
    HomotopicIn U γ₂ γ₁ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.symm, fun z => by simpa using hF (σ z.1, z.2)⟩

theorem HomotopicIn.trans {γ₁ γ₂ γ₃ : Path x y} (h : HomotopicIn U γ₁ γ₂)
    (h' : HomotopicIn U γ₂ γ₃) : HomotopicIn U γ₁ γ₃ := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := h'
  refine ⟨F.trans G, fun z => ?_⟩
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

theorem HomotopicIn.cast {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) {x' y' : X}
    (hx : x' = x) (hy : y' = y) : HomotopicIn U (γ₁.cast hx hy) (γ₂.cast hx hy) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.pathCast hx hy, fun z => hF z⟩

theorem HomotopicIn.of_eq {γ₁ γ₂ γ₁' γ₂' : Path x y} (h : HomotopicIn U γ₁ γ₂) (h₁ : γ₁ = γ₁')
    (h₂ : γ₂ = γ₂') : HomotopicIn U γ₁' γ₂' := h₁ ▸ h₂ ▸ h

theorem HomotopicIn.hcomp {p₀ q₀ : Path x y} {p₁ q₁ : Path y z} (h₀ : HomotopicIn U p₀ q₀)
    (h₁ : HomotopicIn U p₁ q₁) : HomotopicIn U (p₀.trans p₁) (q₀.trans q₁) := by
  obtain ⟨F, hF⟩ := h₀
  obtain ⟨G, hG⟩ := h₁
  refine ⟨F.hcomp G, fun w => ?_⟩
  rw [Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hF _
  · exact hG _

theorem HomotopicIn.mono {V : Set X} {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (hUV : U ⊆ V) :
    HomotopicIn V γ₁ γ₂ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun w => hUV (hF w)⟩

end Basic

/-! ### Paths in a subspace -/

section Sub

variable {U : Set X} {x y z : X}

/-- A path of `X` with values in `U`, as a path of the subspace `U`. -/
def pathToSub (γ : Path x y) (h : ∀ t, γ t ∈ U) :
    Path (⟨x, γ.source ▸ h 0⟩ : U) ⟨y, γ.target ▸ h 1⟩ where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp] theorem pathToSub_apply (γ : Path x y) (h : ∀ t, γ t ∈ U) (t : I) :
    (pathToSub γ h t : X) = γ t := rfl

theorem pathToSub_trans (γ : Path x y) (γ' : Path y z) (h : ∀ t, γ t ∈ U) (h' : ∀ t, γ' t ∈ U)
    (h'' : ∀ t, (γ.trans γ') t ∈ U) :
    pathToSub (γ.trans γ') h'' = (pathToSub γ h).trans (pathToSub γ' h') := by
  ext t
  simp only [pathToSub_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem pathToSub_symm (γ : Path x y) (h : ∀ t, γ t ∈ U) (h' : ∀ t, γ.symm t ∈ U) :
    pathToSub γ.symm h' = (pathToSub γ h).symm := by
  ext t
  rfl

theorem pathToSub_cast (γ : Path x y) (h : ∀ t, γ t ∈ U) {x' y' : X} (hx : x' = x)
    (hy : y' = y) (h' : ∀ t, (γ.cast hx hy) t ∈ U) :
    pathToSub (γ.cast hx hy) h' = (pathToSub γ h).cast (Subtype.ext hx) (Subtype.ext hy) := by
  ext t
  rfl

theorem homotopicIn_iff {γ₁ γ₂ : Path x y} :
    HomotopicIn U γ₁ γ₂ ↔ ∃ (h₁ : ∀ t, γ₁ t ∈ U) (h₂ : ∀ t, γ₂ t ∈ U),
      (pathToSub γ₁ h₁).Homotopic (pathToSub γ₂ h₂) := by
  constructor
  · intro h
    refine ⟨h.mem_left, h.mem_right, ?_⟩
    obtain ⟨F, hF⟩ := h
    exact ⟨{ toFun := fun w => ⟨F w, hF w⟩
             continuous_toFun := F.continuous.subtype_mk _
             map_zero_left := fun t => Subtype.ext (F.apply_zero t)
             map_one_left := fun t => Subtype.ext (F.apply_one t)
             prop' := fun s t ht => Subtype.ext (F.eq_fst s ht) }⟩
  · rintro ⟨h₁, h₂, ⟨G⟩⟩
    have e₁ : (pathToSub γ₁ h₁).map continuous_subtype_val = γ₁ := by ext; rfl
    have e₂ : (pathToSub γ₂ h₂).map continuous_subtype_val = γ₂ := by ext; rfl
    refine ⟨(G.map ⟨Subtype.val, continuous_subtype_val⟩).cast e₁ e₂, fun w => ?_⟩
    exact (G w).2

end Sub

/-! ### Straight-line homotopies, sub-paths, splicing -/

section Line

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- The straight-line homotopy between two paths of a real topological vector space. -/
def lineHomotopy {a b : E} (α β : Path a b) : Path.Homotopy α β where
  toFun w := AffineMap.lineMap (α w.2) (β w.2) (w.1 : ℝ)
  continuous_toFun := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with rfl | rfl <;> simp

theorem lineHomotopy_apply {a b : E} (α β : Path a b) (w : I × I) :
    lineHomotopy α β w = AffineMap.lineMap (α w.2) (β w.2) (w.1 : ℝ) := rfl

/-- Two paths of a convex `A` with the same ends have homotopic images under any `F`, the
homotopy taking its values in `F(A)`. -/
theorem homotopicIn_map_of_convex {U : Set X} {a b : E} (α β : Path a b) {A : Set E}
    (hA : Convex ℝ A) (hα : ∀ t, α t ∈ A) (hβ : ∀ t, β t ∈ A) {F : E → X} (hF : Continuous F)
    (hFA : ∀ e ∈ A, F e ∈ U) : HomotopicIn U (α.map hF) (β.map hF) :=
  ⟨(lineHomotopy α β).map ⟨F, hF⟩, fun w => hFA _ (hA.lineMap_mem (hα w.2) (hβ w.2) w.1.2)⟩

end Line

section Splice

variable {U : Set X} {x y z : X}

/-- The sub-path `γ_{|[a,b]}` (affinely reparametrised; `a`, `b` in any order). -/
def subpath (γ : Path x y) (a b : I) : Path (γ a) (γ b) :=
  ((Path.segment (a : ℝ) (b : ℝ)).map γ.continuous_extend).cast (γ.extend_extends' a).symm
    (γ.extend_extends' b).symm

theorem subpath_apply (γ : Path x y) (a b : I) (t : I) :
    subpath γ a b t = γ.extend (AffineMap.lineMap (a : ℝ) (b : ℝ) (t : ℝ)) := rfl

theorem subpath_apply' (γ : Path x y) (a b : I) (t : I) :
    subpath γ a b t = γ.extend ((1 - (t : ℝ)) * a + t * b) := by
  rw [subpath_apply, AffineMap.lineMap_apply_module]
  simp [smul_eq_mul]

/-- The values of a sub-path lie in the image of the interval between its ends. -/
theorem subpath_mem (γ : Path x y) (a b : I) (t : I) :
    ∃ s : I, min (a : ℝ) b ≤ s ∧ (s : ℝ) ≤ max (a : ℝ) b ∧ subpath γ a b t = γ s := by
  set r : ℝ := (1 - (t : ℝ)) * a + t * b with hr
  have ht0 := t.2.1
  have ht1 := t.2.2
  have h1 : min (a : ℝ) b ≤ r := by
    rcases le_total (a : ℝ) b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have h2 : r ≤ max (a : ℝ) b := by
    rcases le_total (a : ℝ) b with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hrI : r ∈ I := ⟨le_trans (le_min a.2.1 b.2.1) h1, h2.trans (max_le a.2.2 b.2.2)⟩
  refine ⟨⟨r, hrI⟩, h1, h2, ?_⟩
  rw [subpath_apply', Path.extend_apply γ hrI]

/-- The head `γ_{|[0,s]}` of a path, from `x`. -/
def head (γ : Path x y) (s : I) : Path x (γ s) :=
  (subpath γ 0 s).cast γ.source.symm rfl

theorem head_apply (γ : Path x y) (s t : I) : head γ s t = subpath γ 0 s t := rfl

/-- Reparametrising a path inside an interval on which it stays in `U` is a homotopy in `U`. -/
theorem homotopicIn_reparam (γ : Path x y) {a b : ℝ} (α β : Path a b) {A : Set ℝ}
    (hA : Convex ℝ A) (hα : ∀ t, α t ∈ A) (hβ : ∀ t, β t ∈ A) (hγA : ∀ r ∈ A, γ.extend r ∈ U) :
    HomotopicIn U (α.map γ.continuous_extend) (β.map γ.continuous_extend) :=
  homotopicIn_map_of_convex α β hA hα hβ γ.continuous_extend hγA

end Splice

section Splice2

variable {U : Set X} {x y z : X}

theorem subpath_trans_homotopicIn (γ : Path x y) (a b c : I)
    (hU : ∀ r : ℝ, min (min (a : ℝ) b) c ≤ r → r ≤ max (max (a : ℝ) b) c → γ.extend r ∈ U) :
    HomotopicIn U (subpath γ a c) ((subpath γ a b).trans (subpath γ b c)) := by
  set A : Set ℝ := Icc (min (min (a : ℝ) b) c) (max (max (a : ℝ) b) c)
  have hAc : Convex ℝ A := convex_Icc _ _
  have ha : (a : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hb : (b : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hc : (c : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hseg : ∀ {p q : ℝ}, p ∈ A → q ∈ A → ∀ t, Path.segment p q t ∈ A := fun hp hq t => by
    rw [Path.segment_apply]; exact hAc.lineMap_mem hp hq t.2
  have h := homotopicIn_reparam γ (Path.segment (a : ℝ) c)
    ((Path.segment (a : ℝ) b).trans (Path.segment (b : ℝ) c)) hAc (hseg ha hc)
    (fun t => by
      rw [Path.trans_apply]; split_ifs
      · exact hseg ha hb _
      · exact hseg hb hc _) (fun r hr => hU r hr.1 hr.2)
  have h' := h.cast (γ.extend_extends' a).symm (γ.extend_extends' c).symm
  refine h'.of_eq rfl ?_
  ext t
  simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- The function underlying a splice, for a family parametrised by `Q`. -/
def spliceFun {Q : Type*} (g : Q × I → X) (w : Q × I → X) (t₀ t₁ : I) (z : Q × I) : X :=
  if (z.2 : ℝ) ≤ t₀ then g z
  else if (z.2 : ℝ) ≤ t₁ then w (z.1, Set.projIcc 0 1 zero_le_one ((z.2 - t₀) / (t₁ - t₀)))
  else g z

theorem projIcc_div_self {t₀ t₁ : ℝ} (h : t₀ < t₁) :
    Set.projIcc (0 : ℝ) 1 zero_le_one ((t₁ - t₀) / (t₁ - t₀)) = 1 := by
  rw [div_self (sub_ne_zero.2 h.ne')]
  exact Subtype.ext (by simp)

theorem projIcc_sub_self_div (t₀ t₁ : ℝ) :
    Set.projIcc (0 : ℝ) 1 zero_le_one ((t₀ - t₀) / (t₁ - t₀)) = 0 := by
  rw [sub_self, zero_div]
  exact Subtype.ext (by simp)

theorem continuous_spliceFun {Q : Type*} [TopologicalSpace Q] {g w : Q × I → X}
    (hg : Continuous g) (hw : Continuous w) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (h0 : ∀ q, w (q, 0) = g (q, t₀)) (h1 : ∀ q, w (q, 1) = g (q, t₁)) :
    Continuous (spliceFun g w t₀ t₁) := by
  have hproj : Continuous fun z : Q × I =>
      w (z.1, Set.projIcc 0 1 zero_le_one (((z.2 : ℝ) - t₀) / (t₁ - t₀))) :=
    hw.comp (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hinner : Continuous fun z : Q × I =>
      if (z.2 : ℝ) ≤ t₁ then w (z.1, Set.projIcc 0 1 zero_le_one ((z.2 - t₀) / (t₁ - t₀)))
      else g z := by
    refine Continuous.if_le hproj hg (by fun_prop) continuous_const fun z hz => ?_
    rw [hz, projIcc_div_self h, h1]
    congr 1
    exact Prod.ext rfl (Subtype.ext hz.symm)
  refine Continuous.if_le hg hinner (by fun_prop) continuous_const fun z hz => ?_
  rw [if_pos (hz.le.trans h.le), hz, projIcc_sub_self_div, h0]
  congr 1
  exact Prod.ext rfl (Subtype.ext hz)

/-- `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`, in the parametrisation keeping `γ` on `[0,t₀] ∪ [t₁,1]`
and running `ω` on `[t₀,t₁]` (the paper's `*` is "any parameterization",
`RamcovGX.tex:1204`). -/
def splice (γ : Path x y) (t₀ t₁ : I) (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁)) :
    Path x y where
  toFun t := spliceFun (fun z : Unit × I => γ z.2) (fun z => ω z.2) t₀ t₁ ((), t)
  continuous_toFun := (continuous_spliceFun (by fun_prop) (by fun_prop) h (fun _ => ω.source)
    (fun _ => ω.target)).comp (by fun_prop)
  source' := by
    simp only [spliceFun, Icc.coe_zero, if_pos t₀.2.1, γ.source]
  target' := by
    simp only [spliceFun, Icc.coe_one]
    have h1 : ¬ (1 : ℝ) ≤ t₀ := fun h' => absurd (h'.trans_lt h) (not_lt.2 t₁.2.2)
    rw [if_neg h1]
    split_ifs with h2
    · have : (t₁ : ℝ) = 1 := le_antisymm t₁.2.2 h2
      have ht₁ : t₁ = 1 := Subtype.ext this
      have e : (1 - (t₀ : ℝ)) / (t₁ - t₀) = (t₁ - t₀) / (t₁ - t₀) := by rw [this]
      rw [e, projIcc_div_self h, ω.target, ht₁, γ.target]
    · exact γ.target

theorem splice_apply (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁))
    (t : I) : splice γ t₀ t₁ h ω t =
      spliceFun (fun z : Unit × I => γ z.2) (fun z => ω z.2) t₀ t₁ ((), t) := rfl

theorem splice_apply_of_le (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t : ℝ) ≤ t₀) : splice γ t₀ t₁ h ω t = γ t := by
  rw [splice_apply]
  simp only [spliceFun, if_pos ht]

theorem splice_apply_of_ge (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t₁ : ℝ) ≤ t) : splice γ t₀ t₁ h ω t = γ t := by
  rw [splice_apply]
  simp only [spliceFun, if_neg (not_le.2 (h.trans_le ht))]
  split_ifs with h2
  · have : (t : ℝ) = t₁ := le_antisymm h2 ht
    rw [this, projIcc_div_self h, ω.target]
    congr 1; exact Subtype.ext this.symm
  · rfl

theorem splice_apply_mid (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t₀ : ℝ) < t) (ht' : (t : ℝ) ≤ t₁) :
    splice γ t₀ t₁ h ω t = ω (Set.projIcc 0 1 zero_le_one ((t - t₀) / (t₁ - t₀))) := by
  rw [splice_apply]
  simp only [spliceFun, if_neg (not_le.2 ht), if_pos ht']

theorem projIcc_mid {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t₀ ≤ t) (ht' : t ≤ t₁) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one ((t - t₀) / (t₁ - t₀)) : I) : ℝ) = (t - t₀) / (t₁ - t₀) := by
  have hd : 0 < t₁ - t₀ := sub_pos.2 h
  rw [Set.projIcc_of_mem]
  exact ⟨div_nonneg (sub_nonneg.2 ht) hd.le, (div_le_one hd).2 (by linarith)⟩

/-- The values of a splice. -/
theorem splice_mem (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁))
    (t : I) : ((t : ℝ) ≤ t₀ ∧ splice γ t₀ t₁ h ω t = γ t) ∨
      ((t₁ : ℝ) ≤ t ∧ splice γ t₀ t₁ h ω t = γ t) ∨ splice γ t₀ t₁ h ω t ∈ range ω := by
  rcases le_or_gt (t : ℝ) t₀ with h1 | h1
  · exact Or.inl ⟨h1, splice_apply_of_le γ h ω h1⟩
  rcases le_or_gt (t : ℝ) t₁ with h2 | h2
  · exact Or.inr (Or.inr ⟨_, (splice_apply_mid γ h ω h1 h2).symm⟩)
  · exact Or.inr (Or.inl ⟨h2.le, splice_apply_of_ge γ h ω h2.le⟩)

/-- Splicing `γ`'s own sub-path gives `γ` back. -/
theorem splice_subpath (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) :
    splice γ t₀ t₁ h (subpath γ t₀ t₁) = γ := by
  ext t
  rcases le_or_gt (t : ℝ) t₀ with h1 | h1
  · exact splice_apply_of_le γ h _ h1
  rcases le_or_gt (t : ℝ) t₁ with h2 | h2
  · rw [splice_apply_mid γ h _ h1 h2, subpath_apply', projIcc_mid h h1.le h2]
    have hd : (t₁ : ℝ) - t₀ ≠ 0 := sub_ne_zero.2 h.ne'
    have : (1 - ((t : ℝ) - t₀) / (t₁ - t₀)) * t₀ + ((t : ℝ) - t₀) / (t₁ - t₀) * t₁ = t := by
      field_simp; ring
    rw [this, Path.extend_apply γ t.2]
  · exact splice_apply_of_ge γ h _ h2.le

/-- **The splice lemma.** If the middle `γ_{|[t₀,t₁]}` of `γ ∈ Ω(x,y,U)` is homotopic in `U` to
`ω`, then `γ` is homotopic with respect to `U` to `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`. -/
theorem splice_omegaHomotopic {γ : Path x y} (hγ : MemOmega U γ) {t₀ t₁ : I}
    (h : (t₀ : ℝ) < t₁) (h1 : (t₁ : ℝ) < 1) {ω : Path (γ t₀) (γ t₁)}
    (hω : HomotopicIn U (subpath γ t₀ t₁) ω) : OmegaHomotopic U γ (splice γ t₀ t₁ h ω) := by
  obtain ⟨G, hG⟩ := hω
  have hc := continuous_spliceFun (g := fun z : I × I => γ z.2) (w := fun z => G z)
    (by fun_prop) G.continuous h (fun q => G.source q) (fun q => G.target q)
  have e0 : ∀ t, spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (0, t) = γ t := by
    intro t
    conv_rhs => rw [← splice_subpath γ h]
    simp only [splice, spliceFun, Path.coe_mk_mk]
    split_ifs
    · rfl
    · rw [G.apply_zero]; rfl
    · rfl
  have e1 : ∀ t, spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (1, t) =
      splice γ t₀ t₁ h ω t := by
    intro t
    simp only [splice, spliceFun, Path.coe_mk_mk]
    split_ifs
    · rfl
    · rw [G.apply_one]; rfl
    · rfl
  refine ⟨{ toFun := spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁
            continuous_toFun := hc
            map_zero_left := e0
            map_one_left := e1
            prop' := fun s t ht => ?_ }, fun s t ht0 ht1 => ?_⟩
  · rcases ht with rfl | rfl
    · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, 0) = γ 0
      simp only [spliceFun, Icc.coe_zero, if_pos t₀.2.1]
    · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, 1) = γ 1
      simp only [spliceFun, Icc.coe_one, if_neg (not_le.2 (h.trans h1)), if_neg (not_le.2 h1)]
  · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, t) ∈ U
    simp only [spliceFun]
    split_ifs
    · exact hγ t ht0 ht1
    · exact hG _
    · exact hγ t ht0 ht1

end Splice2

/-! ### Tails of paths, and the tube lemma -/

section Tails

variable {x y : X}

/-- A path stays in a neighbourhood of its origin for small times. -/
theorem exists_head_mem (γ : Path x y) {V : Set X} (hV : V ∈ 𝓝 x) {c : ℝ} (hc : 0 < c) :
    ∃ t₀ : I, 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < c ∧ ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V := by
  have h : ∀ᶠ t in 𝓝 (0 : I), γ t ∈ V :=
    γ.continuous.continuousAt.preimage_mem_nhds (by rw [γ.source]; exact hV)
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff.1 h
  set r : ℝ := min ε (min c 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < ε := by rw [hr]; linarith [min_le_left ε (min c 1)]
  have hrc : r < c := by rw [hr]; linarith [min_le_right ε (min c 1), min_le_left c 1]
  have hr2 : r ≤ 1 := by rw [hr]; linarith [min_le_right ε (min c 1), min_le_right c 1]
  refine ⟨⟨r, hr0.le, hr2⟩, hr0, hrc, fun t ht => hεV ?_⟩
  rw [Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
  exact lt_of_le_of_lt ht hr1

/-- A path stays in a neighbourhood of its end for times close to `1`. -/
theorem exists_tail_mem (γ : Path x y) {V : Set X} (hV : V ∈ 𝓝 y) {c : ℝ} (hc : 0 < c) :
    ∃ t₁ : I, 1 - c < (t₁ : ℝ) ∧ (t₁ : ℝ) < 1 ∧ ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V := by
  obtain ⟨t₀, h0, hc', ht⟩ := exists_head_mem γ.symm hV hc
  refine ⟨σ t₀, by rw [unitInterval.coe_symm_eq]; linarith,
    by rw [unitInterval.coe_symm_eq]; linarith, fun t ht' => ?_⟩
  have := ht (σ t) (by rw [unitInterval.coe_symm_eq] at ht' ⊢; linarith)
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using this

/-- The tube lemma at the two ends of a homotopy with fixed ends. -/
theorem homotopy_exists_ends_mem {γ₁ γ₂ : Path x y} (F : Path.Homotopy γ₁ γ₂)
    {V : Set X} (hV : IsOpen V) (hx : x ∈ V) (hy : y ∈ V) :
    ∃ ε > (0 : ℝ), ∀ s t : I, ((t : ℝ) < ε → F (s, t) ∈ V) ∧ (1 - ε < (t : ℝ) → F (s, t) ∈ V) := by
  have key : ∀ (t₀ : I), F (0, t₀) ∈ V → (∀ s, F (s, t₀) = F (0, t₀)) →
      ∃ ε > (0 : ℝ), ∀ s t : I, dist t t₀ < ε → F (s, t) ∈ V := by
    intro t₀ hV0 hconst
    have hP : ∀ s ∈ (univ : Set I), ∀ᶠ z : I × I in 𝓝 (t₀, s), F (z.2, z.1) ∈ V := by
      intro s _
      have hc : Continuous fun z : I × I => F (z.2, z.1) := F.continuous.comp continuous_swap
      exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by rw [hconst]; exact hV0))
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
      (isCompact_univ.eventually_forall_of_forall_eventually (P := fun t s => F (s, t) ∈ V) hP)
    exact ⟨ε, hε, fun s t ht => h ht s (mem_univ s)⟩
  obtain ⟨ε₀, hε₀, h₀⟩ := key 0 (by rw [F.source]; exact hx) (fun s => by rw [F.source, F.source])
  obtain ⟨ε₁, hε₁, h₁⟩ := key 1 (by rw [F.target]; exact hy) (fun s => by rw [F.target, F.target])
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun s t => ⟨fun ht => h₀ s t ?_, fun ht => h₁ s t ?_⟩⟩
  · rw [Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
    exact ht.trans_le (min_le_left _ _)
  · rw [Subtype.dist_eq, Icc.coe_one, Real.dist_eq, abs_of_nonpos (by linarith [t.2.2])]
    linarith [min_le_right ε₀ ε₁]

end Tails

/-! ### `def:almost_trivial_loop` -/

/-- **`def:almost_trivial_loop`** (`RamcovGX.tex:1210`). A loop `γ ∈ Ω(x,x,U)` is *almost
trivial with respect to `U`* if for every neighbourhood `V` of `x` it is homotopic with respect
to `U` to a loop of `Ω(x,x,V ∩ U)` (the "connected component" of the paper read through the
homotopies, `RamcovGX.tex:1201`). -/
def AlmostTrivial (U : Set X) {x : X} (γ : Path x x) : Prop :=
  MemOmega U γ ∧ ∀ V ∈ 𝓝 x, ∃ γ' : Path x x, MemOmega (V ∩ U) γ' ∧ OmegaHomotopic U γ γ'

/-- `Ω_X(x,y,U)` as a subspace of `C([0,1], X)` (compact-open topology, `RamcovGX.tex:1199`). -/
def OmegaSet (U : Set X) (x y : X) : Set C(I, X) :=
  {f | f 0 = x ∧ f 1 = y ∧ ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → f t ∈ U}

/-- `def:almost_trivial_loop` in its **literal** form (`RamcovGX.tex:1212`): the connected
component of `γ` in the compact-open `Ω(x,x,U)` meets `Ω(x,x,V ∩ U)` for every neighbourhood
`V` of `x`. -/
def AlmostTrivialCC (U : Set X) {x : X} (γ : Path x x) : Prop :=
  γ.toContinuousMap ∈ OmegaSet U x x ∧ ∀ V ∈ 𝓝 x,
    (connectedComponentIn (OmegaSet U x x) γ.toContinuousMap ∩ OmegaSet (V ∩ U) x x).Nonempty

/-- Homotopic with respect to `U` implies in the same connected component of the compact-open
`Ω(x,y,U)` (the half of the "equivalently" of `RamcovGX.tex:1201` that holds in general). -/
theorem OmegaHomotopic.mem_connectedComponentIn {U : Set X} {x y : X} {γ₁ γ₂ : Path x y}
    (h : OmegaHomotopic U γ₁ γ₂) :
    γ₂.toContinuousMap ∈ connectedComponentIn (OmegaSet U x y) γ₁.toContinuousMap := by
  obtain ⟨F, hF⟩ := h
  set c : C(I, C(I, X)) := F.toContinuousMap.curry
  have hc0 : c 0 = γ₁.toContinuousMap := ContinuousMap.ext fun t => F.apply_zero t
  have hc1 : c 1 = γ₂.toContinuousMap := ContinuousMap.ext fun t => F.apply_one t
  have hsub : range c ⊆ OmegaSet U x y := by
    rintro _ ⟨s, rfl⟩
    exact ⟨F.source s, F.target s, fun t h0 h1 => hF s t h0 h1⟩
  have := (isPreconnected_range c.continuous).subset_connectedComponentIn ⟨0, hc0⟩ hsub
  exact this ⟨1, hc1⟩

/-- The homotopy reading of `def:almost_trivial_loop` implies the literal one. -/
theorem AlmostTrivial.almostTrivialCC {U : Set X} {x : X} {γ : Path x x}
    (h : AlmostTrivial U γ) : AlmostTrivialCC U γ := by
  refine ⟨⟨γ.source, γ.target, h.1⟩, fun V hV => ?_⟩
  obtain ⟨γ', hγ', hh⟩ := h.2 V hV
  exact ⟨γ'.toContinuousMap, hh.mem_connectedComponentIn, ⟨γ'.source, γ'.target, hγ'⟩⟩

section Square

variable {U : Set X} {x : X}

/-- A map on the square, extended to `ℝ²` through `projIcc`. -/
def squareExt (F : I × I → X) (p : ℝ × ℝ) : X :=
  F (Set.projIcc 0 1 zero_le_one p.1, Set.projIcc 0 1 zero_le_one p.2)

theorem continuous_squareExt {F : I × I → X} (hF : Continuous F) : Continuous (squareExt F) :=
  hF.comp ((continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd))

theorem squareExt_apply (F : I × I → X) (a : ℝ) {b : ℝ} (hb : b ∈ I) :
    squareExt F (a, b) = F (Set.projIcc 0 1 zero_le_one a, ⟨b, hb⟩) := by
  simp only [squareExt, Set.projIcc_of_mem _ hb]

theorem projIcc_zero' : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp)

theorem projIcc_one' : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := Subtype.ext (by simp)

theorem mem_segment_prod {a b c d : ℝ} {e : ℝ × ℝ} (he : e ∈ segment ℝ (a, b) (c, d)) :
    ∃ r ∈ Icc (0 : ℝ) 1, e = ((1 - r) * a + r * c, (1 - r) * b + r * d) := by
  rw [segment_eq_image_lineMap] at he
  obtain ⟨r, hr, rfl⟩ := he
  refine ⟨r, hr, ?_⟩
  simp [AffineMap.lineMap_apply_module, smul_eq_mul]

/-- **The square argument** of `lem:almost_homotopic_carac` (`RamcovGX.tex:1279–1286`), in the
strong form the proof of `lem:hausdorff_first_countable_connected` uses: if `γ` is almost
trivial, `V` an open neighbourhood of `x` and `γ([0,t₀] ∪ [t₁,1]) ⊆ V`, the middle
`γ_{|[t₀,t₁]}` is homotopic **in `U`** to a path `ω` of `V ∩ U`. -/
theorem AlmostTrivial.exists_mid {γ : Path x x} (hγ : AlmostTrivial U γ) {V : Set X}
    (hV : IsOpen V) (hxV : x ∈ V) {t₀ t₁ : I} (h0 : 0 < (t₀ : ℝ)) (h : (t₀ : ℝ) < t₁)
    (h1 : (t₁ : ℝ) < 1) (hγ₀ : ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V)
    (hγ₁ : ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) :
    ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧ HomotopicIn U (subpath γ t₀ t₁) ω := by
  obtain ⟨γ', hγ', F, hF⟩ := hγ.2 V (hV.mem_nhds hxV)
  obtain ⟨ε, hε, hεV⟩ := homotopy_exists_ends_mem F hV hxV hxV
  have ht₁' : 0 < 1 - (t₁ : ℝ) := sub_pos.2 h1
  set τ : ℝ := min (min ε (t₀ : ℝ)) (1 - t₁) / 2 with hτ
  have hm1 := min_le_left (min ε (t₀ : ℝ)) (1 - t₁)
  have hm2 := min_le_right (min ε (t₀ : ℝ)) (1 - t₁)
  have hm3 := min_le_left ε (t₀ : ℝ)
  have hm4 := min_le_right ε (t₀ : ℝ)
  have hτ0 : 0 < τ := by positivity
  have hτε : τ < ε := by rw [hτ]; linarith
  have hτt₀ : τ < t₀ := by rw [hτ]; linarith
  have hτt₁ : τ < 1 - t₁ := by rw [hτ]; linarith
  set G : ℝ × ℝ → X := squareExt (fun z => F z) with hGdef
  have hG : Continuous G := continuous_squareExt F.continuous
  set A : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Icc τ (1 - τ) with hAdef
  have hAc : Convex ℝ A := convex_univ.prod (convex_Icc _ _)
  have hGU : ∀ e ∈ A, G e ∈ U := by
    rintro ⟨a, b⟩ ⟨-, hb1, hb2⟩
    have hb : b ∈ I := ⟨by linarith, by linarith⟩
    rw [hGdef, squareExt_apply _ a hb]
    exact hF _ _ (by show 0 < b; linarith) (by show b < 1; linarith)
  -- the route
  set P0 : ℝ × ℝ := (0, t₀)
  set P1 : ℝ × ℝ := (0, τ)
  set P2 : ℝ × ℝ := (1, τ)
  set P3 : ℝ × ℝ := (1, 1 - τ)
  set P4 : ℝ × ℝ := (0, 1 - τ)
  set P5 : ℝ × ℝ := (0, t₁)
  set Good : Set (ℝ × ℝ) := {e | e ∈ A ∧ G e ∈ V} with hGood
  have hγG : ∀ u : ℝ, ∀ hu : u ∈ I, G (0, u) = γ ⟨u, hu⟩ := fun u hu => by
    rw [hGdef, squareExt_apply _ 0 hu, projIcc_zero']
    exact F.apply_zero _
  have s01 : segment ℝ P0 P1 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : τ ≤ (1 - r) * t₀ + r * τ := by nlinarith
    have hu2 : (1 - r) * t₀ + r * τ ≤ t₀ := by nlinarith
    have hu : (1 - r) * t₀ + r * τ ∈ I := ⟨by linarith, by linarith [t₀.2.2]⟩
    refine ⟨⟨mem_univ _, hu1, by linarith⟩, ?_⟩
    simp only [mul_zero, add_zero]
    rw [hγG _ hu]
    exact hγ₀ _ hu2
  have s12 : segment ℝ P1 P2 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu : (1 - r) * τ + r * τ = τ := by ring
    have hτI : τ ∈ I := ⟨hτ0.le, by linarith⟩
    refine ⟨⟨mem_univ _, by rw [hu], by rw [hu]; linarith⟩, ?_⟩
    rw [hu, hGdef, squareExt_apply _ _ hτI]
    exact (hεV _ _).1 hτε
  have s23 : segment ℝ P2 P3 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : τ ≤ (1 - r) * τ + r * (1 - τ) := by nlinarith
    have hu2 : (1 - r) * τ + r * (1 - τ) ≤ 1 - τ := by nlinarith
    have hu : (1 - r) * τ + r * (1 - τ) ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨mem_univ _, hu1, hu2⟩, ?_⟩
    have h11 : (1 - r) * 1 + r * 1 = 1 := by ring
    rw [h11, hGdef, squareExt_apply _ _ hu, projIcc_one', F.apply_one]
    exact (hγ' _ (show (0 : ℝ) < _ by linarith) (show _ < (1 : ℝ) by linarith)).1
  have s34 : segment ℝ P3 P4 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu : (1 - r) * (1 - τ) + r * (1 - τ) = 1 - τ := by ring
    have hτI : 1 - τ ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨mem_univ _, by rw [hu]; linarith, by rw [hu]⟩, ?_⟩
    rw [hu, hGdef, squareExt_apply _ _ hτI]
    exact (hεV _ _).2 (by show 1 - ε < 1 - τ; linarith)
  have s45 : segment ℝ P4 P5 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : (t₁ : ℝ) ≤ (1 - r) * (1 - τ) + r * t₁ := by nlinarith
    have hu2 : (1 - r) * (1 - τ) + r * t₁ ≤ 1 - τ := by nlinarith
    have hu : (1 - r) * (1 - τ) + r * t₁ ∈ I := ⟨by linarith [t₁.2.1], by linarith⟩
    refine ⟨⟨mem_univ _, by linarith, hu2⟩, ?_⟩
    simp only [mul_zero, add_zero]
    rw [hγG _ hu]
    exact hγ₁ _ hu1
  set η : Path P0 P5 := ((((Path.segment P0 P1).trans (Path.segment P1 P2)).trans
    (Path.segment P2 P3)).trans (Path.segment P3 P4)).trans (Path.segment P4 P5) with hη
  have hηG : ∀ t, η t ∈ Good := by
    intro t
    have : η t ∈ range η := mem_range_self t
    simp only [hη, Path.trans_range, Path.range_segment] at this
    rcases this with (((h | h) | h) | h) | h
    · exact s01 h
    · exact s12 h
    · exact s23 h
    · exact s34 h
    · exact s45 h
  have e0 : γ t₀ = G P0 := (hγG _ t₀.2).symm
  have e5 : γ t₁ = G P5 := (hγG _ t₁.2).symm
  refine ⟨(η.map hG).cast e0 e5, fun s => ?_, ?_⟩
  · exact ⟨(hηG s).2, hGU _ (hηG s).1⟩
  · have hP0 : P0 ∈ A := ⟨mem_univ _, hτt₀.le, by linarith⟩
    have hP5 : P5 ∈ A := ⟨mem_univ _, by linarith [t₁.2.1], by linarith⟩
    have hmain := homotopicIn_map_of_convex (Path.segment P0 P5) η hAc
      (fun t => by rw [Path.segment_apply]; exact hAc.lineMap_mem hP0 hP5 t.2)
      (fun t => (hηG t).1) hG hGU
    refine (hmain.cast e0 e5).of_eq ?_ rfl
    ext r
    rw [Path.cast_coe, Path.map_coe, comp_apply, Path.segment_apply, subpath_apply']
    have hl : AffineMap.lineMap P0 P5 (r : ℝ) = (0, (1 - (r : ℝ)) * t₀ + r * t₁) := by
      simp [P0, P5, AffineMap.lineMap_apply_module, smul_eq_mul]
    obtain ⟨w, hw1, hw2, hw⟩ := subpath_mem γ t₀ t₁ r
    have hwI : (1 - (r : ℝ)) * t₀ + r * t₁ ∈ I := by
      constructor <;> nlinarith [r.2.1, r.2.2, t₀.2.1, t₁.2.2]
    rw [hl, hγG _ hwI, Path.extend_apply γ hwI]

end Square

/-! ### `lem:almost_homotopic_carac` -/

section Carac

variable {U : Set X} {x : X}

/-- **`lem:almost_homotopic_carac`** (`RamcovGX.tex:1271`). For `γ ∈ Ω(x,x,U)`: `γ` is almost
trivial iff for every open neighbourhood `V` of `x` and all `0 < t₀ < t₁ < 1` with
`γ([0,t₀] ∪ [t₁,1]) ⊆ V` there is a path `ω : γ(t₀) ⇝ γ(t₁)` in `V ∩ U` with `γ` homotopic in
`Ω(x,x,U)` to `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`. -/
theorem almost_homotopic_carac {γ : Path x x} (hγ : MemOmega U γ) :
    AlmostTrivial U γ ↔ ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        OmegaHomotopic U γ (splice γ t₀ t₁ h ω) := by
  constructor
  · intro hat V hV hxV t₀ t₁ h0 h h1 hv0 hv1
    obtain ⟨ω, hω, hh⟩ := hat.exists_mid hV hxV h0 h h1 hv0 hv1
    exact ⟨ω, hω, splice_omegaHomotopic hγ h h1 hh⟩
  · intro H
    refine ⟨hγ, fun V hV => ?_⟩
    obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
    obtain ⟨t₀, h0, h0', hv0⟩ := exists_head_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
    obtain ⟨t₁, h1', h1, hv1⟩ := exists_tail_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
    have h : (t₀ : ℝ) < t₁ := by linarith
    obtain ⟨ω, hω, hh⟩ := H V' hV' hxV' t₀ t₁ h0 h h1 hv0 hv1
    refine ⟨splice γ t₀ t₁ h ω, fun t ht0 ht1 => ?_, hh⟩
    rcases splice_mem γ h ω t with ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨s, hs⟩
    · rw [he]; exact ⟨hV'V (hv0 t ht), hγ t ht0 ht1⟩
    · rw [he]; exact ⟨hV'V (hv1 t ht), hγ t ht0 ht1⟩
    · rw [← hs]; exact ⟨hV'V (hω s).1, (hω s).2⟩

end Carac

/-! ### Groupoid calculus for homotopies in `U` -/

section Groupoid

variable {U : Set X} {x y z w : X}

open Path.Homotopic.Quotient in
theorem homotopicIn_iff_mk {γ₁ γ₂ : Path x y} (h₁ : ∀ t, γ₁ t ∈ U) (h₂ : ∀ t, γ₂ t ∈ U) :
    HomotopicIn U γ₁ γ₂ ↔ mk (pathToSub γ₁ h₁) = mk (pathToSub γ₂ h₂) := by
  rw [Path.Homotopic.Quotient.eq, homotopicIn_iff]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨h₁, h₂, h⟩⟩

open Path.Homotopic.Quotient in
/-- `A⁻¹ * B ≃ W` iff `B ≃ A * W`, in `U`. -/
theorem homotopicIn_symm_trans_iff {A : Path x y} {B : Path x z} {W : Path y z}
    (hA : ∀ t, A t ∈ U) (hB : ∀ t, B t ∈ U) (hW : ∀ t, W t ∈ U) :
    HomotopicIn U (A.symm.trans B) W ↔ HomotopicIn U B (A.trans W) := by
  have h1 := path_trans_mem (path_symm_mem hA) hB
  have h2 := path_trans_mem hA hW
  rw [homotopicIn_iff_mk h1 hW, homotopicIn_iff_mk hB h2,
    pathToSub_trans _ _ (path_symm_mem hA) hB, pathToSub_symm _ hA, pathToSub_trans _ _ hA hW,
    mk_trans, mk_trans, mk_symm]
  constructor
  · intro h
    rw [← h, ← trans_assoc, trans_symm, refl_trans]
  · intro h
    rw [h, ← trans_assoc, symm_trans, refl_trans]

open Path.Homotopic.Quotient in
theorem homotopicIn_trans_assoc {p : Path x y} {q : Path y z} {r : Path z w}
    (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) (hr : ∀ t, r t ∈ U) :
    HomotopicIn U ((p.trans q).trans r) (p.trans (q.trans r)) := by
  rw [homotopicIn_iff_mk (path_trans_mem (path_trans_mem hp hq) hr)
    (path_trans_mem hp (path_trans_mem hq hr)), pathToSub_trans _ _ (path_trans_mem hp hq) hr,
    pathToSub_trans _ _ hp hq, pathToSub_trans _ _ hp (path_trans_mem hq hr),
    pathToSub_trans _ _ hq hr]
  simp only [mk_trans, trans_assoc]

open Path.Homotopic.Quotient in
/-- `B ≃ A * W` gives `A ≃ B * W⁻¹`, in `U`. -/
theorem homotopicIn_swap {A : Path x y} {B : Path x z} {W : Path y z}
    (hA : ∀ t, A t ∈ U) (hB : ∀ t, B t ∈ U) (hW : ∀ t, W t ∈ U)
    (h : HomotopicIn U B (A.trans W)) : HomotopicIn U A (B.trans W.symm) := by
  rw [homotopicIn_iff_mk hB (path_trans_mem hA hW), pathToSub_trans _ _ hA hW, mk_trans] at h
  rw [homotopicIn_iff_mk hA (path_trans_mem hB (path_symm_mem hW)),
    pathToSub_trans _ _ hB (path_symm_mem hW), pathToSub_symm _ hW, mk_trans, mk_symm, h,
    trans_assoc, trans_symm, trans_refl]

end Groupoid

/-! ### `def:almost_homotopic_paths`, `rem:implicitely_two_almost_homotopic` -/

/-- **`def:almost_homotopic_paths`** (`RamcovGX.tex:1262`). Two paths `γ₁, γ₂ ∈ Ω(x,y,U)` are
*almost homotopic with respect to `U`* if the loop `γ₂⁻¹ * γ₁` is almost trivial with respect
to `U`. (Being a loop of `Ω(y,y,U)`, this forces `x ∈ U` and `γ₁, γ₂ ∈ Ω(x,y,U)`:
`GX.AlmostHomotopic.mem`.) -/
def AlmostHomotopic (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  AlmostTrivial U (γ₂.symm.trans γ₁)

section AlmostHom

variable {U : Set X} {x y : X}

/-- **`rem:implicitely_two_almost_homotopic`** (`RamcovGX.tex:1268`): two almost homotopic paths
have the same ends (here by typing: both are paths `x ⇝ y`). -/
theorem AlmostHomotopic.ends {γ₁ γ₂ : Path x y} (_ : AlmostHomotopic U γ₁ γ₂) :
    γ₁ 0 = γ₂ 0 ∧ γ₁ 1 = γ₂ 1 := by
  simp

theorem loop_apply_le (γ₁ γ₂ : Path x y) {t : I} (ht : (t : ℝ) ≤ 1 / 2) :
    (γ₂.symm.trans γ₁) t = γ₂ ⟨1 - 2 * t, by constructor <;> linarith [t.2.1]⟩ := by
  rw [Path.trans_apply, dif_pos ht, Path.symm_apply]
  congr 1

theorem loop_apply_ge (γ₁ γ₂ : Path x y) {t : I} (ht : 1 / 2 ≤ (t : ℝ)) :
    (γ₂.symm.trans γ₁) t = γ₁ ⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩ := by
  rw [Path.trans_apply]
  split_ifs with h
  · have h' : (t : ℝ) = 1 / 2 := le_antisymm h ht
    rw [Path.symm_apply]
    have e1 : (σ ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ : I) = 0 :=
      Subtype.ext (by simp [h'])
    have e2 : (⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.2]⟩ : I) = 0 :=
      Subtype.ext (by simp [h'])
    simp only [comp_apply, e1, e2, γ₂.source, γ₁.source]
  · rfl

/-- The values of a path of `Ω(x,y,U)` before time `1` lie in `U`, when `x ∈ U`. -/
theorem MemOmega.extend_mem {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {r : ℝ}
    (hr : r < 1) : γ.extend r ∈ U := by
  rcases le_or_gt r 0 with h | h
  · rw [Path.extend_of_le_zero γ h]; exact hx
  · rw [Path.extend_apply γ ⟨h.le, hr.le⟩]; exact hγ _ h hr

theorem MemOmega.loop {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) : MemOmega U (γ₂.symm.trans γ₁) := by
  intro t h0 h1
  rcases le_total (t : ℝ) (1 / 2) with h | h
  · rw [loop_apply_le γ₁ γ₂ h]
    rcases eq_or_lt_of_le h with h' | h'
    · have : (⟨1 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1]⟩ : I) = 0 :=
        Subtype.ext (by simp [h'])
      rw [this, γ₂.source]; exact hx
    · exact h₂ _ (show (0 : ℝ) < 1 - 2 * t by linarith) (show 1 - 2 * (t : ℝ) < 1 by linarith)
  · rw [loop_apply_ge γ₁ γ₂ h]
    rcases eq_or_lt_of_le h with h' | h'
    · have : (⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.2]⟩ : I) = 0 :=
        Subtype.ext (by simp [← h'])
      rw [this, γ₁.source]; exact hx
    · exact h₁ _ (show (0 : ℝ) < 2 * t - 1 by linarith) (show 2 * (t : ℝ) - 1 < 1 by linarith)

/-- An almost homotopy lives in `Ω(x,y,U)` with `x ∈ U`. -/
theorem AlmostHomotopic.mem {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    x ∈ U ∧ MemOmega U γ₁ ∧ MemOmega U γ₂ := by
  have hL := h.1
  have hhalf : (0 : ℝ) < ((⟨1 / 2, by norm_num, by norm_num⟩ : I) : ℝ) := by norm_num
  refine ⟨?_, fun t h0 h1 => ?_, fun t h0 h1 => ?_⟩
  · have := hL ⟨1 / 2, by norm_num, by norm_num⟩ hhalf (by norm_num)
    rw [loop_apply_le γ₁ γ₂ (by norm_num)] at this
    have e : (⟨1 - 2 * (1 / 2 : ℝ), by norm_num, by norm_num⟩ : I) = 0 := Subtype.ext (by norm_num)
    rwa [e, γ₂.source] at this
  · have := hL ⟨(1 + t) / 2, by constructor <;> linarith⟩ (by show (0 : ℝ) < _; linarith)
      (by show _ < (1 : ℝ); linarith)
    rw [loop_apply_ge γ₁ γ₂ (by show (1 / 2 : ℝ) ≤ _; linarith)] at this
    have e : (⟨2 * ((1 + (t : ℝ)) / 2) - 1, by constructor <;> linarith⟩ : I) = t :=
      Subtype.ext (by simp; ring)
    rwa [e] at this
  · have := hL ⟨(1 - t) / 2, by constructor <;> linarith⟩ (by show (0 : ℝ) < _; linarith)
      (by show _ < (1 : ℝ); linarith)
    rw [loop_apply_le γ₁ γ₂ (by show _ ≤ (1 / 2 : ℝ); linarith)] at this
    have e : (⟨1 - 2 * ((1 - (t : ℝ)) / 2), by constructor <;> linarith⟩ : I) = t :=
      Subtype.ext (by simp; ring)
    rwa [e] at this

/-- The parameter `(1 - s)/2`. -/
def loopLo (s : I) : I := ⟨(1 - s) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩

/-- The parameter `(1 + s)/2`. -/
def loopHi (s : I) : I := ⟨(1 + s) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩

theorem loop_loopLo (γ₁ γ₂ : Path x y) (s : I) : (γ₂.symm.trans γ₁) (loopLo s) = γ₂ s := by
  rw [loop_apply_le γ₁ γ₂ (by show (1 - (s : ℝ)) / 2 ≤ 1 / 2; linarith [s.2.1])]
  congr 1; exact Subtype.ext (by simp [loopLo]; ring)

theorem loop_loopHi (γ₁ γ₂ : Path x y) (s : I) : (γ₂.symm.trans γ₁) (loopHi s) = γ₁ s := by
  rw [loop_apply_ge γ₁ γ₂ (by show 1 / 2 ≤ (1 + (s : ℝ)) / 2; linarith [s.2.1])]
  congr 1; exact Subtype.ext (by simp [loopHi]; ring)

/-- The middle of `γ₂⁻¹ * γ₁` between `(1-s)/2` and `(1+s)/2` is `(γ₂{|[0,s]})⁻¹ * γ₁{|[0,s]}`. -/
theorem subpath_loop (γ₁ γ₂ : Path x y) {s : I} (hs : 0 < (s : ℝ)) :
    subpath (γ₂.symm.trans γ₁) (loopLo s) (loopHi s) =
      ((head γ₂ s).symm.trans (head γ₁ s)).cast (loop_loopLo γ₁ γ₂ s)
        (loop_loopHi γ₁ γ₂ s) := by
  ext r
  rw [Path.cast_coe, subpath_apply', Path.trans_apply]
  have hr0 := r.2.1
  have hr1 := r.2.2
  have hs1 := s.2.2
  have hu : (1 - (r : ℝ)) * (loopLo s : ℝ) + r * (loopHi s : ℝ) ∈ I := by
    simp only [loopLo, loopHi]; constructor <;> nlinarith
  rw [Path.extend_apply _ hu]
  split_ifs with h
  · rw [loop_apply_le γ₁ γ₂ (by simp only [loopLo, loopHi]; nlinarith), Path.symm_apply,
      comp_apply, head_apply, subpath_apply']
    have hv : (1 - ((σ ⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨hr0, h⟩⟩ : I) :
        ℝ)) * ((0 : I) : ℝ) + ((σ ⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
        ⟨hr0, h⟩⟩ : I) : ℝ) * s ∈ I := by
      simp only [unitInterval.coe_symm_eq, Icc.coe_zero, mul_zero, zero_add]
      constructor <;> nlinarith
    rw [Path.extend_apply _ hv]
    congr 1
    exact Subtype.ext (by simp [loopLo, loopHi]; ring)
  · rw [not_le] at h
    rw [loop_apply_ge γ₁ γ₂ (by simp only [loopLo, loopHi]; nlinarith), head_apply,
      subpath_apply']
    have hv : (1 - ((⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨h.le, hr1⟩⟩ : I) :
        ℝ)) * ((0 : I) : ℝ) + ((⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨h.le, hr1⟩⟩ : I) : ℝ) * s ∈ I := by
      simp only [Icc.coe_zero, mul_zero, zero_add]
      constructor <;> nlinarith
    rw [Path.extend_apply _ hv]
    congr 1
    exact Subtype.ext (by simp [loopLo, loopHi]; ring)

end AlmostHom

/-! ### The germ form of almost homotopy, and `lem:hausdorff_first_countable_connected` -/

section Germ

variable {U : Set X} {x y : X}

/-- The class of a path of `U` in the fundamental groupoid of the subspace `U`. -/
abbrev qU {a b : X} (γ : Path a b) (h : ∀ t, γ t ∈ U) :
    Path.Homotopic.Quotient (⟨a, γ.source ▸ h 0⟩ : U) ⟨b, γ.target ▸ h 1⟩ :=
  Path.Homotopic.Quotient.mk (pathToSub γ h)

theorem qU_trans {a b c : X} (γ : Path a b) (γ' : Path b c) (h : ∀ t, γ t ∈ U)
    (h' : ∀ t, γ' t ∈ U) :
    qU (γ.trans γ') (path_trans_mem h h') = (qU γ h).trans (qU γ' h') := by
  rw [qU, pathToSub_trans _ _ h h', Path.Homotopic.Quotient.mk_trans]

theorem homotopicIn_iff_qU {a b : X} {γ₁ γ₂ : Path a b} (h₁ : ∀ t, γ₁ t ∈ U)
    (h₂ : ∀ t, γ₂ t ∈ U) : HomotopicIn U γ₁ γ₂ ↔ qU γ₁ h₁ = qU γ₂ h₂ :=
  homotopicIn_iff_mk h₁ h₂

theorem head_mem {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {s : I} (hs : (s : ℝ) < 1)
    (t : I) : head γ s t ∈ U := by
  rw [head_apply, subpath_apply']
  refine hγ.extend_mem hx ?_
  simp only [Icc.coe_zero, mul_zero, zero_add]
  nlinarith [t.2.1, t.2.2, s.2.1]

theorem subpath_mem_of_memOmega {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {a b : I}
    (ha : (a : ℝ) < 1) (hb : (b : ℝ) < 1) (t : I) : subpath γ a b t ∈ U := by
  obtain ⟨w, -, hw2, hw⟩ := subpath_mem γ a b t
  rw [hw, ← Path.extend_extends' γ w]
  exact hγ.extend_mem hx (hw2.trans_lt (max_lt ha hb))

theorem subpath_mem_of_tail {γ : Path x y} {V : Set X} {c : ℝ}
    (hV : ∀ t : I, c ≤ t → γ t ∈ V) {a b : I} (ha : c ≤ a) (hb : c ≤ b) (t : I) :
    subpath γ a b t ∈ V := by
  obtain ⟨w, hw1, -, hw⟩ := subpath_mem γ a b t
  rw [hw]; exact hV w ((le_min ha hb).trans hw1)

theorem head_trans_subpath {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {a b : I}
    (ha : (a : ℝ) < 1) (hb : (b : ℝ) < 1) :
    HomotopicIn U (head γ b) ((head γ a).trans (subpath γ a b)) := by
  have h := subpath_trans_homotopicIn (U := U) γ 0 a b (fun r _ hr => hγ.extend_mem hx
    (hr.trans_lt (max_lt (max_lt (by simp) ha) hb)))
  refine (h.cast γ.source.symm rfl).of_eq rfl ?_
  ext t
  simp only [Path.cast_coe, Path.trans_apply]
  split_ifs <;> rfl

/-- **The germ form of almost homotopy.** `γ₁ ≈ γ₂` iff for every open neighbourhood `V` of `y`
and all `s₁, s₂ < 1` with `γᵢ([sᵢ,1]) ⊆ V` there is `ω : γ₂(s₂) ⇝ γ₁(s₁)` in `V ∩ U` with
`γ₁{|[0,s₁]} ≃ γ₂{|[0,s₂]} * ω` in `U`. (`GX.almostHomotopic_iff_germEquiv`.) -/
def GermEquiv (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∀ V : Set X, IsOpen V → y ∈ V → ∀ s₁ s₂ : I, (s₁ : ℝ) < 1 → (s₂ : ℝ) < 1 →
    (∀ t : I, (s₁ : ℝ) ≤ t → γ₁ t ∈ V) → (∀ t : I, (s₂ : ℝ) ≤ t → γ₂ t ∈ V) →
    ∃ ω : Path (γ₂ s₂) (γ₁ s₁), (∀ τ, ω τ ∈ V ∩ U) ∧
      HomotopicIn U (head γ₁ s₁) ((head γ₂ s₂).trans ω)

open Path.Homotopic.Quotient in
/-- Moving the cut points of a germ relation along the tails. -/
theorem germ_adjust {γ₁ γ₂ : Path x y} (h₁ : MemOmega U γ₁) (h₂ : MemOmega U γ₂) (hx : x ∈ U)
    {s s' a a' : I} (hs : (s : ℝ) < 1) (hs' : (s' : ℝ) < 1) (ha : (a : ℝ) < 1) (ha' : (a' : ℝ) < 1)
    {ω : Path (γ₂ s') (γ₁ s)} (hω : ∀ τ, ω τ ∈ U)
    (h : HomotopicIn U (head γ₁ s) ((head γ₂ s').trans ω)) :
    HomotopicIn U (head γ₁ a)
      ((head γ₂ a').trans ((subpath γ₂ a' s').trans (ω.trans (subpath γ₁ s a)))) := by
  have m1 := subpath_mem_of_memOmega h₁ hx hs ha
  have m2 := subpath_mem_of_memOmega h₂ hx ha' hs'
  have e1 := (homotopicIn_iff_qU (head_mem h₁ hx ha)
    (path_trans_mem (head_mem h₁ hx hs) m1)).1 (head_trans_subpath h₁ hx hs ha)
  have e2 := (homotopicIn_iff_qU (head_mem h₂ hx hs')
    (path_trans_mem (head_mem h₂ hx ha') m2)).1 (head_trans_subpath h₂ hx ha' hs')
  have e3 := (homotopicIn_iff_qU (head_mem h₁ hx hs)
    (path_trans_mem (head_mem h₂ hx hs') hω)).1 h
  rw [qU_trans _ _ (head_mem h₁ hx hs) m1] at e1
  rw [qU_trans _ _ (head_mem h₂ hx ha') m2] at e2
  rw [qU_trans _ _ (head_mem h₂ hx hs') hω] at e3
  rw [homotopicIn_iff_qU (head_mem h₁ hx ha) (path_trans_mem (head_mem h₂ hx ha')
    (path_trans_mem m2 (path_trans_mem hω m1))), qU_trans _ _ (head_mem h₂ hx ha')
    (path_trans_mem m2 (path_trans_mem hω m1)), qU_trans _ _ m2 (path_trans_mem hω m1),
    qU_trans _ _ hω m1, e1, e3, e2]
  simp only [trans_assoc]

theorem germEquiv_refl {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) : GermEquiv U γ γ := by
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  refine ⟨subpath γ s₂ s₁, fun τ => ?_, head_trans_subpath hγ hx hs₂ hs₁⟩
  obtain ⟨w, hw1, hw2, hw⟩ := subpath_mem γ s₂ s₁ τ
  refine ⟨?_, subpath_mem_of_memOmega hγ hx hs₂ hs₁ τ⟩
  rw [hw]
  rcases le_total (s₂ : ℝ) s₁ with h | h
  · exact ht₂ w (by rw [min_eq_left h] at hw1; exact hw1)
  · exact ht₁ w (by rw [min_eq_right h] at hw1; exact hw1)

theorem GermEquiv.symm {γ₁ γ₂ : Path x y} (h₁ : MemOmega U γ₁) (h₂ : MemOmega U γ₂)
    (hx : x ∈ U) (h : GermEquiv U γ₁ γ₂) : GermEquiv U γ₂ γ₁ := by
  intro V hV hyV a b ha hb hta htb
  obtain ⟨ω, hω, hh⟩ := h V hV hyV b a hb ha htb hta
  exact ⟨ω.symm, path_symm_mem hω, homotopicIn_swap (head_mem h₂ hx ha) (head_mem h₁ hx hb)
    (fun τ => (hω τ).2) hh⟩

theorem GermEquiv.trans {γ₁ γ₂ γ₃ : Path x y} (h₃ : MemOmega U γ₃) (hx : x ∈ U) (h : GermEquiv U γ₁ γ₂) (h' : GermEquiv U γ₂ γ₃) :
    GermEquiv U γ₁ γ₃ := by
  intro V hV hyV s₁ s₃ hs₁ hs₃ ht₁ ht₃
  obtain ⟨s₂, -, hs₂, ht₂⟩ := exists_tail_mem γ₂ (hV.mem_nhds hyV) (c := 1) one_pos
  obtain ⟨ω₁, hω₁, hh₁⟩ := h V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  obtain ⟨ω₂, hω₂, hh₂⟩ := h' V hV hyV s₂ s₃ hs₂ hs₃ ht₂ ht₃
  have hU₁ : ∀ τ, ω₁ τ ∈ U := fun τ => (hω₁ τ).2
  have hU₂ : ∀ τ, ω₂ τ ∈ U := fun τ => (hω₂ τ).2
  refine ⟨ω₂.trans ω₁, path_trans_mem hω₂ hω₁, ?_⟩
  refine hh₁.trans ((hh₂.hcomp (HomotopicIn.refl hU₁)).trans ?_)
  exact homotopicIn_trans_assoc (head_mem h₃ hx hs₃) hU₂ hU₁

theorem AlmostHomotopic.germEquiv {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    GermEquiv U γ₁ γ₂ := by
  obtain ⟨hx, h₁, h₂⟩ := h.mem
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  set s : I := ⟨max (max (s₁ : ℝ) s₂) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le s₁.2.2 s₂.2.2) (by norm_num)⟩ with hsdef
  have hs1 : (s : ℝ) < 1 := max_lt (max_lt hs₁ hs₂) (by norm_num)
  have hs0 : (1 / 2 : ℝ) ≤ s := le_max_right _ _
  have hss₁ : (s₁ : ℝ) ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hss₂ : (s₂ : ℝ) ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have hlo : ∀ t : I, (t : ℝ) ≤ loopLo s → (γ₂.symm.trans γ₁) t ∈ V := by
    intro t ht
    have ht' : (t : ℝ) ≤ 1 / 2 := ht.trans (by simp only [loopLo]; linarith)
    rw [loop_apply_le γ₁ γ₂ ht']
    exact ht₂ _ (by simp only [loopLo] at ht; show (s₂ : ℝ) ≤ 1 - 2 * t; linarith)
  have hhi : ∀ t : I, (loopHi s : ℝ) ≤ t → (γ₂.symm.trans γ₁) t ∈ V := by
    intro t ht
    have ht' : (1 / 2 : ℝ) ≤ t := le_trans (by simp only [loopHi]; linarith [s.2.1]) ht
    rw [loop_apply_ge γ₁ γ₂ ht']
    exact ht₁ _ (by simp only [loopHi] at ht; show (s₁ : ℝ) ≤ 2 * t - 1; linarith)
  obtain ⟨ω', hω', hh⟩ := h.exists_mid hV hyV (t₀ := loopLo s) (t₁ := loopHi s)
    (by simp only [loopLo]; linarith) (by simp only [loopLo, loopHi]; linarith)
    (by simp only [loopHi]; linarith) hlo hhi
  rw [subpath_loop γ₁ γ₂ (by linarith)] at hh
  set ω : Path (γ₂ s) (γ₁ s) := ω'.cast (loop_loopLo γ₁ γ₂ s).symm (loop_loopHi γ₁ γ₂ s).symm
  have hωV : ∀ τ, ω τ ∈ V ∩ U := fun τ => hω' τ
  have hh' : HomotopicIn U ((head γ₂ s).symm.trans (head γ₁ s)) ω :=
    (hh.cast (loop_loopLo γ₁ γ₂ s).symm (loop_loopHi γ₁ γ₂ s).symm).of_eq (by ext; rfl) rfl
  have hB := (homotopicIn_symm_trans_iff (head_mem h₂ hx hs1) (head_mem h₁ hx hs1)
    (fun τ => (hωV τ).2)).1 hh'
  refine ⟨_, fun τ => ?_, germ_adjust h₁ h₂ hx hs1 hs1 hs₁ hs₂ (fun τ => (hωV τ).2) hB⟩
  have m1 := subpath_mem_of_tail ht₂ (le_refl (s₂ : ℝ)) hss₂
  have m2 := subpath_mem_of_tail ht₁ hss₁ (le_refl (s₁ : ℝ))
  have m1' := subpath_mem_of_memOmega h₂ hx hs₂ hs1
  have m2' := subpath_mem_of_memOmega h₁ hx hs1 hs₁
  exact path_trans_mem (W := V ∩ U) (fun t => ⟨m1 t, m1' t⟩)
    (path_trans_mem hωV fun t => ⟨m2 t, m2' t⟩) τ

theorem almostHomotopic_of_germEquiv {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) (h : GermEquiv U γ₁ γ₂) : AlmostHomotopic U γ₁ γ₂ := by
  have hL := MemOmega.loop hx h₁ h₂
  refine ⟨hL, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hyV'⟩ := mem_nhds_iff.1 hV
  obtain ⟨a, -, ha, hta⟩ := exists_tail_mem γ₁ (hV'.mem_nhds hyV') (c := 1) one_pos
  obtain ⟨b, -, hb, htb⟩ := exists_tail_mem γ₂ (hV'.mem_nhds hyV') (c := 1) one_pos
  set s : I := ⟨max (max (a : ℝ) b) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le a.2.2 b.2.2) (by norm_num)⟩ with hsdef
  have hs1 : (s : ℝ) < 1 := max_lt (max_lt ha hb) (by norm_num)
  have hs0 : (1 / 2 : ℝ) ≤ s := le_max_right _ _
  have hsa : (a : ℝ) ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hsb : (b : ℝ) ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨ω, hω, hh⟩ := h V' hV' hyV' s s hs1 hs1 (fun t ht => hta t (hsa.trans ht))
    (fun t ht => htb t (hsb.trans ht))
  have hh' := (homotopicIn_symm_trans_iff (head_mem h₂ hx hs1) (head_mem h₁ hx hs1)
    (fun τ => (hω τ).2)).2 hh
  have hmid : HomotopicIn U (subpath (γ₂.symm.trans γ₁) (loopLo s) (loopHi s))
      (ω.cast (loop_loopLo γ₁ γ₂ s) (loop_loopHi γ₁ γ₂ s)) := by
    rw [subpath_loop γ₁ γ₂ (by linarith)]
    exact hh'.cast _ _
  have hlohi : ((loopLo s : I) : ℝ) < loopHi s := by simp only [loopLo, loopHi]; linarith
  refine ⟨_, fun t ht0 ht1 => ?_,
    splice_omegaHomotopic hL hlohi (by simp only [loopHi]; linarith) hmid⟩
  rcases splice_mem _ hlohi (ω.cast (loop_loopLo γ₁ γ₂ s) (loop_loopHi γ₁ γ₂ s)) t with
    ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨r, hr⟩
  · rw [he]
    refine ⟨hV'V ?_, hL t ht0 ht1⟩
    have ht' : (t : ℝ) ≤ 1 / 2 := ht.trans (by simp only [loopLo]; linarith)
    rw [loop_apply_le γ₁ γ₂ ht']
    exact htb _ (by simp only [loopLo] at ht; show (b : ℝ) ≤ 1 - 2 * t; linarith)
  · rw [he]
    refine ⟨hV'V ?_, hL t ht0 ht1⟩
    have ht' : (1 / 2 : ℝ) ≤ t := le_trans (by simp only [loopHi]; linarith) ht
    rw [loop_apply_ge γ₁ γ₂ ht']
    exact hta _ (by simp only [loopHi] at ht; show (a : ℝ) ≤ 2 * t - 1; linarith)
  · rw [← hr]
    exact ⟨hV'V (hω r).1, (hω r).2⟩

/-- Almost homotopy is the germ relation (for paths of `Ω(x,y,U)`, `x ∈ U`). -/
theorem almostHomotopic_iff_germEquiv {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) : AlmostHomotopic U γ₁ γ₂ ↔ GermEquiv U γ₁ γ₂ :=
  ⟨AlmostHomotopic.germEquiv, almostHomotopic_of_germEquiv hx h₁ h₂⟩

theorem almostHomotopic_refl {γ : Path x y} (hx : x ∈ U) (hγ : MemOmega U γ) :
    AlmostHomotopic U γ γ :=
  almostHomotopic_of_germEquiv hx hγ hγ (germEquiv_refl hγ hx)

theorem AlmostHomotopic.symm {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    AlmostHomotopic U γ₂ γ₁ := by
  obtain ⟨hx, h₁, h₂⟩ := h.mem
  exact almostHomotopic_of_germEquiv hx h₂ h₁ (h.germEquiv.symm h₁ h₂ hx)

theorem AlmostHomotopic.trans {γ₁ γ₂ γ₃ : Path x y} (h : AlmostHomotopic U γ₁ γ₂)
    (h' : AlmostHomotopic U γ₂ γ₃) : AlmostHomotopic U γ₁ γ₃ := by
  obtain ⟨hx, h₁, -⟩ := h.mem
  obtain ⟨-, -, h₃⟩ := h'.mem
  exact almostHomotopic_of_germEquiv hx h₁ h₃ (h.germEquiv.trans h₃ hx h'.germEquiv)

/-- **`lem:hausdorff_first_countable_connected`** (`RamcovGX.tex:1290`). For `x ∈ U`, almost
homotopy with respect to `U` is an equivalence relation on `Ω(x,y,U)`. -/
theorem hausdorff_first_countable_connected (hx : x ∈ U) :
    Equivalence fun γ₁ γ₂ : {γ : Path x y // MemOmega U γ} => AlmostHomotopic U γ₁.1 γ₂.1 :=
  ⟨fun γ => almostHomotopic_refl hx γ.2, fun h => h.symm, fun h h' => h.trans h'⟩

end Germ

/-! ### Lifting paths through a map which is a covering over `s` -/

section Lift

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {p : E → Y} {s : Set Y}

/-- Lifts of a path lying in `s` before time `1` are unique (`E` Hausdorff, `p` a covering
over `s`). -/
theorem lift_unique [T2Space E] (cov : IsCoveringMap (s.restrictPreimage p)) {γ : I → Y}
    (hγ : ∀ t : I, (t : ℝ) < 1 → γ t ∈ s) {Γ₁ Γ₂ : C(I, E)} (h₁ : ∀ t, p (Γ₁ t) = γ t)
    (h₂ : ∀ t, p (Γ₂ t) = γ t) (h0 : Γ₁ 0 = Γ₂ 0) : Γ₁ = Γ₂ := by
  have key : ∀ a : I, (a : ℝ) < 1 → Γ₁ a = Γ₂ a := by
    intro a ha
    have hm : ∀ (Γ : C(I, E)), (∀ t, p (Γ t) = γ t) → ∀ t : I, Γ (t * a) ∈ p ⁻¹' s :=
      fun Γ hΓ t => by
        show p (Γ (t * a)) ∈ s
        rw [hΓ]
        exact hγ _ (by
          rw [Set.Icc.coe_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left a.2.1 t.2.2) ha)
    let f : (Γ : C(I, E)) → (∀ t, p (Γ t) = γ t) → I → p ⁻¹' s :=
      fun Γ hΓ t => ⟨Γ (t * a), hm Γ hΓ t⟩
    have hf : ∀ Γ hΓ, Continuous (f Γ hΓ) := fun Γ hΓ =>
      (Γ.continuous.comp (continuous_id.mul continuous_const)).subtype_mk _
    have := cov.eq_of_comp_eq (hf Γ₁ h₁) (hf Γ₂ h₂) (funext fun t => Subtype.ext (by
      show p (Γ₁ (t * a)) = p (Γ₂ (t * a))
      rw [h₁, h₂])) 0 (Subtype.ext (by
        show Γ₁ (0 * a) = Γ₂ (0 * a)
        rw [zero_mul]; exact h0))
    have h1 := congrArg Subtype.val (congrFun this 1)
    simpa [f] using h1
  ext t
  exact (Continuous.ext_on dense_setOf_lt_one Γ₁.continuous Γ₂.continuous
    (fun t (ht : t < 1) => key t ht)).symm ▸ rfl

/-- Lifts exist through a complete spread which is a covering over `s`. -/
theorem exists_lift [T1Space Y] [LocallyConnectedSpace Y] (hp : IsSpread p)
    (hc : IsCompleteSpread p) (cov : IsCoveringMap (s.restrictPreimage p)) (γ : C(I, Y))
    (hγ : ∀ t : I, (t : ℝ) < 1 → γ t ∈ s) {e : E} (he : p e = γ 0) :
    ∃ Γ : C(I, E), (∀ t, p (Γ t) = γ t) ∧ Γ 0 = e := by
  obtain ⟨f, hf, hf0, hfs⟩ := exists_partial_lift cov γ (fun t ht => hγ t ht)
    (he ▸ hγ 0 (by simp)) he
  obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp hc γ f hf
    (fun t ht => (hfs t ht).2)
  exact ⟨g, hg, by rw [hgf 0 (by exact zero_lt_one), hf0]⟩

/-- Lifts of paths homotopic in `s` end at the same point. -/
theorem lift_end_eq_of_homotopicIn (cov : IsCoveringMap (s.restrictPreimage p)) {a b : Y}
    {δ δ' : Path a b} (h : HomotopicIn s δ δ') {Δ Δ' : C(I, E)} (hΔ : ∀ t, p (Δ t) = δ t)
    (hΔ' : ∀ t, p (Δ' t) = δ' t) (h0 : Δ 0 = Δ' 0) : Δ 1 = Δ' 1 := by
  obtain ⟨h₁, h₂, hom⟩ := homotopicIn_iff.1 h
  have hm : ∀ t, Δ t ∈ p ⁻¹' s := fun t => by show p (Δ t) ∈ s; rw [hΔ]; exact h₁ t
  have hm' : ∀ t, Δ' t ∈ p ⁻¹' s := fun t => by show p (Δ' t) ∈ s; rw [hΔ']; exact h₂ t
  set e : p ⁻¹' s := ⟨Δ 0, hm 0⟩
  let D : C(I, p ⁻¹' s) := ⟨fun t => ⟨Δ t, hm t⟩, Δ.continuous.subtype_mk _⟩
  let D' : C(I, p ⁻¹' s) := ⟨fun t => ⟨Δ' t, hm' t⟩, Δ'.continuous.subtype_mk _⟩
  have he0 : (pathToSub δ h₁).toContinuousMap 0 = s.restrictPreimage p e :=
    Subtype.ext (by simp [e, hΔ])
  have he0' : (pathToSub δ' h₂).toContinuousMap 0 = s.restrictPreimage p e :=
    Subtype.ext (by simp [e, h0, hΔ'])
  have hD : D = cov.liftPath (pathToSub δ h₁).toContinuousMap e he0 :=
    (cov.eq_liftPath_iff' he0).2 ⟨funext fun t => Subtype.ext (hΔ t), rfl⟩
  have hD' : D' = cov.liftPath (pathToSub δ' h₂).toContinuousMap e he0' :=
    (cov.eq_liftPath_iff' he0').2 ⟨funext fun t => Subtype.ext (hΔ' t), Subtype.ext h0.symm⟩
  have := cov.liftPath_apply_one_eq_of_homotopicRel hom e he0 he0'
  rw [← hD, ← hD'] at this
  exact congrArg Subtype.val this

end Lift

section Lift2

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {p : E → Y} {s : Set Y}

/-- A path all of whose values lie in `s` lifts through a covering over `s`. -/
theorem exists_lift_of_mem (cov : IsCoveringMap (s.restrictPreimage p)) {a b : Y}
    (δ : Path a b) (h : ∀ t, δ t ∈ s) {e : E} (he : p e = a) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = δ t) ∧ Δ 0 = e := by
  have he' : p e ∈ s := by rw [he]; exact δ.source ▸ h 0
  have h0 : (pathToSub δ h).toContinuousMap 0 = s.restrictPreimage p ⟨e, he'⟩ :=
    Subtype.ext (by simp [he])
  set L := cov.liftPath (pathToSub δ h).toContinuousMap ⟨e, he'⟩ h0
  refine ⟨⟨fun t => (L t : E), continuous_subtype_val.comp L.continuous⟩, fun t => ?_, ?_⟩
  · have := congrFun (cov.liftPath_lifts (pathToSub δ h).toContinuousMap ⟨e, he'⟩ h0) t
    exact congrArg Subtype.val this
  · show (L 0 : E) = e
    rw [cov.liftPath_zero]

/-- The lift of a head is the restriction of the lift. -/
theorem lift_head {x y : Y} {γ : Path x y} {Γ : C(I, E)} (hΓ : ∀ t, p (Γ t) = γ t) (s₀ : I) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = head γ s₀ t) ∧ Δ 0 = Γ 0 ∧ Δ 1 = Γ s₀ := by
  refine ⟨⟨fun t => Γ (t * s₀), Γ.continuous.comp (continuous_id.mul continuous_const)⟩,
    fun t => ?_, by simp, by simp⟩
  show p (Γ (t * s₀)) = head γ s₀ t
  rw [hΓ, head_apply, subpath_apply']
  have hm : (1 - (t : ℝ)) * ((0 : I) : ℝ) + t * s₀ ∈ I := by
    simp only [Icc.coe_zero, mul_zero, zero_add]
    exact (t * s₀).2
  rw [Path.extend_apply γ hm]
  congr 1
  exact Subtype.ext (by simp)

/-- The lift of a concatenation is the concatenation of the lifts. -/
theorem lift_trans {a b c : Y} {A : Path a b} {B : Path b c} {ΔA ΔB : C(I, E)}
    (hA : ∀ t, p (ΔA t) = A t) (hB : ∀ t, p (ΔB t) = B t) (h : ΔB 0 = ΔA 1) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = (A.trans B) t) ∧ Δ 0 = ΔA 0 ∧ Δ 1 = ΔB 1 := by
  set PA : Path (ΔA 0) (ΔA 1) := ⟨ΔA, rfl, rfl⟩
  set PB : Path (ΔA 1) (ΔB 1) := ⟨ΔB, h, rfl⟩
  refine ⟨(PA.trans PB).toContinuousMap, fun t => ?_, (PA.trans PB).source,
    (PA.trans PB).target⟩
  show p ((PA.trans PB) t) = (A.trans B) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hA _
  · exact hB _

theorem HomotopicIn.map {Z : Type*} [TopologicalSpace Z] {U : Set Z} {V : Set Y} {f : Z → Y}
    (hf : Continuous f) (hfU : MapsTo f U V) {a b : Z} {P Q : Path a b}
    (h : HomotopicIn U P Q) : HomotopicIn V (P.map hf) (Q.map hf) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.map ⟨f, hf⟩, fun w => hfU (hF w)⟩

end Lift2

/-! ### `lem:almost_homotopic_carac2` -/

section Carac2

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- `lem:almost_homotopic_carac2`, "if" half, for **any** spread `p` which is a covering over
`Y ∖ S` (no maximality, no simple connectivity): lifts of almost homotopic paths from the same
point end at the same point. -/
theorem lift_end_eq_of_almostHomotopic [T1Space E] [LocallyConnectedSpace Y] {p : E → Y}
    (hp : IsSpread p) {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p)) {x y : Y}
    {γ₁ γ₂ : Path x y} (h : AlmostHomotopic Sᶜ γ₁ γ₂) {Γ₁ Γ₂ : C(I, E)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 := by
  haveI := hp.locallyConnectedSpace
  have hg := h.germEquiv
  suffices key : ∀ N : Set E, IsOpen N → Γ₂ 1 ∈ N → Γ₁ 1 ∈ N by
    by_contra hne
    exact key {Γ₁ 1}ᶜ isOpen_compl_singleton (Ne.symm hne) rfl
  intro N hN hmem
  obtain ⟨V, hV, hyV, hVN⟩ := (isSpread_iff.1 hp).2.2 (Γ₂ 1) N hN hmem
  have hy : p (Γ₂ 1) = y := by rw [hΓ₂, γ₂.target]
  rw [hy] at hyV
  set V' := connectedComponentIn V y
  have hV' : IsOpen V' := hV.connectedComponentIn
  have hyV' : y ∈ V' := mem_connectedComponentIn hyV
  set W := connectedComponentIn (p ⁻¹' V') (Γ₂ 1) with hWdef
  have hW : IsOpen W := (hV'.preimage hp.continuous).connectedComponentIn
  have hmemW : Γ₂ 1 ∈ W := mem_connectedComponentIn (show p (Γ₂ 1) ∈ V' by rw [hy]; exact hyV')
  have hWN : W ⊆ N := (connectedComponentIn_mono _ (preimage_mono
    (connectedComponentIn_subset V y))).trans hVN
  have hWV' : ∀ e ∈ W, p e ∈ V' := fun e he =>
    (connectedComponentIn_subset (p ⁻¹' V') _ he : e ∈ p ⁻¹' V')
  obtain ⟨s₂, -, hs₂, ht₂W⟩ := exists_tail_mem (⟨Γ₂, rfl, rfl⟩ : Path (Γ₂ 0) (Γ₂ 1))
    (hW.mem_nhds hmemW) (c := 1) one_pos
  obtain ⟨s₁, -, hs₁, ht₁⟩ := exists_tail_mem γ₁ (hV'.mem_nhds hyV') (c := 1) one_pos
  have ht₂ : ∀ t : I, (s₂ : ℝ) ≤ t → γ₂ t ∈ V' := fun t ht => by
    rw [← hΓ₂]; exact hWV' _ (ht₂W t ht)
  obtain ⟨ω, hω, hh⟩ := hg V' hV' hyV' s₁ s₂ hs₁ hs₂ ht₁ ht₂
  obtain ⟨Δ₁, hΔ₁, hΔ₁0, hΔ₁1⟩ := lift_head hΓ₁ s₁
  obtain ⟨Δ₂, hΔ₂, hΔ₂0, hΔ₂1⟩ := lift_head hΓ₂ s₂
  obtain ⟨Ωl, hΩl, hΩl0⟩ := exists_lift_of_mem cov ω (fun t => (hω t).2) (hΓ₂ s₂)
  obtain ⟨Δ, hΔ, hΔ0, hΔ1⟩ := lift_trans hΔ₂ hΩl (hΩl0.trans hΔ₂1.symm)
  have heq := lift_end_eq_of_homotopicIn cov hh hΔ₁ hΔ (by rw [hΔ₁0, hΔ0, hΔ₂0, h0])
  rw [hΔ₁1, hΔ1] at heq
  have hΩW : range Ωl ⊆ W := by
    have h1 : Ωl 0 ∈ W := by rw [hΩl0]; exact ht₂W s₂ le_rfl
    rw [hWdef, connectedComponentIn_eq h1]
    exact (isPreconnected_range Ωl.continuous).subset_connectedComponentIn (mem_range_self 0)
      (by rintro _ ⟨t, rfl⟩; show p (Ωl t) ∈ V'; rw [hΩl]; exact (hω t).1)
  have hs₁W : Γ₁ s₁ ∈ W := heq ▸ hΩW (mem_range_self 1)
  have hseg : Γ₁ '' Icc s₁ 1 ⊆ W := by
    rw [hWdef, connectedComponentIn_eq hs₁W]
    exact (isPreconnected_Icc.image _ Γ₁.continuous.continuousOn).subset_connectedComponentIn
      ⟨s₁, ⟨le_rfl, s₁.2.2⟩, rfl⟩ (by
        rintro _ ⟨t, ht, rfl⟩
        show p (Γ₁ t) ∈ V'
        rw [hΓ₁]; exact ht₁ t ht.1)
  exact hWN (hseg ⟨1, ⟨s₁.2.2, le_rfl⟩, rfl⟩)

/-- `lem:almost_homotopic_carac2`, "only if" half, for a branched covering possibly branched
over a skeletal `S` whose part over `Y ∖ S` is simply connected: lifts ending at the same point
come from almost homotopic paths. -/
theorem almostHomotopic_of_lift_end_eq [LocPathConnectedSpace E] {p : E → Y}
    (hp : IsBranchedCovering p) {S : Set Y} (hS : IsSkeletal S)
    [SimplyConnectedSpace (p ⁻¹' Sᶜ)] {x y : Y} (hx : x ∈ Sᶜ) {γ₁ γ₂ : Path x y}
    (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂) {Γ₁ Γ₂ : C(I, E)} (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t)
    (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) (h1 : Γ₁ 1 = Γ₂ 1) :
    AlmostHomotopic Sᶜ γ₁ γ₂ := by
  refine almostHomotopic_of_germEquiv hx h₁ h₂ ?_
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  set e := Γ₂ 1
  have hpe : p e = y := by rw [hΓ₂, γ₂.target]
  set W := connectedComponentIn (p ⁻¹' V) e with hWdef
  have hpV : IsOpen (p ⁻¹' V) := hV.preimage hp.isSpread.continuous
  have hW : IsOpen W := hpV.connectedComponentIn
  have heW : e ∈ W := mem_connectedComponentIn (show p e ∈ V by rw [hpe]; exact hyV)
  have hWV : ∀ z ∈ W, p z ∈ V := fun z hz =>
    (connectedComponentIn_subset (p ⁻¹' V) _ hz : z ∈ p ⁻¹' V)
  have tailW : ∀ (Γ : C(I, E)) (γ : Path x y), (∀ t, p (Γ t) = γ t) → Γ 1 = e → ∀ s₀ : I,
      (∀ t : I, (s₀ : ℝ) ≤ t → γ t ∈ V) → Γ s₀ ∈ W := by
    intro Γ γ hΓ he s₀ ht
    have hseg : Γ '' Icc s₀ 1 ⊆ W := by
      rw [hWdef, ← he]
      exact (isPreconnected_Icc.image _ Γ.continuous.continuousOn).subset_connectedComponentIn
        ⟨1, ⟨s₀.2.2, le_rfl⟩, rfl⟩ (by
          rintro _ ⟨t, ht', rfl⟩
          show p (Γ t) ∈ V
          rw [hΓ]; exact ht t ht'.1)
    exact hseg ⟨s₀, ⟨le_rfl, s₀.2.2⟩, rfl⟩
  have hW₁ := tailW Γ₁ γ₁ hΓ₁ h1 s₁ ht₁
  have hW₂ := tailW Γ₂ γ₂ hΓ₂ rfl s₂ ht₂
  have hE₁ : Γ₁ s₁ ∈ p ⁻¹' Sᶜ := by
    show p (Γ₁ s₁) ∈ Sᶜ
    rw [hΓ₁, ← Path.extend_extends' γ₁ s₁]; exact h₁.extend_mem hx hs₁
  have hE₂ : Γ₂ s₂ ∈ p ⁻¹' Sᶜ := by
    show p (Γ₂ s₂) ∈ Sᶜ
    rw [hΓ₂, ← Path.extend_extends' γ₂ s₂]; exact h₂.extend_mem hx hs₂
  have hWc : IsConnected W := ⟨⟨e, heW⟩, isPreconnected_connectedComponentIn⟩
  have hpc : IsPathConnected (W ∩ p ⁻¹' Sᶜ) :=
    (hW.inter hE.isOpen).isConnected_iff_isPathConnected.1 (hE.isConnected_inter hW hWc)
  have hj := hpc.joinedIn _ ⟨hW₂, hE₂⟩ _ ⟨hW₁, hE₁⟩
  set ωl := hj.somePath
  have hωl : ∀ t, ωl t ∈ W ∩ p ⁻¹' Sᶜ := hj.somePath_mem
  set ω : Path (γ₂ s₂) (γ₁ s₁) := (ωl.map hp.isSpread.continuous).cast (hΓ₂ s₂).symm
    (hΓ₁ s₁).symm
  have hωV : ∀ τ, ω τ ∈ V ∩ Sᶜ := fun τ => ⟨hWV _ (hωl τ).1, (hωl τ).2⟩
  refine ⟨ω, hωV, ?_⟩
  -- lifts of both sides inside `p ⁻¹' Sᶜ`
  obtain ⟨Δ₁, hΔ₁, hΔ₁0, hΔ₁1⟩ := lift_head hΓ₁ s₁
  obtain ⟨Δ₂, hΔ₂, hΔ₂0, hΔ₂1⟩ := lift_head hΓ₂ s₂
  set P₁ : Path (Γ₁ 0) (Γ₁ s₁) := ⟨Δ₁, hΔ₁0, hΔ₁1⟩
  set P₂ : Path (Γ₁ 0) (Γ₂ s₂) := ⟨Δ₂, hΔ₂0.trans h0.symm, hΔ₂1⟩
  have hP₁ : ∀ t, P₁ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Δ₁ t) ∈ Sᶜ; rw [hΔ₁]; exact head_mem h₁ hx hs₁ t
  have hP₂ : ∀ t, (P₂.trans ωl) t ∈ p ⁻¹' Sᶜ := path_trans_mem (fun t => by
    show p (Δ₂ t) ∈ Sᶜ; rw [hΔ₂]; exact head_mem h₂ hx hs₂ t) (fun t => (hωl t).2)
  have hhom : HomotopicIn (p ⁻¹' Sᶜ) P₁ (P₂.trans ωl) :=
    homotopicIn_iff.2 ⟨hP₁, hP₂, SimplyConnectedSpace.paths_homotopic _ _⟩
  have hmap := (hhom.map hp.isSpread.continuous (fun z hz => hz)).cast
    (show x = p (Γ₁ 0) by rw [hΓ₁, γ₁.source]) (hΓ₁ s₁).symm
  refine hmap.of_eq ?_ ?_
  · ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply]
    exact hΔ₁ t
  · ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply]
    split_ifs
    · exact hΔ₂ _
    · rfl

end Carac2

section MaxCover

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- The lifting facts of `\widetilde Y^S` used in §3.3: a covering over `Y ∖ S`, with a simply
connected part over `Y ∖ S` (it is `\widetilde{Y ∖ S}`). -/
theorem maxBranched_lifting (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) :
    IsCoveringMap (Sᶜ.restrictPreimage (SpreadEnd.base : MaxBranchedCover S y₀ → Y)) ∧
      SimplyConnectedSpace ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ) := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  obtain ⟨-, hbc, hpb, hpre, -, hsp⟩ := maxBranched_basic hS hSc y₀
  have hOp : (Sᶜ : Set Y) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := fun y hy => by
    by_contra h
    exact hy (hpb h)
  refine ⟨(hbc.restrict_isCoveringMap hO hOp).1, ?_⟩
  haveI : T2Space (UniversalCover (Sᶜ : Set Y) y₀) :=
    t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc)
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hSc
  have hemb₁ := SpreadEnd.isEmbedding_ofPoint hsp
  set ψ : UniversalCover (Sᶜ : Set Y) y₀ ≃ₜ
      ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ) :=
    hemb₁.toHomeomorph.trans (Homeomorph.setCongr hpre.symm)
  exact ψ.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Paths of `Ω(x,y,Y ∖ S)`, `x ∈ Y ∖ S`, lift uniquely to `\widetilde Y^S` from any point over
`x` ("the respective lifts" of `lem:almost_homotopic_carac2`). -/
theorem maxBranched_existsUnique_lift (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {x y : Y} (hx : x ∈ Sᶜ)
    {γ : Path x y} (hγ : MemOmega Sᶜ γ) {e : MaxBranchedCover S y₀} (he : e.base = x) :
    ∃! Γ : C(I, MaxBranchedCover S y₀), (∀ t, (Γ t).base = γ t) ∧ Γ 0 = e := by
  obtain ⟨-, hbc, -, -, -, -⟩ := maxBranched_basic hS hSc y₀
  obtain ⟨cov, -⟩ := maxBranched_lifting hS hSc y₀
  have hγs : ∀ t : I, (t : ℝ) < 1 → γ t ∈ Sᶜ := fun t ht => by
    rw [← Path.extend_extends' γ t]; exact hγ.extend_mem hx ht
  obtain ⟨Γ, hΓ, hΓ0⟩ := exists_lift hbc.isSpread hbc.isComplete cov γ.toContinuousMap hγs
    (by rw [he]; exact γ.source.symm)
  exact ⟨Γ, ⟨hΓ, hΓ0⟩, fun Γ' ⟨hΓ', hΓ'0⟩ =>
    lift_unique cov hγs hΓ' hΓ (hΓ'0.trans hΓ0.symm)⟩

/-- **`lem:almost_homotopic_carac2`** (`RamcovGX.tex:1306`). Let `\widetilde Y^S → Y` be the
maximal covering possibly branched over `S` (`Y ∖ S` semilocally simply connected), `x ∈ Y ∖ S`,
`γ₁, γ₂ ∈ Ω(x,y,Y ∖ S)` and `Γ₁, Γ₂` their lifts from the same point. Then
`Γ₁(1) = Γ₂(1)` iff `γ₁` and `γ₂` are almost homotopic. -/
theorem almost_homotopic_carac2 (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂)
    {Γ₁ Γ₂ : C(I, MaxBranchedCover S y₀)} (hΓ₁ : ∀ t, (Γ₁ t).base = γ₁ t)
    (hΓ₂ : ∀ t, (Γ₂ t).base = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopic Sᶜ γ₁ γ₂ := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, hsc⟩ := maxBranched_lifting hS hSc y₀
  haveI := hsc
  exact ⟨fun h1 => almostHomotopic_of_lift_end_eq hbc hS hx h₁ h₂ hΓ₁ hΓ₂ h0 h1,
    fun h => lift_end_eq_of_almostHomotopic hbc.isSpread cov h hΓ₁ hΓ₂ h0⟩

/-- `lem:almost_homotopic_carac2` for **any** maximal covering `p : X → Y` possibly branched
over `S` (transported along `GX.IsMaximalPossiblyBranched.nonempty_homeomorph`). -/
theorem almost_homotopic_carac2_of_isMaximal (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X] [FirstCountableTopology X]
    {p : X → Y} (hp : IsMaximalPossiblyBranched.{u} p S) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂) {Γ₁ Γ₂ : C(I, X)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopic Sᶜ γ₁ γ₂ := by
  obtain ⟨Φ, hΦ⟩ := hp.nonempty_homeomorph hS hSc y₀
  have hb : ∀ (Γ : C(I, X)) (γ : Path x y), (∀ t, p (Γ t) = γ t) →
      ∀ t, ((ContinuousMap.comp ⟨Φ.symm, Φ.symm.continuous⟩ Γ) t).base = γ t := fun Γ γ hΓ t => by
    show (Φ.symm (Γ t)).base = γ t
    rw [← hΦ, Φ.apply_symm_apply, hΓ]
  rw [← almost_homotopic_carac2 hS hSc y₀ hx h₁ h₂ (hb Γ₁ γ₁ hΓ₁) (hb Γ₂ γ₂ hΓ₂)
    (by show Φ.symm (Γ₁ 0) = Φ.symm (Γ₂ 0); rw [h0])]
  exact ⟨fun h => by show Φ.symm (Γ₁ 1) = Φ.symm (Γ₂ 1); rw [h],
    fun h => Φ.symm.injective h⟩

end MaxCover

/-! ### Gluing a path to the end of another, and perturbing tails in the compact-open topology -/

section Glue

variable {Z : Type*} [TopologicalSpace Z]

/-- Follow `f` on `[0,t₀]`, then `g` (affinely rescaled) on `[t₀,1]`. -/
def glue (f : C(I, Z)) (t₀ : I) (_h : (t₀ : ℝ) < 1) (g : C(I, Z)) (hg : g 0 = f t₀) : C(I, Z) where
  toFun t := if (t : ℝ) ≤ t₀ then f t else g (Set.projIcc 0 1 zero_le_one ((t - t₀) / (1 - t₀)))
  continuous_toFun := by
    refine Continuous.if_le f.continuous (g.continuous.comp (continuous_projIcc.comp (by fun_prop)))
      (by fun_prop) continuous_const fun t ht => ?_
    rw [ht, projIcc_sub_self_div, hg]
    congr 1
    exact Subtype.ext ht

variable {f : C(I, Z)} {t₀ : I} {h : (t₀ : ℝ) < 1} {g : C(I, Z)} {hg : g 0 = f t₀}

theorem glue_apply_le {t : I} (ht : (t : ℝ) ≤ t₀) : glue f t₀ h g hg t = f t := by
  show (if (t : ℝ) ≤ t₀ then _ else _) = _
  rw [if_pos ht]

theorem glue_apply_gt {t : I} (ht : (t₀ : ℝ) < t) :
    glue f t₀ h g hg t = g (Set.projIcc 0 1 zero_le_one ((t - t₀) / (1 - t₀))) := by
  show (if (t : ℝ) ≤ t₀ then _ else _) = _
  rw [if_neg (not_le.2 ht)]

theorem glue_zero : glue f t₀ h g hg 0 = f 0 := glue_apply_le (by simp [t₀.2.1])

theorem glue_one : glue f t₀ h g hg 1 = g 1 := by
  rw [glue_apply_gt (by simpa using h)]
  congr 1
  rw [Icc.coe_one]
  exact projIcc_div_self h

theorem glue_mem (t : I) : ((t : ℝ) ≤ t₀ ∧ glue f t₀ h g hg t = f t) ∨
    ∃ r : I, glue f t₀ h g hg t = g r ∧ ((t : ℝ) < 1 → (r : ℝ) < 1) := by
  rcases le_or_gt (t : ℝ) t₀ with ht | ht
  · exact Or.inl ⟨ht, glue_apply_le ht⟩
  · refine Or.inr ⟨_, glue_apply_gt ht, fun ht1 => ?_⟩
    rw [projIcc_mid h ht.le t.2.2]
    have : 0 < 1 - (t₀ : ℝ) := sub_pos.2 h
    rw [div_lt_one this]; linarith

theorem glue_map {Z' : Type*} [TopologicalSpace Z'] {φ : Z → Z'} {f' g' : C(I, Z')}
    (hf : ∀ t, φ (f t) = f' t) (hg' : ∀ t, φ (g t) = g' t) (hg'' : g' 0 = f' t₀) (t : I) :
    φ (glue f t₀ h g hg t) = glue f' t₀ h g' hg'' t := by
  rcases le_or_gt (t : ℝ) t₀ with ht | ht
  · rw [glue_apply_le ht, glue_apply_le ht, hf]
  · rw [glue_apply_gt ht, glue_apply_gt ht, hg']

end Glue

section Perturb

variable {Y : Type*} [TopologicalSpace Y]

theorem coe_maxI (a b : I) : ((max a b : I) : ℝ) = max (a : ℝ) b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Subtype.coe_le_coe.2 h)]
  · rw [max_eq_left h, max_eq_left (Subtype.coe_le_coe.2 h)]

/-- **Tails in the compact-open topology.** A neighbourhood of a path `γ` contains every path
agreeing with `γ` on some `[0,t₀]`, `t₀ < 1`, and staying in some neighbourhood of `γ(1)` after
`t₀`. -/
theorem exists_tail_perturb {γ : C(I, Y)} {O : Set C(I, Y)} (hO : O ∈ 𝓝 γ) :
    ∃ t₀ : I, (t₀ : ℝ) < 1 ∧ ∃ V ∈ 𝓝 (γ 1), (∀ t : I, (t₀ : ℝ) ≤ t → γ t ∈ V) ∧
      ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₀ → f t = γ t) → (∀ t : I, (t₀ : ℝ) ≤ t → f t ∈ V) →
        f ∈ O := by
  let P : Set C(I, Y) → Prop := fun O => ∃ t₀ : I, (t₀ : ℝ) < 1 ∧ ∃ V ∈ 𝓝 (γ 1),
    (∀ t : I, (t₀ : ℝ) ≤ t → γ t ∈ V) ∧
      ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₀ → f t = γ t) → (∀ t : I, (t₀ : ℝ) ≤ t → f t ∈ V) →
        f ∈ O
  let 𝓕 : Filter C(I, Y) :=
    { sets := {O | P O}
      univ_sets := ⟨0, by simp, univ, univ_mem, fun _ _ => mem_univ _, fun _ _ _ => mem_univ _⟩
      sets_of_superset := fun {O O'} ⟨t₀, h1, V, hV, hγV, hf⟩ hOO' =>
        ⟨t₀, h1, V, hV, hγV, fun f h₁ h₂ => hOO' (hf f h₁ h₂)⟩
      inter_sets := fun {O O'} ⟨t₁, h1, V₁, hV₁, hγV₁, hf₁⟩ ⟨t₂, h2, V₂, hV₂, hγV₂, hf₂⟩ => by
        refine ⟨max t₁ t₂, by rw [coe_maxI]; exact max_lt h1 h2, V₁ ∩ V₂, inter_mem hV₁ hV₂,
          fun t ht => ⟨hγV₁ t ((le_max_left _ _).trans (by rwa [coe_maxI] at ht)),
            hγV₂ t ((le_max_right _ _).trans (by rwa [coe_maxI] at ht))⟩, fun f hf hfV => ?_⟩
        rw [coe_maxI] at hf hfV
        refine ⟨hf₁ f (fun t ht => hf t (ht.trans (le_max_left _ _))) fun t ht => ?_,
          hf₂ f (fun t ht => hf t (ht.trans (le_max_right _ _))) fun t ht => ?_⟩
        · rcases le_total (t : ℝ) (max (t₁ : ℝ) t₂) with h | h
          · rw [hf t h]; exact hγV₁ t ht
          · exact (hfV t h).1
        · rcases le_total (t : ℝ) (max (t₁ : ℝ) t₂) with h | h
          · rw [hf t h]; exact hγV₂ t ht
          · exact (hfV t h).2 }
  suffices hle : 𝓕 ≤ 𝓝 γ from hle hO
  rw [ContinuousMap.nhds_compactOpen]
  refine le_iInf₂ fun K hK => le_iInf₂ fun U hU => le_iInf fun hγ => le_principal_iff.2 ?_
  by_cases h1 : (1 : I) ∈ K
  · have hU1 : U ∈ 𝓝 (γ 1) := hU.mem_nhds (hγ h1)
    obtain ⟨t₀, -, ht₀, htail⟩ := exists_tail_mem (⟨γ, rfl, rfl⟩ : Path (γ 0) (γ 1)) hU1
      (c := 1) one_pos
    refine ⟨t₀, ht₀, U, hU1, htail, fun f hf hfU k hk => ?_⟩
    rcases le_total (k : ℝ) t₀ with h | h
    · show f k ∈ U; rw [hf k h]; exact hγ hk
    · exact hfU k h
  · rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, by simp, univ, univ_mem, fun _ _ => mem_univ _, fun f _ _ => by
        rw [hKe]; exact mapsTo_empty _ _⟩
    · obtain ⟨m, hmK, hm⟩ := hK.exists_isGreatest hKne
      have hm1 : (m : ℝ) < 1 := lt_of_le_of_ne m.2.2 fun h => h1 (by
        rw [show (1 : I) = m from Subtype.ext h.symm]; exact hmK)
      refine ⟨m, hm1, univ, univ_mem, fun _ _ => mem_univ _, fun f hf _ k hk => ?_⟩
      show f k ∈ U
      rw [hf k (hm hk)]; exact hγ hk

end Perturb

/-! ### `theo:ramified_covering_path` -/

section Ramified

universe u

variable {Y : Type u} [TopologicalSpace Y]

/-- `Ω = ⋃_{x ∈ Y} Ω(y₀, x, Y ∖ S)` (`RamcovGX.tex:1324`), as a subspace of `C([0,1], Y)` with the
compact-open topology. -/
def OmegaSpace (S : Set Y) (y₀ : Y) : Set C(I, Y) :=
  {γ | γ 0 = y₀ ∧ ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∈ Sᶜ}

variable {S : Set Y} {y₀ : Y}

/-- An element of `Ω` as a path `y₀ ⇝ γ(1)`. -/
def OmegaSpace.toPath (γ : OmegaSpace S y₀) : Path y₀ (γ.1 1) := ⟨γ.1, γ.2.1, rfl⟩

theorem OmegaSpace.memOmega (γ : OmegaSpace S y₀) : MemOmega Sᶜ (OmegaSpace.toPath γ) := γ.2.2

theorem OmegaSpace.mem_compl (hy₀ : y₀ ∈ Sᶜ) (γ : OmegaSpace S y₀) {t : I} (ht : (t : ℝ) < 1) :
    γ.1 t ∈ Sᶜ := by
  rcases eq_or_lt_of_le t.2.1 with h | h
  · rw [show t = 0 from Subtype.ext h.symm, γ.2.1]; exact hy₀
  · exact γ.2.2 t h ht

theorem AlmostHomotopic.cast {U : Set Y} {x y : Y} {γ₁ γ₂ : Path x y}
    (h : AlmostHomotopic U γ₁ γ₂) {x' y' : Y} (hx : x' = x) (hy : y' = y) :
    AlmostHomotopic U (γ₁.cast hx hy) (γ₂.cast hx hy) := by
  subst hx; subst hy; exact h

/-- Almost homotopy with respect to `Y ∖ S` on `Ω` (paths with the same end). -/
def OmegaRel (S : Set Y) (y₀ : Y) (γ γ' : OmegaSpace S y₀) : Prop :=
  ∃ h : γ.1 1 = γ'.1 1, AlmostHomotopic Sᶜ (OmegaSpace.toPath γ) ((OmegaSpace.toPath γ').cast rfl h)

theorem omegaRel_equivalence (hy₀ : y₀ ∈ Sᶜ) : Equivalence (OmegaRel S y₀) where
  refl γ := ⟨rfl, almostHomotopic_refl hy₀ (OmegaSpace.memOmega γ)⟩
  symm := fun ⟨h, H⟩ => ⟨h.symm, H.symm.cast rfl h.symm⟩
  trans := fun ⟨h, H⟩ ⟨h', H'⟩ => ⟨h.trans h', H.trans (H'.cast rfl h)⟩

/-- The setoid of almost homotopy classes on `Ω` (`y₀ ∈ Y ∖ S`). -/
def omegaSetoid (S : Set Y) (y₀ : (Sᶜ : Set Y)) : Setoid (OmegaSpace S (y₀ : Y)) :=
  ⟨OmegaRel S y₀, omegaRel_equivalence y₀.2⟩

/-- `X`: the almost homotopy classes of `Ω` with respect to `Y ∖ S`, with the quotient
topology. -/
abbrev OmegaQuot (S : Set Y) (y₀ : (Sᶜ : Set Y)) : Type u := Quotient (omegaSetoid S y₀)

/-- `\overline φ : X → Y`, induced by `φ : γ ↦ γ(1)`. -/
def omegaEnd (S : Set Y) (y₀ : (Sᶜ : Set Y)) : OmegaQuot S y₀ → Y :=
  Quotient.lift (fun γ : OmegaSpace S (y₀ : Y) => γ.1 1) fun _ _ h => h.1

end Ramified

section RamifiedMain

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- The base point `ŷ₀` of `\widetilde Y^S` over `y₀`. -/
def maxBase (S : Set Y) (y₀ : (Sᶜ : Set Y)) : MaxBranchedCover S y₀ :=
  SpreadEnd.ofPoint (univCoverProj S y₀) (UniversalCover.base y₀)

theorem maxBase_base (y₀ : (Sᶜ : Set Y)) : (maxBase S y₀).base = y₀ := rfl

/-- The lift from `ŷ₀` of a path of `Ω`. -/
def omegaLift (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (γ : OmegaSpace S (y₀ : Y)) : C(I, MaxBranchedCover S y₀) :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).exists.choose

variable (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y))

theorem omegaLift_spec (γ : OmegaSpace S (y₀ : Y)) :
    (∀ t, (omegaLift hS hSc y₀ γ t).base = γ.1 t) ∧ omegaLift hS hSc y₀ γ 0 = maxBase S y₀ :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).exists.choose_spec

theorem omegaLift_unique (γ : OmegaSpace S (y₀ : Y)) {Γ : C(I, MaxBranchedCover S y₀)}
    (hΓ : ∀ t, (Γ t).base = γ.1 t) (h0 : Γ 0 = maxBase S y₀) : Γ = omegaLift hS hSc y₀ γ :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).unique ⟨hΓ, h0⟩ (omegaLift_spec hS hSc y₀ γ)

/-- `ψ` is constant exactly on the almost homotopy classes (`lem:almost_homotopic_carac2`). -/
theorem omegaLift_one_eq_iff (γ γ' : OmegaSpace S (y₀ : Y)) :
    omegaLift hS hSc y₀ γ 1 = omegaLift hS hSc y₀ γ' 1 ↔ OmegaRel S y₀ γ γ' := by
  constructor
  · intro h1
    have hb : γ.1 1 = γ'.1 1 := by
      rw [← (omegaLift_spec hS hSc y₀ γ).1, ← (omegaLift_spec hS hSc y₀ γ').1, h1]
    exact ⟨hb, (almost_homotopic_carac2 hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
      (γ₂ := (OmegaSpace.toPath γ').cast rfl hb) (OmegaSpace.memOmega γ')
      (omegaLift_spec hS hSc y₀ γ).1 (omegaLift_spec hS hSc y₀ γ').1
      ((omegaLift_spec hS hSc y₀ γ).2.trans (omegaLift_spec hS hSc y₀ γ').2.symm)).1 h1⟩
  · rintro ⟨hb, H⟩
    exact (almost_homotopic_carac2 hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
      (γ₂ := (OmegaSpace.toPath γ').cast rfl hb) (OmegaSpace.memOmega γ')
      (omegaLift_spec hS hSc y₀ γ).1 (omegaLift_spec hS hSc y₀ γ').1
      ((omegaLift_spec hS hSc y₀ γ).2.trans (omegaLift_spec hS hSc y₀ γ').2.symm)).2 H

omit [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] [ConnectedSpace Y] in
/-- The tail of a path lying over `V` stays in one component of `p ⁻¹' V`. -/
theorem comp_tail {E : Type*} [TopologicalSpace E] {p : E → Y} {Γ : C(I, E)} {V : Set Y}
    {t₀ : I} (h : ∀ t : I, (t₀ : ℝ) ≤ t → p (Γ t) ∈ V) :
    (∀ t : I, (t₀ : ℝ) ≤ t → Γ t ∈ connectedComponentIn (p ⁻¹' V) (Γ t₀)) ∧
      connectedComponentIn (p ⁻¹' V) (Γ t₀) = connectedComponentIn (p ⁻¹' V) (Γ 1) := by
  have hsub : Γ '' Icc t₀ 1 ⊆ connectedComponentIn (p ⁻¹' V) (Γ t₀) :=
    (isPreconnected_Icc.image _ Γ.continuous.continuousOn).subset_connectedComponentIn
      ⟨t₀, ⟨le_rfl, t₀.2.2⟩, rfl⟩ (by
        rintro _ ⟨t, ht, rfl⟩
        exact h t ht.1)
  have hm : ∀ t : I, (t₀ : ℝ) ≤ t → Γ t ∈ connectedComponentIn (p ⁻¹' V) (Γ t₀) :=
    fun t ht => hsub ⟨t, ⟨ht, t.2.2⟩, rfl⟩
  exact ⟨hm, connectedComponentIn_eq (hm 1 t₀.2.2)⟩

/-- `ψ : Ω → \widetilde Y^S` is continuous (the second item of the proof of
`theo:ramified_covering_path`; here through the homotopy lifting property over `Y ∖ S`). -/
theorem continuous_omegaLift_one :
    Continuous fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, -⟩ := maxBranched_lifting hS hSc y₀
  set E := MaxBranchedCover S y₀
  have hbase : Continuous (SpreadEnd.base : E → Y) := hbc.isSpread.continuous
  rw [continuous_iff_continuousAt]
  intro γ
  rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro N ⟨hmem, hN⟩
  set L := omegaLift hS hSc y₀ γ
  obtain ⟨V, hV, hyV, hVN⟩ := (isSpread_iff.1 hbc.isSpread).2.2 (L 1) N hN hmem
  have hL1 : (L 1).base = γ.1 1 := (omegaLift_spec hS hSc y₀ γ).1 1
  rw [hL1] at hyV
  set V' := connectedComponentIn V (γ.1 1)
  have hV' : IsOpen V' := hV.connectedComponentIn
  have hyV' : γ.1 1 ∈ V' := mem_connectedComponentIn hyV
  set W := connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V') (L 1) with hWdef
  have hW : IsOpen W := (hV'.preimage hbase).connectedComponentIn
  have hWN : W ⊆ N := (connectedComponentIn_mono _ (preimage_mono
    (connectedComponentIn_subset V _))).trans hVN
  obtain ⟨t₀, -, ht₀1, ht₀⟩ := exists_tail_mem (OmegaSpace.toPath γ) (hV'.mem_nhds hyV')
    (c := 1) one_pos
  -- the homotopy `(t, η) ↦ η(t t₀)` and its lift
  have hlt : ∀ t : I, ((t * t₀ : I) : ℝ) < 1 := fun t => by
    rw [Set.Icc.coe_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left t₀.2.1 t.2.2) ht₀1
  have hmemH : ∀ z : I × OmegaSpace S (y₀ : Y), z.2.1 (z.1 * t₀) ∈ Sᶜ := fun z =>
    OmegaSpace.mem_compl y₀.2 z.2 (hlt z.1)
  let H : C(I × OmegaSpace S (y₀ : Y), (Sᶜ : Set Y)) :=
    ⟨fun z => ⟨z.2.1 (z.1 * t₀), hmemH z⟩, by
      refine Continuous.subtype_mk ?_ _
      exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_fst.mul continuous_const))⟩
  have hb0 : (maxBase S y₀) ∈ (SpreadEnd.base : E → Y) ⁻¹' Sᶜ := y₀.2
  let f : C(OmegaSpace S (y₀ : Y), (SpreadEnd.base : E → Y) ⁻¹' Sᶜ) :=
    ContinuousMap.const _ ⟨maxBase S y₀, hb0⟩
  have H_0 : ∀ a, H (0, a) = Sᶜ.restrictPreimage SpreadEnd.base (f a) := fun a => Subtype.ext (by
    show a.1 (0 * t₀) = (maxBase S y₀).base
    rw [zero_mul, a.2.1, maxBase_base])
  set Hl := cov.liftHomotopy H f H_0
  have claim : ∀ η : OmegaSpace S (y₀ : Y), (Hl (1, η) : E) = omegaLift hS hSc y₀ η t₀ := by
    intro η
    let Γ₁ : C(I, E) := ⟨fun t => (Hl (t, η) : E),
      continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
    let Γ₂ : C(I, E) := ⟨fun t => omegaLift hS hSc y₀ η (t * t₀),
      (omegaLift hS hSc y₀ η).continuous.comp (continuous_id.mul continuous_const)⟩
    have := lift_unique cov (γ := fun t => η.1 (t * t₀)) (Γ₁ := Γ₁) (Γ₂ := Γ₂)
      (fun t _ => hmemH (t, η))
      (fun t => congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H f H_0) (t, η)))
      (fun t => (omegaLift_spec hS hSc y₀ η).1 _)
      (by
        show (Hl (0, η) : E) = omegaLift hS hSc y₀ η (0 * t₀)
        rw [cov.liftHomotopy_zero, zero_mul, (omegaLift_spec hS hSc y₀ η).2]; rfl)
    have h1 := congrArg (fun Γ : C(I, E) => Γ 1) this
    simpa [Γ₁, Γ₂] using h1
  set g : OmegaSpace S (y₀ : Y) → E := fun η => (Hl (1, η) : E)
  have hg : Continuous g :=
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_const.prodMk continuous_id))
  have htail : ∀ η : OmegaSpace S (y₀ : Y), (∀ t : I, (t₀ : ℝ) ≤ t → η.1 t ∈ V') →
      (∀ t : I, (t₀ : ℝ) ≤ t → (omegaLift hS hSc y₀ η t).base ∈ V') := fun η h t ht => by
    rw [(omegaLift_spec hS hSc y₀ η).1]; exact h t ht
  have hγW : g γ ∈ W := by
    show (Hl (1, γ) : E) ∈ W
    rw [claim, hWdef, ← (comp_tail (htail γ ht₀)).2]
    exact mem_connectedComponentIn (htail γ ht₀ t₀ le_rfl)
  have hO₂ : IsOpen {η : OmegaSpace S (y₀ : Y) | MapsTo η.1 (Icc t₀ 1) V'} :=
    (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc hV').preimage continuous_subtype_val
  refine Filter.mem_of_superset (inter_mem ((hW.preimage hg).mem_nhds hγW)
    (hO₂.mem_nhds fun t ht => ht₀ t ht.1)) ?_
  rintro η ⟨h1, h2⟩
  have h2' : ∀ t : I, (t₀ : ℝ) ≤ t → η.1 t ∈ V' := fun t ht => h2 ⟨ht, t.2.2⟩
  have hct := comp_tail (htail η h2')
  have hgη : omegaLift hS hSc y₀ η t₀ ∈ W := by
    have := h1; simp only [mem_preimage, g, claim] at this; exact this
  apply hWN
  have hW' : W = connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V')
      (omegaLift hS hSc y₀ η t₀) := by rw [hWdef]; exact connectedComponentIn_eq hgη
  rw [hW']
  exact hct.1 1 t₀.2.2

/-- `ψ : Ω → \widetilde Y^S` is onto (the first item of the proof). -/
theorem surjective_omegaLift_one :
    Surjective fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  haveI := hbc.connectedSpace_source
  set E := MaxBranchedCover S y₀
  have hE : IsPortly ((SpreadEnd.base : E → Y) ⁻¹' Sᶜ) := hbc.isPortly_preimage hS
  intro e
  obtain ⟨γh, hγh⟩ := path_covering hE (a := maxBase S y₀) (b := e) y₀.2
  set η : C(I, Y) := (γh.map hbc.isSpread.continuous).toContinuousMap
  have hη : η ∈ OmegaSpace S (y₀ : Y) := ⟨by
    show (γh 0).base = y₀
    rw [γh.source]; rfl, fun t _ h1 => hγh t h1⟩
  refine ⟨⟨η, hη⟩, ?_⟩
  have := omegaLift_unique hS hSc y₀ ⟨η, hη⟩ (Γ := γh.toContinuousMap) (fun t => rfl) γh.source
  show omegaLift hS hSc y₀ ⟨η, hη⟩ 1 = e
  rw [← this]; exact γh.target

/-- `ψ : Ω → \widetilde Y^S` is open (the third item of the proof, `RamcovGX.tex:1365`; see the
SCOPE for why the paper's subbasic case analysis is replaced). -/
theorem isOpenMap_omegaLift_one :
    IsOpenMap fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  set E := MaxBranchedCover S y₀
  have hbase : Continuous (SpreadEnd.base : E → Y) := hbc.isSpread.continuous
  have hE : IsPortly ((SpreadEnd.base : E → Y) ⁻¹' Sᶜ) := hbc.isPortly_preimage hS
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨γ, hγO, rfl⟩
  obtain ⟨O', hO'n, hO'O⟩ := (mem_nhds_subtype _ γ O).1 (hO.mem_nhds hγO)
  obtain ⟨t₀, ht₀1, V, hV, hγV, hP⟩ := exists_tail_perturb hO'n
  obtain ⟨V₀, hV₀V, hV₀o, hγ1V₀⟩ := mem_nhds_iff.1 hV
  set V₃ := connectedComponentIn V₀ (γ.1 1)
  have hV₃o : IsOpen V₃ := hV₀o.connectedComponentIn
  have hγ1V₃ : γ.1 1 ∈ V₃ := mem_connectedComponentIn hγ1V₀
  have hV₃V : V₃ ⊆ V := (connectedComponentIn_subset _ _).trans hV₀V
  obtain ⟨t₂, -, ht₂1, ht₂⟩ := exists_tail_mem (OmegaSpace.toPath γ) (hV₃o.mem_nhds hγ1V₃)
    (c := 1) one_pos
  set t₁ : I := ⟨max (max (t₀ : ℝ) t₂) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le t₀.2.2 t₂.2.2) (by norm_num)⟩ with ht₁def
  have ht₁1 : (t₁ : ℝ) < 1 := max_lt (max_lt ht₀1 ht₂1) (by norm_num)
  have ht₁0 : (t₀ : ℝ) ≤ t₁ := (le_max_left _ _).trans (le_max_left _ _)
  have ht₁2 : (t₂ : ℝ) ≤ t₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hP' : ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₁ → f t = γ.1 t) →
      (∀ t : I, (t₁ : ℝ) ≤ t → f t ∈ V₃) → f ∈ O' := fun f hf hfV => hP f
    (fun t ht => hf t (ht.trans ht₁0)) fun t ht => by
      rcases le_total (t : ℝ) t₁ with h | h
      · rw [hf t h]; exact hγV t ht
      · exact hV₃V (hfV t h)
  set L := omegaLift hS hSc y₀ γ
  set W := connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V₃) (L 1) with hWdef
  have hWo : IsOpen W := (hV₃o.preimage hbase).connectedComponentIn
  have hL1 : L 1 ∈ W := mem_connectedComponentIn (show (L 1).base ∈ V₃ by
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact hγ1V₃)
  have htail : ∀ t : I, (t₁ : ℝ) ≤ t → (L t).base ∈ V₃ := fun t ht => by
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact ht₂ t (ht₁2.trans ht)
  have hct := comp_tail htail
  have hLW : L t₁ ∈ W := by rw [hWdef, ← hct.2]; exact mem_connectedComponentIn (htail t₁ le_rfl)
  have hLE : L t₁ ∈ (SpreadEnd.base : E → Y) ⁻¹' Sᶜ := by
    show (L t₁).base ∈ Sᶜ
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact OmegaSpace.mem_compl y₀.2 γ ht₁1
  refine Filter.mem_of_superset (hWo.mem_nhds hL1) fun e' he' => ?_
  obtain ⟨ζ, hζW, hζE⟩ := exists_path_of_isPortly_of_isOpen hE hWo
    isPreconnected_connectedComponentIn hLE hLW he'
  set ζY : C(I, Y) := (ζ.map hbase).toContinuousMap
  have hζ0 : ζY 0 = γ.1 t₁ := by
    show (ζ 0).base = γ.1 t₁
    rw [ζ.source, (omegaLift_spec hS hSc y₀ γ).1]
  set η₀ : C(I, Y) := glue γ.1 t₁ ht₁1 ζY hζ0
  have hη₀ : η₀ ∈ OmegaSpace S (y₀ : Y) := by
    refine ⟨by rw [glue_zero]; exact γ.2.1, fun t h0 h1 => ?_⟩
    rcases glue_mem (f := γ.1) (h := ht₁1) (hg := hζ0) t with ⟨_, he⟩ | ⟨r, he, hr⟩
    · rw [he]; exact γ.2.2 t h0 h1
    · rw [he]; exact hζE r (hr h1)
  have hη₀O' : η₀ ∈ O' := hP' η₀ (fun t ht => glue_apply_le ht) fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [glue_apply_le h.ge]; exact ht₂ t (ht₁2.trans ht)
    · rw [glue_apply_gt h]
      exact (connectedComponentIn_subset _ _ (hζW _) : ζ _ ∈ (SpreadEnd.base : E → Y) ⁻¹' V₃)
  refine ⟨⟨η₀, hη₀⟩, hO'O hη₀O', ?_⟩
  have hζ0' : ζ.toContinuousMap 0 = L t₁ := ζ.source
  have hlift := omegaLift_unique hS hSc y₀ ⟨η₀, hη₀⟩ (Γ := glue L t₁ ht₁1 ζ.toContinuousMap hζ0')
    (fun t => glue_map (φ := SpreadEnd.base) (fun t => (omegaLift_spec hS hSc y₀ γ).1 t)
      (fun t => rfl) hζ0 t)
    (by rw [glue_zero]; exact (omegaLift_spec hS hSc y₀ γ).2)
  show omegaLift hS hSc y₀ ⟨η₀, hη₀⟩ 1 = e'
  rw [← hlift, glue_one]; exact ζ.target

include hS hSc in
/-- **`theo:ramified_covering_path`** (`RamcovGX.tex:1322`), with the semilocal simple
connectivity of `Y ∖ S` the proof uses (and without which `\widetilde Y^S` is not defined). The
almost homotopy classes `X` of `Ω = ⋃_x Ω(y₀,x,Y ∖ S)` with the quotient of the compact-open
topology are homeomorphic over `Y` to `\widetilde Y^S`: `\overline φ = p ∘ Ψ`. -/
theorem ramified_covering_path :
    ∃ Ψ : OmegaQuot S y₀ ≃ₜ MaxBranchedCover S y₀, ∀ q, (Ψ q).base = omegaEnd S y₀ q := by
  set ψ : OmegaSpace S (y₀ : Y) → MaxBranchedCover S y₀ := fun γ => omegaLift hS hSc y₀ γ 1
  have hψc : Continuous ψ := continuous_omegaLift_one hS hSc y₀
  have hψo : IsOpenMap ψ := isOpenMap_omegaLift_one hS hSc y₀
  have hψs : Surjective ψ := surjective_omegaLift_one hS hSc y₀
  set ψb : OmegaQuot S y₀ → MaxBranchedCover S y₀ :=
    Quotient.lift ψ fun a b h => (omegaLift_one_eq_iff hS hSc y₀ a b).2 h
  have hinj : Injective ψb := by
    intro q q'
    induction q using Quotient.inductionOn with | h a =>
    induction q' using Quotient.inductionOn with | h b =>
    intro h
    exact Quotient.sound ((omegaLift_one_eq_iff hS hSc y₀ a b).1 h)
  have hsurj : Surjective ψb := fun e => by
    obtain ⟨γ, hγ⟩ := hψs e
    exact ⟨Quotient.mk _ γ, hγ⟩
  have hc : Continuous ψb := hψc.quotient_lift _
  have ho : IsOpenMap ψb := by
    intro O hO
    have : ψb '' O = ψ '' (Quotient.mk (omegaSetoid S y₀) ⁻¹' O) := by
      ext e
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h a =>
        exact ⟨a, hq, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ha, rfl⟩
    rw [this]
    exact hψo _ (hO.preimage continuous_quotient_mk')
  refine ⟨(Equiv.ofBijective ψb ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hc ho, fun q => ?_⟩
  induction q using Quotient.inductionOn with | h a =>
  exact (omegaLift_spec hS hSc y₀ a).1 1

include hS hSc in
/-- `theo:ramified_covering_path`, the branched covering: `\overline φ : X → Y` is a branched
covering, possibly branched over `S`. -/
theorem omegaEnd_isBranchedCovering :
    IsBranchedCovering (omegaEnd S y₀) ∧ IsPossiblyBranchedOver (omegaEnd S y₀) S := by
  obtain ⟨Ψ, hΨ⟩ := ramified_covering_path hS hSc y₀
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  have heq : omegaEnd S y₀ = (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∘ Ψ :=
    funext fun q => (hΨ q).symm
  rw [heq]
  have hord := image_ordY_of_homeomorph (p := (SpreadEnd.base : MaxBranchedCover S y₀ → Y))
    (p' := SpreadEnd.base ∘ Ψ) Ψ.symm (Homeomorph.refl Y) (fun e => by simp)
  have hid : ⇑(Homeomorph.refl Y) = id := rfl
  rw [hid, image_id] at hord
  refine ⟨hbc.comp_homeomorph Ψ, ?_⟩
  unfold IsPossiblyBranchedOver branchingLocus
  rw [← hord]
  exact hpb

end RamifiedMain

/-! ### `def:covering_branched_two_paths`, `prop:general_fiber_path` -/

section FiberPath

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Paths with fixed start `a`, in `Y ∖ S`, with free end in `U` (`RamcovGX.tex:1387`). -/
def FreePath (S : Set Y) (a : Y) (U : Set Y) : Set C(I, Y) :=
  {γ | γ 0 = a ∧ (∀ t, γ t ∈ Sᶜ) ∧ γ 1 ∈ U}

/-- **`def:covering_branched_two_paths`** (`RamcovGX.tex:1385`). Two paths from `a` with free end
in `U` are *`p`-homotopic* if their lifts from the same start point `â` end in the same connected
component of `p⁻¹(U)`. -/
def PHomotopic (p : X → Y) (â : X) (U : Set Y) (γ₁ γ₂ : C(I, Y)) : Prop :=
  ∃ Γ₁ Γ₂ : C(I, X), (∀ t, p (Γ₁ t) = γ₁ t) ∧ (∀ t, p (Γ₂ t) = γ₂ t) ∧ Γ₁ 0 = â ∧ Γ₂ 0 = â ∧
    connectedComponentIn (p ⁻¹' U) (Γ₁ 1) = connectedComponentIn (p ⁻¹' U) (Γ₂ 1)

variable [T2Space X] {p : X → Y} {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p))
  {a : Y} {â : X} (hâ : p â = a)

/-- An element of `FreePath` as a path. -/
def FreePath.toPath {U : Set Y} (γ : FreePath S a U) : Path a (γ.1 1) := ⟨γ.1, γ.2.1, rfl⟩

include cov hâ in
theorem FreePath.exists_lift {U : Set Y} (γ : FreePath S a U) :
    ∃ Γ : C(I, X), (∀ t, p (Γ t) = γ.1 t) ∧ Γ 0 = â :=
  exists_lift_of_mem cov (FreePath.toPath γ) γ.2.2.1 hâ

include cov in
theorem FreePath.lift_unique {U : Set Y} (γ : FreePath S a U) {Γ Γ' : C(I, X)}
    (hΓ : ∀ t, p (Γ t) = γ.1 t) (hΓ' : ∀ t, p (Γ' t) = γ.1 t) (h0 : Γ 0 = Γ' 0) : Γ = Γ' :=
  _root_.GX.lift_unique cov (fun t _ => γ.2.2.1 t) hΓ hΓ' h0

include cov in
theorem pHomotopic_iff {U : Set Y} {γ₁ γ₂ : FreePath S a U} {Γ₁ Γ₂ : C(I, X)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁.1 t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂.1 t) (h₁ : Γ₁ 0 = â)
    (h₂ : Γ₂ 0 = â) :
    PHomotopic p â U γ₁.1 γ₂.1 ↔
      connectedComponentIn (p ⁻¹' U) (Γ₁ 1) = connectedComponentIn (p ⁻¹' U) (Γ₂ 1) := by
  constructor
  · rintro ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, h₁', h₂', h⟩
    rw [FreePath.lift_unique cov γ₁ hΓ₁ hΔ₁ (h₁.trans h₁'.symm),
      FreePath.lift_unique cov γ₂ hΓ₂ hΔ₂ (h₂.trans h₂'.symm)]
    exact h
  · exact fun h => ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, h₁, h₂, h⟩

include cov hâ in
theorem pHomotopic_equivalence (U : Set Y) :
    Equivalence fun γ₁ γ₂ : FreePath S a U => PHomotopic p â U γ₁.1 γ₂.1 where
  refl γ := by
    obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
    exact (pHomotopic_iff cov hΓ hΓ h0 h0).2 rfl
  symm := fun ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ => ⟨Γ₂, Γ₁, h₂, h₁, h₂0, h₁0, h.symm⟩
  trans := fun {γ₁ γ₂ γ₃} ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ ⟨Γ₂', Γ₃, h₂', h₃, h₂0', h₃0, h'⟩ => by
    refine ⟨Γ₁, Γ₃, h₁, h₃, h₁0, h₃0, h.trans ?_⟩
    rw [FreePath.lift_unique cov γ₂ h₂ h₂' (h₂0.trans h₂0'.symm)]
    exact h'

/-- The `p`-homotopy setoid. -/
def pSetoid (U : Set Y) : Setoid (FreePath S a U) :=
  ⟨fun γ₁ γ₂ => PHomotopic p â U γ₁.1 γ₂.1, pHomotopic_equivalence cov hâ U⟩

/-- **`π₁(a,p,U)`** (`RamcovGX.tex:1392`): paths with fixed start at `a` and free end in `U` up to
`p`-homotopy (a discrete space). -/
def PiOneP (U : Set Y) : Type _ := Quotient (pSetoid cov hâ U)

instance (U : Set Y) : TopologicalSpace (PiOneP cov hâ U) := ⊥

instance (U : Set Y) : DiscreteTopology (PiOneP cov hâ U) := ⟨rfl⟩

/-- The natural map `π₁(a,p,U) → π₁(a,p,V)` for `U ⊆ V`. -/
def piOnePMap {U V : Set Y} (hUV : U ⊆ V) : PiOneP cov hâ U → PiOneP cov hâ V :=
  Quotient.map (fun γ => ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩) fun γ₁ γ₂ ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ =>
    ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, by
      have hm : Γ₂ 1 ∈ connectedComponentIn (p ⁻¹' U) (Γ₁ 1) := by
        rw [h]; exact mem_connectedComponentIn (show p (Γ₂ 1) ∈ U by rw [h₂]; exact γ₂.2.2.2)
      exact connectedComponentIn_eq (connectedComponentIn_mono _ (preimage_mono hUV) hm)⟩

/-- The component of `p⁻¹(U)` in which the lifts of a class end. -/
def compOfClass (U : Set Y) : PiOneP cov hâ U → Set X :=
  Quotient.lift (fun γ : FreePath S a U => connectedComponentIn (p ⁻¹' U)
      ((FreePath.exists_lift cov hâ γ).choose 1)) fun γ₁ γ₂ h =>
    (pHomotopic_iff cov (FreePath.exists_lift cov hâ γ₁).choose_spec.1
      (FreePath.exists_lift cov hâ γ₂).choose_spec.1 (FreePath.exists_lift cov hâ γ₁).choose_spec.2
      (FreePath.exists_lift cov hâ γ₂).choose_spec.2).1 h

theorem compOfClass_mk {U : Set Y} (γ : FreePath S a U) {Γ : C(I, X)} (hΓ : ∀ t, p (Γ t) = γ.1 t)
    (h0 : Γ 0 = â) : compOfClass cov hâ U (Quotient.mk _ γ) = connectedComponentIn (p ⁻¹' U) (Γ 1) := by
  show connectedComponentIn (p ⁻¹' U) ((FreePath.exists_lift cov hâ γ).choose 1) = _
  rw [FreePath.lift_unique cov γ (FreePath.exists_lift cov hâ γ).choose_spec.1 hΓ
    ((FreePath.exists_lift cov hâ γ).choose_spec.2.trans h0.symm)]

theorem compOfClass_injective (U : Set Y) : Injective (compOfClass cov hâ U) := by
  intro c c'
  induction c using Quotient.inductionOn with | h γ =>
  induction c' using Quotient.inductionOn with | h γ' =>
  intro h
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  obtain ⟨Γ', hΓ', h0'⟩ := FreePath.exists_lift cov hâ γ'
  rw [compOfClass_mk cov hâ γ hΓ h0, compOfClass_mk cov hâ γ' hΓ' h0'] at h
  exact Quotient.sound ((pHomotopic_iff cov hΓ hΓ' h0 h0').2 h)

theorem compOfClass_isCompOf {U : Set Y} (c : PiOneP cov hâ U) :
    IsCompOf p U (compOfClass cov hâ U c) := by
  induction c using Quotient.inductionOn with | h γ =>
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  rw [compOfClass_mk cov hâ γ hΓ h0]
  exact isCompOf_connectedComponentIn (by rw [hΓ]; exact γ.2.2.2)

theorem compOfClass_piOnePMap {U V : Set Y} (hUV : U ⊆ V) (c : PiOneP cov hâ U) :
    compOfClass cov hâ U c ⊆ compOfClass cov hâ V (piOnePMap cov hâ hUV c) := by
  induction c using Quotient.inductionOn with | h γ =>
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  rw [compOfClass_mk cov hâ γ hΓ h0]
  show _ ⊆ compOfClass cov hâ V (Quotient.mk _ ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩)
  rw [compOfClass_mk cov hâ ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩ hΓ h0]
  exact connectedComponentIn_mono _ (preimage_mono hUV)

include hâ in
theorem compOfClass_surjective [LocPathConnectedSpace X] (hp : IsBranchedCovering p)
    (hS : IsSkeletal S) (haS : a ∈ Sᶜ) {U : Set Y} (hU : IsOpen U) {C : Set X}
    (hC : IsCompOf p U C) : ∃ c, compOfClass cov hâ U c = C := by
  haveI := hp.connectedSpace_source
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  have hEpc : IsPathConnected (p ⁻¹' Sᶜ) :=
    hE.isOpen.isConnected_iff_isPathConnected.1 hE.isConnected
  obtain ⟨z₀, hz₀, rfl⟩ := hC
  have hCo : IsOpen (connectedComponentIn (p ⁻¹' U) z₀) :=
    (hU.preimage hp.isSpread.continuous).connectedComponentIn
  obtain ⟨z, hzC, hzE⟩ := hE.dense.inter_open_nonempty _ hCo
    ⟨z₀, mem_connectedComponentIn (show z₀ ∈ p ⁻¹' U from hz₀)⟩
  have hâE : â ∈ p ⁻¹' Sᶜ := by show p â ∈ Sᶜ; rw [hâ]; exact haS
  obtain ⟨ζ, hζ⟩ := hEpc.joinedIn â hâE z hzE
  have hγ : (ζ.map hp.isSpread.continuous).toContinuousMap ∈ FreePath S a U :=
    ⟨by show p (ζ 0) = a; rw [ζ.source, hâ], fun t => hζ t, by
      show p (ζ 1) ∈ U; rw [ζ.target]
      exact (connectedComponentIn_subset (p ⁻¹' U) _ hzC : z ∈ p ⁻¹' U)⟩
  refine ⟨Quotient.mk _ ⟨_, hγ⟩, ?_⟩
  rw [compOfClass_mk cov hâ ⟨_, hγ⟩ (Γ := ζ.toContinuousMap) (fun t => rfl) ζ.source]
  show connectedComponentIn (p ⁻¹' U) (ζ 1) = _
  rw [ζ.target]; exact (connectedComponentIn_eq hzC).symm

/-- `def:covering_branched_two_paths` is set in a covering possibly branched over `S`: the part
over `Y ∖ S` is a covering, so lifts exist and are unique. -/
theorem isCoveringMap_restrict_compl {p : X → Y} (hp : IsBranchedCovering p) {S : Set Y}
    (hS : IsSkeletal S) (hpS : IsPossiblyBranchedOver p S) :
    IsCoveringMap (Sᶜ.restrictPreimage p) :=
  (hp.restrict_isCoveringMap (isSkeletal_iff.1 hS) fun y hy => by
    by_contra h; exact hy (hpS h)).1

/-- **`prop:general_fiber_path`** (`RamcovGX.tex:1390`). For a covering `p : X → Y` possibly
branched over a skeletal `S`, `a ∈ Y ∖ S`, `â` over `a`, every `b ∈ Y` and every basis `𝓤` of
connected open neighbourhoods of `b`, the natural map `p⁻¹(b) → ∏_{U ∈ 𝓤} π₁(a,p,U)`
(`x ↦` the classes whose lifts end in the component of `x`) is an embedding (each `π₁(a,p,U)`
discrete) onto the projective limit `lim_{U ∈ 𝓤} π₁(a,p,U)` of the natural maps. -/
theorem general_fiber_path [LocPathConnectedSpace X] [T1Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) (hS : IsSkeletal S) (haS : a ∈ Sᶜ) {b : Y} (𝓤 : Set (Set Y))
    (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    ∃ Φ : p ⁻¹' {b} → ∀ U : 𝓤, PiOneP cov hâ U,
      (∀ x (U : 𝓤), compOfClass cov hâ U (Φ x U) = connectedComponentIn (p ⁻¹' U) x) ∧
      IsEmbedding Φ ∧
      range Φ = {f | ∀ U V : 𝓤, ∀ h : (U : Set Y) ⊆ V, piOnePMap cov hâ h (f U) = f V} := by
  have hmem : ∀ (x : p ⁻¹' {b}) (U : 𝓤), IsCompOf p U (connectedComponentIn (p ⁻¹' U) x) :=
    fun x U => isCompOf_connectedComponentIn (by
      rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem)
  have hex : ∀ (x : p ⁻¹' {b}) (U : 𝓤), ∃ c, compOfClass cov hâ U c =
      connectedComponentIn (p ⁻¹' U) x := fun x U =>
    compOfClass_surjective cov hâ hp hS haS (h𝓤 U U.2).isOpen (hmem x U)
  choose Φ hΦ using hex
  have hinj : ∀ U : 𝓤, Injective (compOfClass cov hâ U) := fun U => compOfClass_injective cov hâ U
  -- continuity
  have hfc := continuous_fiberMap hp.isSpread h𝓤
  have hΦc : Continuous Φ := by
    refine continuous_pi fun U => continuous_discrete_rng.2 fun c => ?_
    have : (fun x => Φ x U) ⁻¹' {c} =
        (fun x => (fiberMap p 𝓤 h𝓤 x).toFun U) ⁻¹' {compOfClass cov hâ U c} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · rintro rfl; exact (hΦ x U).symm
      · intro h
        apply hinj U
        rw [hΦ x U]; exact h
    rw [this]
    exact (FiberThread.isOpen_cylinder U _).preimage hfc
  set G : (∀ U : 𝓤, PiOneP cov hâ U) → (𝓤 → DiscreteSets X) :=
    fun f U => compOfClass cov hâ U (f U)
  have hGc : Continuous G :=
    continuous_pi fun U => continuous_of_discreteTopology.comp (continuous_apply U)
  have hcomp : G ∘ Φ = FiberThread.coords ∘ fiberMap p 𝓤 h𝓤 := by
    funext x U
    exact hΦ x U
  have hind : IsInducing (FiberThread.coords ∘ fiberMap p 𝓤 h𝓤) :=
    (IsInducing.induced _).comp (isInducing_fiberMap hp.isSpread h𝓤 hbasis)
  have hΦi : IsInducing Φ := IsInducing.of_comp hΦc hGc (hcomp ▸ hind)
  refine ⟨Φ, hΦ, ⟨hΦi, hΦi.injective⟩, ?_⟩
  ext f
  constructor
  · rintro ⟨x, rfl⟩ U V h
    apply hinj V
    rw [hΦ x V]
    refine (compOfClass_isCompOf cov hâ _).eq_of_meets (hmem x V) ⟨x, ?_, ?_⟩
    · apply compOfClass_piOnePMap cov hâ h
      rw [hΦ x U]
      exact mem_connectedComponentIn (show p x ∈ (U : Set Y) by
        rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem)
    · exact mem_connectedComponentIn (show p x ∈ (V : Set Y) by
        rw [show p x = b from x.2]; exact (h𝓤 V V.2).mem)
  · intro hf
    let s : FiberThread p 𝓤 :=
      { toFun := fun U => compOfClass cov hâ U (f U)
        isCompOf := fun U => compOfClass_isCompOf cov hâ _
        mono := fun U V h => by
          have := compOfClass_piOnePMap cov hâ h (f U)
          rwa [hf U V h] at this }
    obtain ⟨x, hx⟩ := isCompleteSpread_iff_forall_surjective_fiberMap.1 hp.isComplete b 𝓤 h𝓤
      hbasis s
    refine ⟨x, funext fun U => hinj U ?_⟩
    rw [hΦ x U]
    exact congrArg (fun t : FiberThread p 𝓤 => t.toFun U) hx

end FiberPath

/-! ### `prop:general_fiber_path_universal` -/

section FreeHom

variable {Y : Type*} [TopologicalSpace Y]

/-- Homotopy of paths of `Y ∖ S` with fixed start `a` and free end in `U` (the "up to homotopy" of
`RamcovGX.tex:1402`): a homotopy `H` in `Y ∖ S`, `H(s,0) = a`, `H(s,1) ∈ U`. -/
def FreeHomotopic (S : Set Y) (a : Y) (U : Set Y) (γ₁ γ₂ : C(I, Y)) : Prop :=
  ∃ H : C(I × I, Y), (∀ t, H (0, t) = γ₁ t) ∧ (∀ t, H (1, t) = γ₂ t) ∧ (∀ s, H (s, 0) = a) ∧
    (∀ s, H (s, 1) ∈ U) ∧ ∀ z, H z ∈ Sᶜ

variable {S : Set Y} {a : Y} {U : Set Y}

theorem freeHomotopic_refl {γ : C(I, Y)} (hγ : γ ∈ FreePath S a U) : FreeHomotopic S a U γ γ :=
  ⟨⟨fun z => γ z.2, by fun_prop⟩, fun _ => rfl, fun _ => rfl, fun _ => hγ.1, fun _ => hγ.2.2,
    fun z => hγ.2.1 z.2⟩

theorem FreeHomotopic.symm {γ₁ γ₂ : C(I, Y)} (h : FreeHomotopic S a U γ₁ γ₂) :
    FreeHomotopic S a U γ₂ γ₁ := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  refine ⟨⟨fun z => H (σ z.1, z.2), by fun_prop⟩, fun t => ?_, fun t => ?_, fun s => ha _,
    fun s => hU _, fun z => hS _⟩
  · show H (σ 0, t) = _; rw [unitInterval.symm_zero, h1]
  · show H (σ 1, t) = _; rw [unitInterval.symm_one, h0]

theorem FreeHomotopic.trans {γ₁ γ₂ γ₃ : C(I, Y)} (h : FreeHomotopic S a U γ₁ γ₂)
    (h' : FreeHomotopic S a U γ₂ γ₃) : FreeHomotopic S a U γ₁ γ₃ := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  obtain ⟨H', h0', h1', ha', hU', hS'⟩ := h'
  set pr : ℝ → I := Set.projIcc 0 1 zero_le_one
  let K : I × I → Y := fun z =>
    if (z.1 : ℝ) ≤ 1 / 2 then H (pr (2 * z.1), z.2) else H' (pr (2 * z.1 - 1), z.2)
  have hK : Continuous K := by
    refine Continuous.if_le (H.continuous.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      continuous_snd)) (H'.continuous.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      continuous_snd)) (by fun_prop) continuous_const fun z hz => ?_
    rw [hz]
    have e1 : pr (2 * (1 / 2 : ℝ)) = 1 := Subtype.ext (by simp [pr])
    have e2 : pr (2 * (1 / 2 : ℝ) - 1) = 0 := Subtype.ext (by simp [pr])
    rw [e1, e2, h1, h0']
  have hmem : ∀ z, K z = H (pr (2 * z.1), z.2) ∨ K z = H' (pr (2 * z.1 - 1), z.2) := fun z => by
    simp only [K]; split_ifs <;> simp
  refine ⟨⟨K, hK⟩, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_, fun z => ?_⟩
  · show K (0, t) = _
    simp only [K, Icc.coe_zero, mul_zero, if_pos (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    rw [show pr 0 = 0 from Subtype.ext (by simp [pr]), h0]
  · show K (1, t) = _
    simp only [K, Icc.coe_one, if_neg (show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num)]
    rw [show pr (2 * 1 - 1) = 1 from Subtype.ext (by norm_num [pr]), h1']
  · show K (s, 0) = a
    rcases hmem (s, 0) with h | h <;> rw [h]
    · exact ha _
    · exact ha' _
  · show K (s, 1) ∈ U
    rcases hmem (s, 1) with h | h <;> rw [h]
    · exact hU _
    · exact hU' _
  · show K z ∈ Sᶜ
    rcases hmem z with h | h <;> rw [h]
    · exact hS _
    · exact hS' _

theorem freeHomotopic_of_homotopicIn {c : Y} (hc : c ∈ U) {P Q : Path a c}
    (h : HomotopicIn Sᶜ P Q) : FreeHomotopic S a U P.toContinuousMap Q.toContinuousMap := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.toContinuousMap, F.apply_zero, F.apply_one, F.source, fun s => (F.target s).symm ▸ hc,
    hF⟩

/-- Moving the end back along a path of `U ∖ S`. -/
theorem freeHomotopic_trans_shrink {c d : Y} (P : Path a c) (hP : ∀ t, P t ∈ Sᶜ) (ω : Path c d)
    (hω : ∀ t, ω t ∈ U ∩ Sᶜ) :
    FreeHomotopic S a U (P.trans ω).toContinuousMap (P.trans (Path.refl c)).toContinuousMap := by
  set pr : ℝ → I := Set.projIcc 0 1 zero_le_one
  let K : I × I → Y := fun z =>
    if (z.2 : ℝ) ≤ 1 / 2 then P.extend (2 * z.2) else ω.extend ((1 - z.1) * (2 * z.2 - 1))
  have hK : Continuous K := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
      fun z hz => ?_
    rw [hz]; simp
  have hK1 : ∀ z : I × I, (1 / 2 : ℝ) < z.2 → K z ∈ U ∩ Sᶜ := fun z hz => by
    simp only [K, if_neg (not_le.2 hz)]
    rw [ω.extend_apply ⟨by nlinarith [z.1.2.2, z.2.2.2], by nlinarith [z.1.2.1, z.2.2.2]⟩]
    exact hω _
  refine ⟨⟨K, hK⟩, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_, fun z => ?_⟩
  · show K (0, t) = (P.trans ω) t
    simp only [K, Icc.coe_zero, sub_zero, one_mul, Path.trans_apply]
    split_ifs with h
    · rw [P.extend_apply]
    · rw [ω.extend_apply]
  · show K (1, t) = (P.trans (Path.refl c)) t
    simp only [K, Icc.coe_one, sub_self, zero_mul, Path.trans_apply]
    split_ifs with h
    · rw [P.extend_apply]
    · rw [ω.extend_zero]; rfl
  · show K (s, 0) = a
    simp [K]
  · exact (hK1 (s, 1) (by simp; norm_num)).1
  · show K z ∈ Sᶜ
    rcases le_or_gt (z.2 : ℝ) (1 / 2) with h | h
    · simp only [K, if_pos h]
      rw [P.extend_apply ⟨by linarith [z.2.2.1], by linarith⟩]; exact hP _
    · exact (hK1 z h).2

theorem freeHomotopic_equivalence :
    Equivalence fun γ₁ γ₂ : FreePath S a U => FreeHomotopic S a U γ₁.1 γ₂.1 :=
  ⟨fun γ => freeHomotopic_refl γ.2, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **`π₁(a,U)`** (`RamcovGX.tex:1402`): paths of `Y ∖ S` with fixed start at `a` and free end in
`U`, up to homotopy (with free end in `U`); a discrete space. -/
def PiOneU (S : Set Y) (a : Y) (U : Set Y) : Type _ :=
  Quotient (⟨fun γ₁ γ₂ : FreePath S a U => FreeHomotopic S a U γ₁.1 γ₂.1,
    freeHomotopic_equivalence⟩ : Setoid (FreePath S a U))

instance : TopologicalSpace (PiOneU S a U) := ⊥

instance : DiscreteTopology (PiOneU S a U) := ⟨rfl⟩

/-- The natural map `π₁(a,U) → π₁(a,V)` for `U ⊆ V`. -/
def piOneUMap {V : Set Y} (hUV : U ⊆ V) : PiOneU S a U → PiOneU S a V :=
  Quotient.map (fun γ => ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩)
    fun _ _ ⟨H, h0, h1, ha, hU, hS⟩ => ⟨H, h0, h1, ha, fun s => hUV (hU s), hS⟩

end FreeHom

section FiberUniv

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {p : X → Y}
  {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p)) {a : Y} {â : X} (hâ : p â = a)

include cov hâ in
/-- A homotopy with free end in `U` lifts: free-end homotopic paths are `p`-homotopic (for any
covering over `Y ∖ S`). -/
theorem pHomotopic_of_freeHomotopic {U : Set Y} {γ₁ γ₂ : FreePath S a U}
    (h : FreeHomotopic S a U γ₁.1 γ₂.1) : PHomotopic p â U γ₁.1 γ₂.1 := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  let H' : C(I × I, (Sᶜ : Set Y)) := ⟨fun z => ⟨H (z.2, z.1), hS _⟩, by
    refine Continuous.subtype_mk ?_ _
    exact H.continuous.comp continuous_swap⟩
  have hâS : â ∈ p ⁻¹' Sᶜ := by show p â ∈ Sᶜ; rw [hâ, ← ha 0]; exact hS _
  let f : C(I, p ⁻¹' Sᶜ) := ContinuousMap.const _ ⟨â, hâS⟩
  have H_0 : ∀ s, H' (0, s) = Sᶜ.restrictPreimage p (f s) := fun s => Subtype.ext (by
    show H (s, 0) = p â
    rw [ha, hâ])
  set Hl := cov.liftHomotopy H' f H_0
  have hlift : ∀ z : I × I, p (Hl z) = H (z.2, z.1) := fun z =>
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H' f H_0) z)
  let Γ₁ : C(I, X) := ⟨fun t => (Hl (t, 0) : X),
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
  let Γ₂ : C(I, X) := ⟨fun t => (Hl (t, 1) : X),
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
  refine ⟨Γ₁, Γ₂, fun t => by show p (Hl (t, 0)) = _; rw [hlift, h0],
    fun t => by show p (Hl (t, 1)) = _; rw [hlift, h1],
    by show (Hl (0, 0) : X) = â; rw [cov.liftHomotopy_zero]; rfl,
    by show (Hl (0, 1) : X) = â; rw [cov.liftHomotopy_zero]; rfl, ?_⟩
  have hr : range (fun s : I => (Hl (1, s) : X)) ⊆ connectedComponentIn (p ⁻¹' U) (Γ₁ 1) :=
    (isPreconnected_range (continuous_subtype_val.comp (Hl.continuous.comp
      (continuous_const.prodMk continuous_id)))).subset_connectedComponentIn
      ⟨0, rfl⟩ (by rintro _ ⟨s, rfl⟩; show p (Hl (1, s)) ∈ U; rw [hlift]; exact hU s)
  exact connectedComponentIn_eq (hr ⟨1, rfl⟩)

include hâ in
/-- Conversely, over a simply connected part over `Y ∖ S`, `p`-homotopic paths are homotopic
with free end in `U`. -/
theorem freeHomotopic_of_pHomotopic [LocPathConnectedSpace X] (hp : IsBranchedCovering p)
    (hS : IsSkeletal S) [SimplyConnectedSpace (p ⁻¹' Sᶜ)] {U : Set Y} (hU : IsOpen U)
    {γ₁ γ₂ : FreePath S a U} (h : PHomotopic p â U γ₁.1 γ₂.1) :
    FreeHomotopic S a U γ₁.1 γ₂.1 := by
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, h₁0, h₂0, hc⟩ := h
  have hpc : Continuous p := hp.isSpread.continuous
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  set C := connectedComponentIn (p ⁻¹' U) (Γ₁ 1)
  have hCo : IsOpen C := (hU.preimage hpc).connectedComponentIn
  have hΓ₁U : Γ₁ 1 ∈ p ⁻¹' U := by show p (Γ₁ 1) ∈ U; rw [hΓ₁]; exact γ₁.2.2.2
  have hΓ₂U : Γ₂ 1 ∈ p ⁻¹' U := by show p (Γ₂ 1) ∈ U; rw [hΓ₂]; exact γ₂.2.2.2
  have h1C : Γ₁ 1 ∈ C := mem_connectedComponentIn hΓ₁U
  have h2C : Γ₂ 1 ∈ C := by rw [hc]; exact mem_connectedComponentIn hΓ₂U
  have hpath : IsPathConnected (C ∩ p ⁻¹' Sᶜ) :=
    (hCo.inter hE.isOpen).isConnected_iff_isPathConnected.1
      (hE.isConnected_inter hCo ⟨⟨_, h1C⟩, isPreconnected_connectedComponentIn⟩)
  have hE₁ : Γ₁ 1 ∈ p ⁻¹' Sᶜ := by show p (Γ₁ 1) ∈ Sᶜ; rw [hΓ₁]; exact γ₁.2.2.1 1
  have hE₂ : Γ₂ 1 ∈ p ⁻¹' Sᶜ := by show p (Γ₂ 1) ∈ Sᶜ; rw [hΓ₂]; exact γ₂.2.2.1 1
  obtain ⟨ωt, hωt⟩ := hpath.joinedIn _ ⟨h2C, hE₂⟩ _ ⟨h1C, hE₁⟩
  set P₁ : Path â (Γ₁ 1) := ⟨Γ₁, h₁0, rfl⟩
  set P₂ : Path â (Γ₂ 1) := ⟨Γ₂, h₂0, rfl⟩
  have hP₁ : ∀ t, P₁ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Γ₁ t) ∈ Sᶜ; rw [hΓ₁]; exact γ₁.2.2.1 t
  have hP₂ : ∀ t, P₂ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Γ₂ t) ∈ Sᶜ; rw [hΓ₂]; exact γ₂.2.2.1 t
  have hhom : HomotopicIn (p ⁻¹' Sᶜ) P₁ (P₂.trans ωt) := homotopicIn_iff.2
    ⟨hP₁, path_trans_mem hP₂ fun t => (hωt t).2, SimplyConnectedSpace.paths_homotopic _ _⟩
  have hmap := (hhom.map hpc fun z hz => hz).cast hâ.symm rfl
  set Q : Path a (p (Γ₂ 1)) := (P₂.map hpc).cast hâ.symm rfl
  set ω : Path (p (Γ₂ 1)) (p (Γ₁ 1)) := ωt.map hpc
  have hQ : ∀ t, Q t ∈ Sᶜ := fun t => hP₂ t
  have hω : ∀ t, ω t ∈ U ∩ Sᶜ := fun t =>
    ⟨(connectedComponentIn_subset (p ⁻¹' U) _ (hωt t).1 : ωt t ∈ p ⁻¹' U), (hωt t).2⟩
  have e₁ : ((P₁.map hpc).cast hâ.symm rfl).toContinuousMap = γ₁.1 := ContinuousMap.ext hΓ₁
  have e₂ : (((P₂.trans ωt).map hpc).cast hâ.symm rfl) = Q.trans ω := by
    ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply, Q, ω]
    split_ifs <;> rfl
  have eQ : Q.toContinuousMap = γ₂.1 := ContinuousMap.ext hΓ₂
  have step1 := freeHomotopic_of_homotopicIn (S := S) hΓ₁U hmap
  rw [e₁, e₂] at step1
  have step2 := freeHomotopic_trans_shrink Q hQ ω hω
  have step3 : FreeHomotopic S a U (Q.trans (Path.refl _)).toContinuousMap Q.toContinuousMap := by
    refine freeHomotopic_of_homotopicIn (show p (Γ₂ 1) ∈ U from hΓ₂U) ?_
    have hr : ∀ t, (Path.refl (p (Γ₂ 1))) t ∈ Sᶜ := fun _ => hQ 1
    refine homotopicIn_iff.2 ⟨path_trans_mem hQ hr, hQ, ?_⟩
    rw [pathToSub_trans _ _ hQ hr]
    have : pathToSub (Path.refl (p (Γ₂ 1))) hr = Path.refl _ := by ext; rfl
    rw [this]
    exact Path.Homotopic.trans_refl _
  rw [eQ] at step3
  exact step1.trans (step2.trans step3)

end FiberUniv

section FiberUniv2

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- **`prop:general_fiber_path_universal`** (`RamcovGX.tex:1399`). For `\widetilde Y^S → Y` (`S`
skeletal, `Y ∖ S` semilocally simply connected), `a ∈ Y ∖ S`, `â` over `a`, every `b ∈ Y` and every
basis `𝓤` of connected open neighbourhoods of `b`, the natural map
`p⁻¹(b) → ∏_{U ∈ 𝓤} π₁(a,U)` (a class goes to `x` when its lift from `â` ends in the component of
`x` in `p⁻¹(U)`) is an embedding (`π₁(a,U)` discrete) onto `lim_{U ∈ 𝓤} π₁(a,U)`. -/
theorem general_fiber_path_universal (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {a : Y} (haS : a ∈ Sᶜ)
    {â : MaxBranchedCover S y₀} (hâ : â.base = a) {b : Y} (𝓤 : Set (Set Y))
    (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    ∃ Φ : (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {b} → ∀ U : 𝓤, PiOneU S a U,
      (∀ (x : (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {b}) (U : 𝓤) (γ : FreePath S a U)
        (Γ : C(I, MaxBranchedCover S y₀)), (∀ t, (Γ t).base = γ.1 t) → Γ 0 = â →
          Γ 1 ∈ connectedComponentIn ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' U)
            (x : MaxBranchedCover S y₀) →
          Φ x U = Quotient.mk _ γ) ∧
      IsEmbedding Φ ∧
      range Φ = {f | ∀ U V : 𝓤, ∀ h : (U : Set Y) ⊆ V, piOneUMap h (f U) = f V} := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, hsc⟩ := maxBranched_lifting hS hSc y₀
  haveI := hsc
  obtain ⟨Φ', hΦ', hemb, hrange⟩ := general_fiber_path cov hâ hbc hS haS 𝓤 h𝓤 hbasis
  have hiff : ∀ (U : 𝓤) (γ₁ γ₂ : FreePath S a U),
      PHomotopic SpreadEnd.base â U γ₁.1 γ₂.1 ↔ FreeHomotopic S a U γ₁.1 γ₂.1 := fun U γ₁ γ₂ =>
    ⟨freeHomotopic_of_pHomotopic hâ hbc hS (h𝓤 U U.2).isOpen,
      pHomotopic_of_freeHomotopic cov hâ⟩
  let e : ∀ U : 𝓤, PiOneP cov hâ U ≃ PiOneU S a U := fun U =>
    Quotient.congr (Equiv.refl _) (hiff U)
  let eh : ∀ U : 𝓤, PiOneP cov hâ U ≃ₜ PiOneU S a U := fun U =>
    { toEquiv := e U
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  set Θ := Homeomorph.piCongrRight eh
  have hΘ : ∀ f U, Θ f U = e U (f U) := fun _ _ => rfl
  have hcomm : ∀ (U V : 𝓤) (h : (U : Set Y) ⊆ V) (c : PiOneP cov hâ U),
      piOneUMap h (e U c) = e V (piOnePMap cov hâ h c) := by
    intro U V h c
    induction c using Quotient.inductionOn with | h γ => rfl
  refine ⟨Θ ∘ Φ', fun x U γ Γ hΓ h0 hx => ?_, Θ.isEmbedding.comp hemb, ?_⟩
  · show e U (Φ' x U) = _
    have : Φ' x U = Quotient.mk (pSetoid cov hâ U) γ := by
      apply compOfClass_injective cov hâ U
      rw [hΦ' x U, compOfClass_mk cov hâ γ hΓ h0, connectedComponentIn_eq hx]
    rw [this]; rfl
  · ext f
    constructor
    · rintro ⟨x, rfl⟩ U V h
      have hx : Φ' x ∈ range Φ' := ⟨x, rfl⟩
      rw [hrange] at hx
      simp only [comp_apply, hΘ, hcomm, hx U V h]
    · intro hf
      have hf' : Θ.symm f ∈ range Φ' := by
        rw [hrange]
        intro U V h
        apply (e V).injective
        have h1 := hf U V h
        have h2 : f = Θ (Θ.symm f) := (Θ.apply_symm_apply f).symm
        rw [h2] at h1
        simp only [hΘ] at h1
        rw [← hcomm, h1]
      obtain ⟨x, hx⟩ := hf'
      exact ⟨x, by simp only [comp_apply, hx, Θ.apply_symm_apply]⟩

end FiberUniv2

/-! ### Standard neighbourhoods (the reading of `RamcovGX.tex:1311`) -/

section Standard

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- A *standard neighbourhood* of `e` for a spread `p` (undefined in the paper,
`RamcovGX.tex:1311`; the reading taken): the connected component containing `e` of `p⁻¹(V)`,
`V` an open connected neighbourhood of `p(e)`. -/
def IsStandardNbhd (p : E → Y) (e : E) (W : Set E) : Prop :=
  ∃ V, IsCNbhd (p e) V ∧ W = connectedComponentIn (p ⁻¹' V) e

/-- For a spread over a locally connected base, standard neighbourhoods are open and form a basis
of neighbourhoods. -/
theorem IsSpread.hasBasis_standardNbhd [LocallyConnectedSpace Y] {p : E → Y} (hp : IsSpread p)
    (e : E) : (𝓝 e).HasBasis (IsStandardNbhd p e) id := by
  haveI := hp.locallyConnectedSpace
  have hopen : ∀ W, IsStandardNbhd p e W → IsOpen W := by
    rintro W ⟨V, hV, rfl⟩
    exact (hV.isOpen.preimage hp.continuous).connectedComponentIn
  have hmem : ∀ W, IsStandardNbhd p e W → e ∈ W := by
    rintro W ⟨V, hV, rfl⟩
    exact mem_connectedComponentIn (show p e ∈ V from hV.mem)
  refine ⟨fun N => ⟨fun hN => ?_, fun ⟨W, hW, hWN⟩ => mem_of_superset
    ((hopen W hW).mem_nhds (hmem W hW)) hWN⟩⟩
  obtain ⟨O, hON, hO, heO⟩ := mem_nhds_iff.1 hN
  obtain ⟨V, hV, hpV, hVO⟩ := (isSpread_iff.1 hp).2.2 e O hO heO
  refine ⟨connectedComponentIn (p ⁻¹' connectedComponentIn V (p e)) e,
    ⟨connectedComponentIn V (p e), ⟨hV.connectedComponentIn, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn hpV⟩, rfl⟩, ?_⟩
  exact ((connectedComponentIn_mono _ (preimage_mono (connectedComponentIn_subset _ _))).trans
    hVO).trans hON

end Standard

/-! ### `ex:consider_carthesian_coordinates_usual` -/

section Trivial

variable {U : Set X} {x : X}

/-- `γ ∈ Ω(x,x,U)` is *homotopically trivial* (the reading of `RamcovGX.tex:1218–1220`): a
homotopy with fixed ends to the constant loop through loops of `Ω(x,x,U)`, the constant loop
being reached only at the end. -/
def IsHomTrivial (U : Set X) {x : X} (γ : Path x x) : Prop :=
  ∃ F : Path.Homotopy γ (Path.refl x), ∀ s t : I, (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    F (s, t) ∈ U

/-- "homotopically trivial hence almost trivial" (`RamcovGX.tex:1219`). -/
theorem IsHomTrivial.almostTrivial {γ : Path x x} (hγ : MemOmega U γ) (h : IsHomTrivial U γ) :
    AlmostTrivial U γ := by
  obtain ⟨F, hF⟩ := h
  refine ⟨hγ, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
  have hP : ∀ t ∈ (univ : Set I), ∀ᶠ z : I × I in 𝓝 (1, t), F z ∈ V' := fun t _ =>
    F.continuous.continuousAt.preimage_mem_nhds (hV'.mem_nhds (by
      rw [F.apply_one]; exact hxV'))
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff.1
    (isCompact_univ.eventually_forall_of_forall_eventually (P := fun s t => F (s, t) ∈ V') hP)
  set s₀ : I := ⟨max 0 (1 - ε / 2), le_max_left _ _, max_le zero_le_one (by linarith)⟩
  have hs₀ : (s₀ : ℝ) < 1 := max_lt zero_lt_one (by linarith)
  have hs₀V : ∀ t, F (s₀, t) ∈ V' := fun t => hεV (by
    have e : (s₀ : ℝ) = max 0 (1 - ε / 2) := rfl
    rw [Subtype.dist_eq, Icc.coe_one, Real.dist_eq, abs_of_nonpos (by linarith), e]
    linarith [le_max_right (0 : ℝ) (1 - ε / 2)]) t (mem_univ t)
  refine ⟨F.eval s₀, fun t h0 h1 => ⟨hV'V (hs₀V t), hF s₀ t hs₀ h0 h1⟩, ?_⟩
  refine ⟨{ toFun := fun z => F (z.1 * s₀, z.2)
            continuous_toFun := F.continuous.comp ((continuous_fst.mul continuous_const).prodMk
              continuous_snd)
            map_zero_left := fun t => by simp
            map_one_left := fun t => by simp [Path.Homotopy.eval]
            prop' := fun s t ht => by
              rcases ht with rfl | rfl
              · simp
              · simp }, fun s t h0 h1 => ?_⟩
  exact hF _ t (by
    show ((s * s₀ : I) : ℝ) < 1
    rw [Set.Icc.coe_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left s₀.2.1 s.2.2) hs₀) h0 h1

end Trivial

section Winding

/-- `ℂ ∖ {0}` as a subtype. -/
abbrev CStar : Type := {w : ℂ // w ≠ 0}

/-- `exp : ℂ → ℂ ∖ {0}`. -/
def cExp : C(ℂ, CStar) := ⟨fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩, by fun_prop⟩

theorem cExp_apply (z : ℂ) : ((cExp z : CStar) : ℂ) = Complex.exp z := rfl

theorem isCoveringMap_cExp : IsCoveringMap (cExp : ℂ → CStar) := Complex.isCoveringMap_exp

/-- Two lifts through `exp` of the same path differ by a constant. -/
theorem expLift_sub_const {Γ Γ' : C(I, ℂ)} (h : ∀ t, Complex.exp (Γ t) = Complex.exp (Γ' t))
    (t : I) : Γ' t = Γ t + (Γ' 0 - Γ 0) := by
  have hc : Complex.exp (Γ' 0 - Γ 0) = 1 := by
    rw [Complex.exp_sub, ← h 0, div_self (Complex.exp_ne_zero _)]
  have := isCoveringMap_cExp.eq_of_comp_eq (g₁ := fun t => Γ t + (Γ' 0 - Γ 0)) (g₂ := Γ')
    (by fun_prop) Γ'.continuous (funext fun t => Subtype.ext (by
      simp only [comp_apply, cExp_apply, Complex.exp_add, hc, mul_one, h t])) 0 (by ring)
  exact (congrFun this t).symm

/-- Every path of `ℂ ∖ {0}` lifts through `exp`. -/
theorem exists_expLift (δ : C(I, CStar)) : ∃ Γ : C(I, ℂ), ∀ t, Complex.exp (Γ t) = δ t := by
  obtain ⟨Γ, hΓ, -⟩ := isCoveringMap_cExp.exists_path_lifts δ (Complex.log (δ 0))
    (Subtype.ext (Complex.exp_log (δ 0).2).symm)
  exact ⟨Γ, fun t => congrArg Subtype.val (congrFun hΓ t)⟩

theorem exists_int_winding {z : CStar} (δ : Path z z) :
    ∃ n : ℤ, ∀ Γ : C(I, ℂ), (∀ t, Complex.exp (Γ t) = δ t) →
      Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I) := by
  obtain ⟨Γ₀, hΓ₀⟩ := exists_expLift δ.toContinuousMap
  have h01 : Complex.exp (Γ₀ 1) = Complex.exp (Γ₀ 0) := by
    rw [hΓ₀, hΓ₀]; simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h01
  refine ⟨n, fun Γ hΓ => ?_⟩
  have h := expLift_sub_const (Γ := Γ₀) (Γ' := Γ) (fun t => by rw [hΓ₀ t, hΓ t]; rfl)
  rw [h 1, hn, h 0]; ring

/-- The winding number of a loop of `ℂ ∖ {0}` (through any lift by `exp`). -/
def cWinding {z : CStar} (δ : Path z z) : ℤ := (exists_int_winding δ).choose

theorem cWinding_spec {z : CStar} (δ : Path z z) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = δ t) :
    Γ 1 = Γ 0 + cWinding δ * (2 * Real.pi * Complex.I) :=
  (exists_int_winding δ).choose_spec Γ hΓ

theorem cWinding_eq {z : CStar} (δ : Path z z) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = δ t) {n : ℤ} (hn : Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I)) :
    cWinding δ = n := by
  have h := cWinding_spec δ hΓ
  rw [hn] at h
  have h' : ((n : ℂ) - cWinding δ) * (2 * Real.pi * Complex.I) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact_mod_cast (sub_eq_zero.1 h'').symm
  · exact absurd h'' Complex.two_pi_I_ne_zero

theorem cWinding_homotopic {z : CStar} {δ δ' : Path z z} (h : δ.Homotopic δ') :
    cWinding δ = cWinding δ' := by
  obtain ⟨H⟩ := h
  have hrel : δ.toContinuousMap.HomotopicRel δ'.toContinuousMap {0, 1} := ⟨H⟩
  have h0 : δ.toContinuousMap 0 = cExp (Complex.log z) :=
    Subtype.ext (by simp [cExp_apply, Complex.exp_log z.2])
  have h0' : δ'.toContinuousMap 0 = cExp (Complex.log z) :=
    Subtype.ext (by simp [cExp_apply, Complex.exp_log z.2])
  have key := isCoveringMap_cExp.liftPath_apply_one_eq_of_homotopicRel hrel _ h0 h0'
  set Γ := isCoveringMap_cExp.liftPath δ.toContinuousMap _ h0
  set Γ' := isCoveringMap_cExp.liftPath δ'.toContinuousMap _ h0'
  have hΓ : ∀ t, Complex.exp (Γ t) = δ t := fun t =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftPath_lifts δ.toContinuousMap _ h0) t)
  have hΓ' : ∀ t, Complex.exp (Γ' t) = δ' t := fun t =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftPath_lifts δ'.toContinuousMap _ h0') t)
  have e0 : Γ 0 = Γ' 0 := by
    rw [isCoveringMap_cExp.liftPath_zero, isCoveringMap_cExp.liftPath_zero]
  refine (cWinding_eq δ' hΓ' ?_).symm
  rw [← key, ← e0]
  exact cWinding_spec δ hΓ

theorem cWinding_trans {z : CStar} (δ₁ δ₂ : Path z z) :
    cWinding (δ₁.trans δ₂) = cWinding δ₁ + cWinding δ₂ := by
  obtain ⟨Γ₁, hΓ₁⟩ := exists_expLift δ₁.toContinuousMap
  obtain ⟨Γ₂, hΓ₂⟩ := exists_expLift δ₂.toContinuousMap
  have e1 := cWinding_spec δ₁ hΓ₁
  have e2 := cWinding_spec δ₂ hΓ₂
  set c := Γ₁ 1 - Γ₂ 0
  have hc : Complex.exp c = 1 := by
    rw [Complex.exp_sub, hΓ₁, hΓ₂]
    simp [div_self z.2]
  let P₁ : Path (Γ₁ 0) (Γ₁ 1) := ⟨Γ₁, rfl, rfl⟩
  let P₂ : Path (Γ₁ 1) (Γ₂ 1 + c) :=
    ⟨⟨fun t => Γ₂ t + c, by fun_prop⟩, by simp [c], rfl⟩
  have hP : ∀ t, Complex.exp ((P₁.trans P₂) t) = (δ₁.trans δ₂) t := by
    intro t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hΓ₁ _
    · show Complex.exp (Γ₂ _ + c) = _
      rw [Complex.exp_add, hc, mul_one, hΓ₂]; rfl
  refine cWinding_eq _ (Γ := (P₁.trans P₂).toContinuousMap) hP ?_
  show (P₁.trans P₂) 1 = (P₁.trans P₂) 0 + _
  rw [Path.target, Path.source]
  push_cast
  rw [show Γ₂ 1 + c = Γ₂ 1 - Γ₂ 0 + Γ₁ 1 by ring, e2, e1]; ring

/-- The loop `t ↦ z e^{2πint}` of `ℂ ∖ {0}`. -/
def cLoop (z : CStar) (n : ℤ) : Path z z where
  toFun t := ⟨z * Complex.exp (n * (2 * Real.pi * Complex.I) * (t : ℝ)),
    mul_ne_zero z.2 (Complex.exp_ne_zero _)⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp [Complex.exp_int_mul_two_pi_mul_I])

theorem cWinding_cLoop (z : CStar) (n : ℤ) : cWinding (cLoop z n) = n := by
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log z + n * (2 * Real.pi * Complex.I) * (t : ℝ),
    by fun_prop⟩) (fun t => ?_) (by simp)
  show Complex.exp (Complex.log z + _) = z * _
  rw [Complex.exp_add, Complex.exp_log z.2]

theorem homotopic_refl_of_cWinding_eq_zero {z : CStar} (δ : Path z z) (h : cWinding δ = 0) :
    δ.Homotopic (Path.refl z) := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift δ.toContinuousMap
  have e := cWinding_spec δ hΓ
  rw [h] at e
  simp only [Int.cast_zero, zero_mul, add_zero] at e
  let P : Path (Γ 0) (Γ 0) := ⟨Γ, rfl, e⟩
  have hz : cExp (Γ 0) = z := Subtype.ext (by rw [cExp_apply, hΓ 0]; simp)
  subst hz
  have h1 := Path.Homotopic.map (⟨lineHomotopy P (Path.refl (Γ 0))⟩ : P.Homotopic (Path.refl (Γ 0))) cExp
  have hm : P.map cExp.continuous = δ := by
    ext t; show Complex.exp (Γ t) = _; rw [hΓ t]; rfl
  have hr : (Path.refl (Γ 0)).map cExp.continuous = Path.refl (cExp (Γ 0)) := by
    ext t; rfl
  rw [← hm, ← hr]
  exact h1

end Winding

section Carthesian

/-- `O`, the origin of `ℝ³` (`RamcovGX.tex:1217`). -/
abbrev cartO : ℝ × ℝ × ℝ := (0, 0, 0)

/-- `S₁ = {y = z = 0}` (`RamcovGX.tex:1216`). -/
def cartS₁ : Set (ℝ × ℝ × ℝ) := {q | q.2.1 = 0 ∧ q.2.2 = 0}

/-- `S₂`, the topologist's sine curve in the plane `{z = 0}` and its limit segment
(`RamcovGX.tex:1216`, read with `z = 0` on the graph, see the findings). -/
def cartS₂ : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ≠ 0 ∧ q.2.1 = Real.sin (1 / q.1) ∧ q.2.2 = 0} ∪ {q | q.1 = 0 ∧ q.2.2 = 0 ∧ |q.2.1| ≤ 1}

theorem cartO_mem_cartS₁ : cartO ∈ cartS₁ := ⟨rfl, rfl⟩

theorem cartO_mem_cartS₂ : cartO ∈ cartS₂ := Or.inr ⟨rfl, rfl, by simp⟩

/-- `ex:consider_carthesian_coordinates_usual`, second claim (`RamcovGX.tex:1219`): every loop of
`Ω(O,O,Y ∖ S₁)` is homotopically trivial (by the radial contraction: `S₁` is a cone at `O`),
hence almost trivial. -/
theorem carthesian_S₁_trivial {γ : Path cartO cartO} (hγ : MemOmega cartS₁ᶜ γ) :
    IsHomTrivial cartS₁ᶜ γ ∧ AlmostTrivial cartS₁ᶜ γ := by
  have h : IsHomTrivial cartS₁ᶜ γ := by
    refine ⟨{ toFun := fun z => (1 - (z.1 : ℝ)) • γ z.2
              continuous_toFun := by fun_prop
              map_zero_left := fun t => by simp
              map_one_left := fun t => by simp; rfl
              prop' := fun s t ht => by
                rcases ht with rfl | rfl
                · simp
                · simp }, fun s t hs h0 h1 => ?_⟩
    have hγt := hγ t h0 h1
    have hne : (1 - (s : ℝ)) ≠ 0 := by linarith
    show (1 - (s : ℝ)) • γ t ∉ cartS₁
    rintro ⟨h2, h3⟩
    apply hγt
    simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, mul_eq_zero, hne, false_or] at h2 h3
    exact ⟨h2, h3⟩
  exact ⟨h, h.almostTrivial hγ⟩

/-- `ex:consider_carthesian_coordinates_usual`, first claim (`RamcovGX.tex:1218`), as a `Prop`:
`π₁(Y ∖ S) ≅ ℤ`. -/
def CartPiOneZ (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∀ y : (Sᶜ : Set (ℝ × ℝ × ℝ)), Nonempty (FundamentalGroup (Sᶜ : Set (ℝ × ℝ × ℝ)) y ≃* Multiplicative ℤ)

theorem cart_ne_zero (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    ((q.1.2.1 : ℂ) + q.1.2.2 * Complex.I) ≠ 0 := fun h => q.2
  ⟨by simpa using congrArg Complex.re h, by simpa using congrArg Complex.im h⟩

/-- `(x, y, z) ↦ y + iz`, from `ℝ³ ∖ S₁` to `ℂ ∖ {0}`. -/
def cartF : C((cartS₁ᶜ : Set (ℝ × ℝ × ℝ)), CStar) :=
  ⟨fun q => ⟨(q.1.2.1 : ℂ) + q.1.2.2 * Complex.I, cart_ne_zero q⟩, by fun_prop⟩

theorem cartF_re (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : ((cartF q : CStar) : ℂ).re = q.1.2.1 := by
  simp [cartF]

theorem cartF_im (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : ((cartF q : CStar) : ℂ).im = q.1.2.2 := by
  simp [cartF]

theorem not_mem_cartS₁_of_ne_zero (x : ℝ) (w : CStar) :
    (x, (w : ℂ).re, (w : ℂ).im) ∈ (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) := fun h =>
  w.2 (Complex.ext h.1 h.2)

/-- The winding number around `S₁`, a homomorphism `π₁(ℝ³ ∖ S₁, y) → ℤ`. -/
def cartDeg (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    FundamentalGroup (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) y →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Quotient.lift (fun γ : Path y y => cWinding (γ.map cartF.continuous))
    (fun _ _ h => cWinding_homotopic (Path.Homotopic.map h cartF)) (FundamentalGroup.toPath g))
  map_one' := by
    show Multiplicative.ofAdd (cWinding ((Path.refl y).map cartF.continuous)) = 1
    rw [show cWinding ((Path.refl y).map cartF.continuous) = 0 from
      cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log (cartF y)))
        (fun t => by simp [Complex.exp_log (cartF y).2]) (by simp)]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (Quotient.lift _ _ ((FundamentalGroup.toPath b).trans
      (FundamentalGroup.toPath a))) = Multiplicative.ofAdd (Quotient.lift _ _ _) *
        Multiplicative.ofAdd (Quotient.lift _ _ _)
    induction FundamentalGroup.toPath a using Quotient.inductionOn with | h α =>
    induction FundamentalGroup.toPath b using Quotient.inductionOn with | h β =>
    show Multiplicative.ofAdd (cWinding ((β.trans α).map cartF.continuous)) =
      Multiplicative.ofAdd (cWinding (α.map cartF.continuous)) *
        Multiplicative.ofAdd (cWinding (β.map cartF.continuous))
    rw [Path.map_trans, cWinding_trans, ← ofAdd_add, add_comm]

theorem cartDeg_mk (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) (γ : Path y y) :
    cartDeg y (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (cWinding (γ.map cartF.continuous)) := rfl

theorem cartDeg_bijective (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : Bijective (cartDeg y) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    induction g using Quotient.inductionOn with | h γ =>
    have h0 : cWinding (γ.map cartF.continuous) = 0 := by
      have := hg
      rw [show (Quotient.mk _ γ : FundamentalGroup _ y) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) from rfl, cartDeg_mk] at this
      exact Multiplicative.ofAdd.injective this
    obtain ⟨G⟩ := homotopic_refl_of_cWinding_eq_zero _ h0
    let F : Path.Homotopy γ (Path.refl y) :=
      { toFun := fun w => ⟨((1 - (w.1 : ℝ)) * (γ w.2).1.1 + (w.1 : ℝ) * y.1.1,
            ((G w : CStar) : ℂ).re, ((G w : CStar) : ℂ).im), not_mem_cartS₁_of_ne_zero _ _⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have hG : Continuous fun w => ((G w : CStar) : ℂ) :=
            continuous_subtype_val.comp G.continuous
          refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
          · have : Continuous fun w : I × I => (γ w.2).1.1 :=
              continuous_fst.comp (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))
            fun_prop
          · exact Complex.continuous_re.comp hG
          · exact Complex.continuous_im.comp hG
        map_zero_left := fun t => by
          have h : G (0, t) = cartF (γ t) := G.apply_zero t
          apply Subtype.ext
          show ((1 - ((0 : I) : ℝ)) * (γ t).1.1 + ((0 : I) : ℝ) * y.1.1,
            ((G (0, t) : CStar) : ℂ).re, ((G (0, t) : CStar) : ℂ).im) = (γ t).1
          rw [h, cartF_re, cartF_im]; simp
        map_one_left := fun t => by
          have h : G (1, t) = cartF y := G.apply_one t
          apply Subtype.ext
          show ((1 - ((1 : I) : ℝ)) * (γ t).1.1 + ((1 : I) : ℝ) * y.1.1,
            ((G (1, t) : CStar) : ℂ).re, ((G (1, t) : CStar) : ℂ).im) = y.1
          rw [h, cartF_re, cartF_im]; simp
        prop' := fun s t ht => by
          apply Subtype.ext
          have hγt : γ t = y := by rcases ht with rfl | rfl <;> simp
          have hGt : G (s, t) = cartF y := by
            rw [G.eq_fst s ht]; simp [hγt]
          show ((1 - (s : ℝ)) * (γ t).1.1 + (s : ℝ) * y.1.1,
            ((G (s, t) : CStar) : ℂ).re, ((G (s, t) : CStar) : ℂ).im) = (γ t).1
          rw [hGt, cartF_re, cartF_im, hγt]
          ext <;> simp; ring }
    exact Quotient.sound ⟨F⟩
  · intro n
    let c := cLoop (cartF y) (Multiplicative.toAdd n)
    let γ : Path y y :=
      { toFun := fun t => ⟨(y.1.1, ((c t : CStar) : ℂ).re, ((c t : CStar) : ℂ).im),
          not_mem_cartS₁_of_ne_zero _ _⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have hc : Continuous fun t => ((c t : CStar) : ℂ) :=
            continuous_subtype_val.comp c.continuous
          exact continuous_const.prodMk ((Complex.continuous_re.comp hc).prodMk
            (Complex.continuous_im.comp hc))
        source' := by
          apply Subtype.ext
          simp only [c.source, cartF_re, cartF_im]
        target' := by
          apply Subtype.ext
          simp only [c.target, cartF_re, cartF_im] }
    have hγ : γ.map cartF.continuous = c := by
      ext t
      show ((cartF (γ t) : CStar) : ℂ) = ((c t : CStar) : ℂ)
      apply Complex.ext
      · rw [cartF_re]; rfl
      · rw [cartF_im]; rfl
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ), ?_⟩
    rw [cartDeg_mk, hγ, cWinding_cLoop]
    rfl

/-- `ex:consider_carthesian_coordinates_usual`, first claim for `S₁` (`RamcovGX.tex:1218`):
`π₁(ℝ³ ∖ S₁) ≅ ℤ` at every base point, by the number of turns around `S₁`. -/
theorem carthesian_piOne_S₁_at (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    Nonempty (FundamentalGroup (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) y ≃* Multiplicative ℤ) :=
  ⟨MulEquiv.ofBijective (cartDeg y) (cartDeg_bijective y)⟩

/-- `ex:consider_carthesian_coordinates_usual`, first claim, for `S₁`. -/
theorem carthesian_piOne_S₁ : CartPiOneZ cartS₁ := carthesian_piOne_S₁_at

theorem carthesian_piOne_S₂ : CartPiOneZ cartS₂ := by
  sorry -- SORRY(ex:consider_carthesian_coordinates_usual): π₁ of the complement of the topologist's sine curve (with its limit segment) in ℝ³: needs, beyond π₁(ℝ³ ∖ line), a deformation of the complement of an ε-neighbourhood of S₂ onto ℝ³ ∖ S₁ (the homeomorphism the paper asserts at l.1227) and a limit argument over ε; left to the reader in the paper

/-- `ex:consider_carthesian_coordinates_usual`, third claim (`RamcovGX.tex:1221`): every loop of
`Ω(O,O,Y ∖ S₂)` is almost trivial. -/
theorem carthesian_S₂_almostTrivial {γ : Path cartO cartO} (hγ : MemOmega cartS₂ᶜ γ) :
    AlmostTrivial cartS₂ᶜ γ := by
  sorry -- SORRY(ex:consider_carthesian_coordinates_usual): the paper's proof (l.1227) rests on "Y ∖ B̄(S₂,ε) is homeomorphic to Y ∖ S₁" and on pushing γ_{|[t₁,t₂]} into B ∖ B(S₂,ε); formalizing it needs an explicit isotopy of ℝ³ moving the closed ε-neighbourhood of the topologist's sine curve onto a neighbourhood of a segment, which is not available

/-- `ex:consider_carthesian_coordinates_usual`, fourth claim (`RamcovGX.tex:1222`): a loop of
`Ω(O,O,Y ∖ S₂)` which is not homotopically trivial. -/
theorem carthesian_S₂_not_trivial :
    ∃ γ : Path cartO cartO, MemOmega cartS₂ᶜ γ ∧ ¬ IsHomTrivial cartS₂ᶜ γ := by
  sorry -- SORRY(ex:consider_carthesian_coordinates_usual): the paper's proof uses mod 2 intersection numbers of loops with the plane {z = 0} and with the components of {z = 0} ∖ S₂ in a ball, and their homotopy invariance (MR2680546); intersection theory for continuous curves is not available at this pin

end Carthesian

/-! ### `ex:consider_fiber_above_homeomorphic` -/

section Tower

variable {A : ℕ → Type*} [∀ k, TopologicalSpace (A k)] [∀ k, DiscreteTopology (A k)]
  (f : ∀ k, A (k + 1) → A k)

/-- The projective limit of a tower `⋯ → A 2 → A 1 → A 0` (a subspace of the product). -/
def TowerLim : Set (∀ k, A k) := {x | ∀ k, f k (x (k + 1)) = x k}

variable (hfib : ∀ k (c : A k), Infinite (f k ⁻¹' {c}) ∧ Countable (f k ⁻¹' {c}))

/-- A bijection of each fibre with `ℕ`. -/
def towerEqv (k : ℕ) (c : A k) : f k ⁻¹' {c} ≃ ℕ :=
  haveI := (hfib k c).1
  haveI := (hfib k c).2
  (nonempty_denumerable (f k ⁻¹' {c})).some.eqv

/-- The thread of the tower starting at `a₀` with fibre coordinates `s`. -/
def towerSeq (a₀ : A 0) (s : ℕ → ℕ) : ∀ k, A k
  | 0 => a₀
  | k + 1 => ((towerEqv f hfib k (towerSeq a₀ s k)).symm (s k)).1

theorem towerSeq_mem (a₀ : A 0) (s : ℕ → ℕ) : towerSeq f hfib a₀ s ∈ TowerLim f := fun k =>
  ((towerEqv f hfib k (towerSeq f hfib a₀ s k)).symm (s k)).2

/-- The fibre coordinates of a thread. -/
def towerCoord (x : TowerLim f) (k : ℕ) : ℕ := towerEqv f hfib k (x.1 k) ⟨x.1 (k + 1), x.2 k⟩

theorem towerSeq_towerCoord (x : TowerLim f) :
    towerSeq f hfib (x.1 0) (towerCoord f hfib x) = x.1 := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (fun t => ((towerEqv f hfib k t).symm (towerCoord f hfib x k)).1)
      (towerSeq f hfib (x.1 0) (towerCoord f hfib x) k) = x.1 (k + 1)
    rw [ih]
    simp [towerCoord]

theorem towerCoord_towerSeq (a₀ : A 0) (s : ℕ → ℕ) :
    towerCoord f hfib ⟨towerSeq f hfib a₀ s, towerSeq_mem f hfib a₀ s⟩ = s := by
  funext k
  show towerEqv f hfib k (towerSeq f hfib a₀ s k) ⟨((towerEqv f hfib k (towerSeq f hfib a₀ s k)).symm
    (s k)).1, _⟩ = s k
  simp

theorem continuous_towerCoord : Continuous (towerCoord f hfib) := by
  refine continuous_pi fun k => ?_
  let g : A k × A (k + 1) → ℕ := fun p =>
    if h : f k p.2 = p.1 then towerEqv f hfib k p.1 ⟨p.2, h⟩ else 0
  have hg : (fun x : TowerLim f => towerCoord f hfib x k) =
      g ∘ fun x : TowerLim f => (x.1 k, x.1 (k + 1)) := by
    funext x
    simp only [g, comp_apply, dif_pos (x.2 k)]
    rfl
  rw [hg]
  exact continuous_of_discreteTopology.comp
    (((continuous_apply k).comp continuous_subtype_val).prodMk
      ((continuous_apply (k + 1)).comp continuous_subtype_val))

theorem continuous_towerSeq_apply (k : ℕ) :
    Continuous fun p : A 0 × (ℕ → ℕ) => towerSeq f hfib p.1 p.2 k := by
  induction k with
  | zero => exact continuous_fst
  | succ k ih =>
    let g : A k × ℕ → A (k + 1) := fun q => ((towerEqv f hfib k q.1).symm q.2).1
    have : (fun p : A 0 × (ℕ → ℕ) => towerSeq f hfib p.1 p.2 (k + 1)) =
        g ∘ fun p => (towerSeq f hfib p.1 p.2 k, p.2 k) := rfl
    rw [this]
    exact continuous_of_discreteTopology.comp (ih.prodMk ((continuous_apply k).comp continuous_snd))

/-- The projective limit of a tower of discrete spaces with countably infinite fibres is
`A 0 × ℕ^ℕ`. -/
def towerHomeomorph : TowerLim f ≃ₜ A 0 × (ℕ → ℕ) where
  toFun x := (x.1 0, towerCoord f hfib x)
  invFun p := ⟨towerSeq f hfib p.1 p.2, towerSeq_mem f hfib p.1 p.2⟩
  left_inv x := Subtype.ext (towerSeq_towerCoord f hfib x)
  right_inv p := Prod.ext rfl (towerCoord_towerSeq f hfib p.1 p.2)
  continuous_toFun := ((continuous_apply 0).comp continuous_subtype_val).prodMk
    (continuous_towerCoord f hfib)
  continuous_invFun := (continuous_pi fun k => continuous_towerSeq_apply f hfib k).subtype_mk _

end Tower

/-- `α^ℕ ≃ₜ α × α^ℕ` (head and tail). -/
def piNatHeadTail (α : Type*) [TopologicalSpace α] : (ℕ → α) ≃ₜ α × (ℕ → α) where
  toFun s := (s 0, fun n => s (n + 1))
  invFun p n := Nat.casesOn n p.1 p.2
  left_inv s := funext fun n => by cases n <;> rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun n => continuous_apply (n + 1))
  continuous_invFun := continuous_pi fun n => by
    cases n with
    | zero => exact continuous_fst
    | succ n => exact (continuous_apply n).comp continuous_snd

/-- For `B` countable, nonempty and discrete, `B × ℕ^ℕ ≃ₜ ℕ^ℕ`. -/
def prodNatPiHomeomorph (B : Type*) [TopologicalSpace B] [DiscreteTopology B] [Countable B]
    [Nonempty B] : B × (ℕ → ℕ) ≃ₜ (ℕ → ℕ) :=
  haveI : Infinite (B × ℕ) := inferInstance
  ((Homeomorph.refl B).prodCongr (piNatHeadTail ℕ)).trans ((Homeomorph.prodAssoc B ℕ (ℕ → ℕ)).symm.trans
    (((nonempty_denumerable (B × ℕ)).some.eqv.toHomeomorphOfDiscrete.prodCongr
      (Homeomorph.refl _)).trans (piNatHeadTail ℕ).symm))

/-- `ℕ^ℕ` (product topology) is not locally compact. -/
theorem not_locallyCompactSpace_nat_pi {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [Infinite α] [Inhabited α] : ¬ LocallyCompactSpace (ℕ → α) := by
  intro h
  obtain ⟨s, hs, -, hsc⟩ := h.local_compact_nhds (fun _ => default) univ univ_mem
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨J, hJ, t, ht, hts⟩ := hs
  obtain ⟨n, hn⟩ := hJ.infinite_compl.nonempty
  have himg : (fun x : ℕ → α => x n) '' s = univ := by
    refine eq_univ_of_forall fun m => ⟨Function.update (fun _ => default) n m, hts fun i hi => ?_,
      by simp⟩
    have hin : i ≠ n := fun h => hn (h ▸ hi)
    rw [Function.update_of_ne hin]
    exact mem_of_mem_nhds (ht i)
  have := hsc.image (continuous_apply n)
  rw [himg] at this
  exact infinite_univ (isCompact_iff_finite.1 this)


section FiberExample

/-- `S = {(1/n, 0) : n ∈ ℕ* ∪ {∞}} ⊆ ℝ² = ℂ` (`RamcovGX.tex:1410`). -/
def fibS : Set ℂ := insert 0 (range fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))

theorem isClosed_fibS : IsClosed fibS := by
  refine (Tendsto.isCompact_insert_range ?_).isClosed
  have h := (Complex.continuous_ofReal.tendsto 0).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Complex.ofReal_zero] at h
  exact h

theorem countable_fibS : fibS.Countable := (countable_range _).insert 0

/-- `S` is skeletal. -/
theorem isSkeletal_fibS : IsSkeletal fibS := isSkeletal_of_countable_complex isClosed_fibS countable_fibS

/-- `ℂ ∖ S` is semilocally simply connected. -/
theorem semilocallySimplyConnected_fibS : SemilocallySimplyConnected (fibSᶜ : Set ℂ) :=
  semilocallySimplyConnected_of_isOpen isClosed_fibS.isOpen_compl

/-- The disc `D_{k+1}` of `ℂ` centred at `0` of radius `1/(k + 1/2)` (the paper's `D_n`,
`n = k + 1`, `RamcovGX.tex:1415`). -/
def fibD (k : ℕ) : Set ℂ := Metric.ball 0 (1 / ((k : ℝ) + 1 / 2))

theorem fibD_radius_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1 / 2) := by positivity

theorem fibD_subset_iff {m n : ℕ} : fibD m ⊆ fibD n ↔ n ≤ m := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hr : 1 / ((n : ℝ) + 1 / 2) < 1 / ((m : ℝ) + 1 / 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast (by linarith [(show (m : ℝ) < n by exact_mod_cast hlt)] : (m : ℝ) + 1 / 2 < n + 1 / 2))
    set ρ := (1 / ((n : ℝ) + 1 / 2) + 1 / ((m : ℝ) + 1 / 2)) / 2 with hρdef
    have hρ : 0 ≤ ρ := by have := fibD_radius_pos n; have := fibD_radius_pos m; positivity
    have hmem : ((ρ : ℝ) : ℂ) ∈ fibD m := by
      rw [fibD, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ]
      linarith [hρdef]
    have := h hmem
    rw [fibD, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ] at this
    linarith [hρdef]
  · intro h
    apply Metric.ball_subset_ball
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by linarith [(show (n : ℝ) ≤ m by exact_mod_cast h)] : (n : ℝ) + 1 / 2 ≤ m + 1 / 2))

theorem fibD_succ_subset (k : ℕ) : fibD (k + 1) ⊆ fibD k := fibD_subset_iff.2 (Nat.le_succ k)

theorem fibD_injective : Injective fibD := fun _ _ h =>
  le_antisymm (fibD_subset_iff.1 h.symm.subset) (fibD_subset_iff.1 h.subset)

theorem isCNbhd_fibD (k : ℕ) : IsCNbhd (0 : ℂ) (fibD k) :=
  ⟨Metric.isOpen_ball, (convex_ball _ _).isPreconnected, Metric.mem_ball_self (fibD_radius_pos k)⟩

/-- The discs `D_n` form a basis of neighbourhoods of `0`. -/
theorem fibD_basis : ∀ N ∈ 𝓝 (0 : ℂ), ∃ U ∈ range fibD, U ⊆ N := by
  intro N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨fibD k, mem_range_self k, (Metric.ball_subset_ball ?_).trans hεN⟩
  have h1 : 1 / ((k : ℝ) + 1 / 2) ≤ 2 * (1 / ((k : ℝ) + 1)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  linarith

theorem piOneUMap_self {Y : Type*} [TopologicalSpace Y] {S : Set Y} {a : Y} {U : Set Y}
    (h : U ⊆ U) (c : PiOneU S a U) : piOneUMap h c = c := by
  induction c using Quotient.inductionOn with | h γ => rfl

theorem piOneUMap_piOneUMap {Y : Type*} [TopologicalSpace Y] {S : Set Y} {a : Y} {U V W : Set Y}
    (h₁ : U ⊆ V) (h₂ : V ⊆ W) (c : PiOneU S a U) :
    piOneUMap h₂ (piOneUMap h₁ c) = piOneUMap (h₁.trans h₂) c := by
  induction c using Quotient.inductionOn with | h γ => rfl

theorem not_mem_fibS_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : z ∉ fibS := by
  rintro (h0 | ⟨n, hn⟩)
  · exact h (by rw [h0]; simp)
  · exact h (by rw [← hn]; simp)

/-- A point of `D_k ∖ S` on the imaginary axis. -/
def fibQ (k : ℕ) : ℂ := ((1 / ((k : ℝ) + 1 / 2) / 2 : ℝ) : ℂ) * Complex.I

theorem fibQ_mem (k : ℕ) : fibQ k ∈ fibD k ∩ fibSᶜ := by
  have hr := fibD_radius_pos k
  refine ⟨?_, not_mem_fibS_of_im_ne_zero ?_⟩
  · rw [fibD, Metric.mem_ball, dist_zero_right, fibQ, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  · rw [fibQ, Complex.mul_I_im, Complex.ofReal_re]; positivity

theorem isPathConnected_fibS_compl : IsPathConnected (fibSᶜ : Set ℂ) := by
  have hO : IsPortly (fibSᶜ : Set ℂ) := isSkeletal_iff.1 isSkeletal_fibS
  exact hO.isOpen.isConnected_iff_isPathConnected.1 hO.isConnected

theorem isPathConnected_fibD_diff (k : ℕ) : IsPathConnected (fibD k ∩ fibSᶜ) := by
  have ho : IsOpen (fibD k ∩ fibSᶜ) := Metric.isOpen_ball.inter isClosed_fibS.isOpen_compl
  refine ho.isConnected_iff_isPathConnected.1 ⟨⟨_, fibQ_mem k⟩, ?_⟩
  rw [← Set.sdiff_eq]
  exact isPreconnected_diff_countable countable_fibS Metric.isOpen_ball
    (convex_ball _ _).isPreconnected

/-- A path from `a` into `U`, extended by a path of `U ∖ S`, is homotopic to itself with free end
in `U`. -/
theorem freeHomotopic_trans_tail {Y : Type*} [TopologicalSpace Y] {S U : Set Y} {a c d : Y}
    (P : Path a c) (hP : ∀ t, P t ∈ Sᶜ) (hc : c ∈ U) (ω : Path c d) (hω : ∀ t, ω t ∈ U ∩ Sᶜ) :
    FreeHomotopic S a U (P.trans ω).toContinuousMap P.toContinuousMap := by
  have step2 := freeHomotopic_trans_shrink P hP ω hω
  have step3 : FreeHomotopic S a U (P.trans (Path.refl c)).toContinuousMap P.toContinuousMap := by
    refine freeHomotopic_of_homotopicIn hc ?_
    have hr : ∀ t, (Path.refl c) t ∈ Sᶜ := fun _ => by simpa using hP 1
    refine homotopicIn_iff.2 ⟨path_trans_mem hP hr, hP, ?_⟩
    rw [pathToSub_trans _ _ hP hr]
    have : pathToSub (Path.refl c) hr = Path.refl _ := by ext; rfl
    rw [this]
    exact Path.Homotopic.trans_refl _
  exact step2.trans step3

/-- `π₁(a, D_k)` is countable (`π₁(ℂ ∖ S)` is countable and maps onto it). -/
theorem countable_piOneU_fibD (a : ℂ) (ha : a ∈ fibSᶜ) (k : ℕ) :
    Countable (PiOneU fibS a (fibD k)) := by
  obtain ⟨hu, huS⟩ := fibQ_mem k
  set u := fibQ k
  let a' : (fibSᶜ : Set ℂ) := ⟨a, ha⟩
  let u' : (fibSᶜ : Set ℂ) := ⟨u, huS⟩
  haveI : LocPathConnectedSpace (fibSᶜ : Set ℂ) :=
    isClosed_fibS.isOpen_compl.locPathConnectedSpace
  haveI : PathConnectedSpace (fibSᶜ : Set ℂ) :=
    isPathConnected_iff_pathConnectedSpace.1 isPathConnected_fibS_compl
  haveI : Countable (FundamentalGroup (fibSᶜ : Set ℂ) a') :=
    UniversalCover.countable_fundamentalGroup semilocallySimplyConnected_fibS a'
  let P₀ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a' u')
  have hcancel : ∀ q : Path.Homotopic.Quotient a' u', (q.trans P₀.symm).trans P₀ = q := fun q => by
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  have hinj : Injective fun q : Path.Homotopic.Quotient a' u' =>
      (FundamentalGroup.fromPath (q.trans P₀.symm) : FundamentalGroup (fibSᶜ : Set ℂ) a') := by
    intro q q' h
    have h' : q.trans P₀.symm = q'.trans P₀.symm := h
    rw [← hcancel q, h', hcancel]
  haveI : Countable (Path.Homotopic.Quotient a' u') := hinj.countable
  let Ξ : Path.Homotopic.Quotient a' u' → PiOneU fibS a (fibD k) :=
    Quotient.lift (fun γ : Path a' u' => (Quotient.mk _ ⟨(γ.map continuous_subtype_val).toContinuousMap,
        by simp [a'], fun t => (γ t).2, by simpa [u'] using hu⟩ : PiOneU fibS a (fibD k)))
      (fun γ γ' ⟨F⟩ => Quotient.sound ⟨⟨fun z => (F z : ℂ), by fun_prop⟩, fun t => by simp,
        fun t => by simp, fun s => by simp [a'], fun s => by simpa [u'] using hu,
        fun z => (F z).2⟩)
  refine (show Surjective Ξ from ?_).countable
  intro cl
  induction cl using Quotient.inductionOn with | h γ =>
  obtain ⟨hγ0, hγS, hγU⟩ := γ.2
  obtain ⟨β, hβ⟩ := (isPathConnected_fibD_diff k).joinedIn (γ.1 1) ⟨hγU, hγS 1⟩ u ⟨hu, huS⟩
  let P : Path a (γ.1 1) := ⟨γ.1, hγ0, rfl⟩
  have hP : ∀ t, P t ∈ fibSᶜ := hγS
  have hPβ : ∀ t, (P.trans β) t ∈ fibSᶜ := path_trans_mem hP fun t => (hβ t).2
  refine ⟨Path.Homotopic.Quotient.mk (pathToSub (P.trans β) hPβ), ?_⟩
  exact Quotient.sound (freeHomotopic_trans_tail P hP hγU β hβ)

/-! The winding of a path around a point, read through `exp`. -/

/-- `Λ` lifts `c - δ` through `exp`. -/
def IsArgLift (c : ℂ) (δ : I → ℂ) (Λ : C(I, ℂ)) : Prop := ∀ t, Complex.exp (Λ t) = c - δ t

theorem exists_argLift {c : ℂ} {δ : C(I, ℂ)} (hδ : ∀ t, δ t ≠ c) : ∃ Λ, IsArgLift c δ Λ := by
  obtain ⟨Λ, hΛ⟩ := exists_expLift
    ⟨fun t => (⟨c - δ t, sub_ne_zero.2 (hδ t).symm⟩ : CStar), by fun_prop⟩
  exact ⟨Λ, hΛ⟩

theorem IsArgLift.sub_eq {c : ℂ} {δ : I → ℂ} {Λ Λ' : C(I, ℂ)} (h : IsArgLift c δ Λ)
    (h' : IsArgLift c δ Λ') : Λ' 1 - Λ' 0 = Λ 1 - Λ 0 := by
  have := expLift_sub_const (Γ := Λ) (Γ' := Λ') (fun t => by rw [h t, h' t])
  rw [this 1]; ring

theorem IsArgLift.trans {c x y z : ℂ} {P : Path x y} {Q : Path y z} {ΛP ΛQ : C(I, ℂ)}
    (hP : IsArgLift c P ΛP) (hQ : IsArgLift c Q ΛQ) :
    ∃ Λ, IsArgLift c (P.trans Q) Λ ∧ Λ 1 - Λ 0 = (ΛP 1 - ΛP 0) + (ΛQ 1 - ΛQ 0) := by
  set d := ΛP 1 - ΛQ 0
  have hne : c - y ≠ 0 := by
    have := hP 1; rw [P.target] at this; rw [← this]; exact Complex.exp_ne_zero _
  have hd : Complex.exp d = 1 := by
    rw [Complex.exp_sub, hP 1, hQ 0, P.target, Q.source, div_self hne]
  let L₁ : Path (ΛP 0) (ΛP 1) := ⟨ΛP, rfl, rfl⟩
  let L₂ : Path (ΛP 1) (ΛQ 1 + d) := ⟨⟨fun t => ΛQ t + d, by fun_prop⟩, by simp [d], rfl⟩
  refine ⟨(L₁.trans L₂).toContinuousMap, fun t => ?_, ?_⟩
  · show Complex.exp ((L₁.trans L₂) t) = c - (P.trans Q) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hP _
    · show Complex.exp (ΛQ _ + d) = _
      rw [Complex.exp_add, hd, mul_one, hQ]
  · show (L₁.trans L₂) 1 - (L₁.trans L₂) 0 = _
    rw [Path.target, Path.source]
    simp only [d]; ring

/-- The winding read through `exp`, corrected by the principal argument of the free end, is
invariant under homotopy with free end in a `U` on which `c - z` has positive real part. -/
theorem argLift_freeHomotopic {S U : Set ℂ} {a c : ℂ} (hc : c ∈ S)
    (hU : ∀ z ∈ U, 0 < (c - z).re) {γ₁ γ₂ : C(I, ℂ)} (h : FreeHomotopic S a U γ₁ γ₂)
    {Λ₁ Λ₂ : C(I, ℂ)} (h₁ : IsArgLift c γ₁ Λ₁) (h₂ : IsArgLift c γ₂ Λ₂) :
    Λ₁ 1 - Λ₁ 0 - Complex.log (c - γ₁ 1) = Λ₂ 1 - Λ₂ 0 - Complex.log (c - γ₂ 1) := by
  obtain ⟨H, h0, h1, ha, hHU, hS⟩ := h
  have hne : ∀ z, c - H z ≠ 0 := fun z h => hS z (by rw [sub_eq_zero] at h; rw [← h]; exact hc)
  have hca : c - a ≠ 0 := by have := hne (0, 0); rwa [ha] at this
  let G : C(I × I, CStar) := ⟨fun w => ⟨c - H (w.2, w.1), hne _⟩, by fun_prop⟩
  have hG0 : ∀ s, G (0, s) = cExp (ContinuousMap.const I (Complex.log (c - a)) s) := fun s =>
    Subtype.ext (by
      show c - H (s, 0) = Complex.exp (Complex.log (c - a))
      rw [ha, Complex.exp_log hca])
  let L := isCoveringMap_cExp.liftHomotopy G _ hG0
  have hL : ∀ w, Complex.exp (L w) = c - H (w.2, w.1) := fun w =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts G _ hG0) w)
  have hL0 : ∀ s, L (0, s) = Complex.log (c - a) := isCoveringMap_cExp.liftHomotopy_zero G _ hG0
  let g : I → ℂ := fun s => L (1, s) - Complex.log (c - H (s, 1))
  have hgc : Continuous g :=
    (L.continuous.comp (continuous_const.prodMk continuous_id)).sub
      ((continuous_const.sub (H.continuous.comp (continuous_id.prodMk continuous_const))).clog
        fun s => Complex.mem_slitPlane_iff.2 (Or.inl (hU _ (hHU s))))
  have hgexp : ∀ s s', cExp (g s) = cExp (g s') := fun s s' => Subtype.ext (by
    simp only [cExp_apply, g, Complex.exp_sub, hL, Complex.exp_log (hne _), div_self (hne _)])
  have hg := isCoveringMap_cExp.const_of_comp hgc hgexp 0 1
  have hs₀ : IsArgLift c γ₁ ⟨fun t => L (t, 0), by fun_prop⟩ := fun t => by
    show Complex.exp (L (t, 0)) = _; rw [hL, h0]
  have hs₁ : IsArgLift c γ₂ ⟨fun t => L (t, 1), by fun_prop⟩ := fun t => by
    show Complex.exp (L (t, 1)) = _; rw [hL, h1]
  have e₁ := h₁.sub_eq hs₀
  have e₂ := h₂.sub_eq hs₁
  simp only [ContinuousMap.coe_mk] at e₁ e₂
  rw [← e₁, ← e₂, hL0, hL0, ← h0 1, ← h1 1]
  simp only [g] at hg
  linear_combination hg

/-- The circle `t ↦ c + ε e^{2πijt}`. -/
def fibCircle (c : ℂ) (ε : ℝ) (j : ℤ) : Path (c + ε) (c + ε) where
  toFun t := c + ε * Complex.exp (j * (2 * Real.pi * Complex.I) * (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [Complex.exp_int_mul_two_pi_mul_I]

theorem argLift_fibCircle (c : ℂ) {ε : ℝ} (hε : 0 < ε) (j : ℤ) :
    IsArgLift c (fibCircle c ε j) ⟨fun t => (Real.log ε : ℂ) + Real.pi * Complex.I +
      j * (2 * Real.pi * Complex.I) * (t : ℝ), by fun_prop⟩ := fun t => by
  show Complex.exp (_ + _ + _) = c - (c + ε * _)
  rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hε,
    Complex.exp_pi_mul_I]
  ring

theorem norm_fibCircle_sub (c : ℂ) {ε : ℝ} (hε : 0 < ε) (j : ℤ) (t : I) :
    ‖fibCircle c ε j t - c‖ = ε := by
  show ‖c + ε * Complex.exp (j * (2 * Real.pi * Complex.I) * (t : ℝ)) - c‖ = ε
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le,
    Complex.norm_exp]
  simp

theorem fibS_sep {k : ℕ} {s : ℂ} (hs : s ∈ fibS) (hne : s ≠ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) :
    1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ ‖s - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)‖ := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases hs with h0 | ⟨m, rfl⟩
  · rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by linarith)
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hmk : m ≠ k := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hmk with h | h
    · have hm : (m : ℝ) + 1 ≤ k := by exact_mod_cast h
      have e : 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) =
          (((k : ℝ) + 2) * ((k : ℝ) + 1 - ((m : ℝ) + 1)) - ((m : ℝ) + 1)) /
            (((m : ℝ) + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        field_simp
      have hpos : 0 ≤ 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
        rw [e]; apply div_nonneg _ (by positivity); nlinarith
      rw [abs_of_nonneg (by linarith [div_nonneg zero_le_one (show (0 : ℝ) ≤ (k + 1) * (k + 2) by positivity), show 0 ≤ 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) by positivity])]
      linarith
    · have hm : (k : ℝ) + 2 ≤ m + 1 := by exact_mod_cast (by omega : k + 2 ≤ m + 1)
      have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) hm
      have e : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
        field_simp; ring
      rw [abs_sub_comm, abs_of_nonneg (by linarith [show 0 ≤ 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) by positivity])]
      linarith

/-- The maps `π₁(a, D_{n+1}) → π₁(a, D_n)` have infinite fibres (`RamcovGX.tex:1414`): the paths
`γ * ω * x_n^j * ω'` (`x_n` a small circle around `1/n`, the only point of `S` in
`D_n ∖ D_{n+1}`), `j ∈ ℤ`, all map to the class of `γ`, and are told apart by their winding
around `1/n` (`GX.argLift_freeHomotopic`). -/
theorem infinite_fiber_piOneUMap_fibD (a : ℂ) (k : ℕ) (cl : PiOneU fibS a (fibD k)) :
    Infinite (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {cl}) := by
  induction cl using Quotient.inductionOn with | h γ =>
  obtain ⟨hγ0, hγS, hγU⟩ := γ.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set r : ℝ := 1 / ((k : ℝ) + 1) with hr
  set c : ℂ := (r : ℂ)
  set ε : ℝ := r / (4 * ((k : ℝ) + 2)) with hεdef
  have hrpos : 0 < r := by positivity
  have hcS : c ∈ fibS := Or.inr ⟨k, rfl⟩
  have hε : 0 < ε := by positivity
  have hεr : ε < r / ((k : ℝ) + 2) := by
    rw [hεdef]; apply div_lt_div_of_pos_left hrpos (by positivity); linarith
  have hrε : r + ε < 1 / ((k : ℝ) + 1 / 2) := by
    rw [hεdef, hr, div_div, div_add_div _ _ (by positivity) (by positivity),
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcirc : ∀ j t, fibCircle c ε j t ∈ fibD k ∩ fibSᶜ := by
    intro j t
    have hn := norm_fibCircle_sub c hε j t
    refine ⟨?_, fun hS => ?_⟩
    · rw [fibD, Metric.mem_ball, dist_zero_right]
      calc ‖fibCircle c ε j t‖ = ‖c + (fibCircle c ε j t - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖fibCircle c ε j t - c‖ := norm_add_le _ _
        _ = r + ε := by rw [hn, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
        _ < _ := hrε
    · have hne : fibCircle c ε j t ≠ c := fun h => by
        rw [h, sub_self, norm_zero] at hn; linarith
      have := fibS_sep hS hne
      rw [hn] at this
      linarith
  have hp₀ : c + (ε : ℂ) ∈ fibD k ∩ fibSᶜ := by
    have := hcirc 0 0; rwa [Path.source] at this
  obtain ⟨Pe, hPe⟩ := (isPathConnected_fibD_diff k).joinedIn (γ.1 1) ⟨hγU, hγS 1⟩ _ hp₀
  obtain ⟨hq, hqS⟩ := fibQ_mem (k + 1)
  have hqk : fibQ (k + 1) ∈ fibD k := fibD_succ_subset k hq
  obtain ⟨Qp, hQp⟩ := (isPathConnected_fibD_diff k).joinedIn _ hp₀ (fibQ (k + 1)) ⟨hqk, hqS⟩
  let G : Path a (γ.1 1) := ⟨γ.1, hγ0, rfl⟩
  let ω : ℤ → Path (γ.1 1) (fibQ (k + 1)) := fun j => Pe.trans ((fibCircle c ε j).trans Qp)
  have hω : ∀ j t, ω j t ∈ fibD k ∩ fibSᶜ := fun j =>
    path_trans_mem hPe (path_trans_mem (hcirc j) hQp)
  have hGω : ∀ j t, (G.trans (ω j)) t ∈ fibSᶜ := fun j =>
    path_trans_mem (fun t => hγS t) (fun t => (hω j t).2)
  let γj : ℤ → FreePath fibS a (fibD (k + 1)) := fun j =>
    ⟨(G.trans (ω j)).toContinuousMap, (G.trans (ω j)).source, hGω j, by
      show (G.trans (ω j)) 1 ∈ _; rw [Path.target]; exact hq⟩
  let φ : ℤ → (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {Quotient.mk _ γ}) :=
    fun j => ⟨Quotient.mk _ (γj j), Quotient.sound
      (freeHomotopic_trans_tail G (fun t => hγS t) hγU (ω j) (hω j))⟩
  refine Infinite.of_injective φ fun j j' hjj => ?_
  have hfh : FreeHomotopic fibS a (fibD (k + 1)) (γj j).1 (γj j').1 :=
    Quotient.exact (congrArg Subtype.val hjj)
  have hUre : ∀ z ∈ fibD (k + 1), 0 < (c - z).re := fun z hz => by
    rw [fibD, Metric.mem_ball, dist_zero_right] at hz
    have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have h2 : 1 / (((k + 1 : ℕ) : ℝ) + 1 / 2) < r := by
      rw [hr]; push_cast; apply one_div_lt_one_div_of_lt (by positivity); linarith
    rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have avoid : ∀ {x y : ℂ} (P : Path x y), (∀ t, P t ∈ fibSᶜ) → ∀ t, P.toContinuousMap t ≠ c :=
    fun P hP t h => hP t (h ▸ hcS)
  obtain ⟨ΛG, hΛG⟩ := exists_argLift (avoid G fun t => hγS t)
  obtain ⟨ΛP, hΛP⟩ := exists_argLift (avoid Pe fun t => (hPe t).2)
  obtain ⟨ΛQ, hΛQ⟩ := exists_argLift (avoid Qp fun t => (hQp t).2)
  have key : ∀ j : ℤ, ∃ Λ, IsArgLift c (G.trans (ω j)) Λ ∧ Λ 1 - Λ 0 = (ΛG 1 - ΛG 0) +
      ((ΛP 1 - ΛP 0) + (j * (2 * Real.pi * Complex.I) + (ΛQ 1 - ΛQ 0))) := by
    intro j
    obtain ⟨Λ₁, h₁, e₁⟩ := (argLift_fibCircle c hε j).trans (Q := Qp) hΛQ
    obtain ⟨Λ₂, h₂, e₂⟩ := IsArgLift.trans (P := Pe) hΛP h₁
    obtain ⟨Λ₃, h₃, e₃⟩ := IsArgLift.trans (P := G) hΛG h₂
    refine ⟨Λ₃, h₃, ?_⟩
    rw [e₃, e₂, e₁]
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, add_zero]
    ring
  obtain ⟨Λ, hΛ, eΛ⟩ := key j
  obtain ⟨Λ', hΛ', eΛ'⟩ := key j'
  have hinv := argLift_freeHomotopic hcS hUre hfh hΛ hΛ'
  have h1 : (γj j).1 1 = (γj j').1 1 := by
    show (G.trans (ω j)) 1 = (G.trans (ω j')) 1
    rw [Path.target, Path.target]
  rw [h1, eΛ, eΛ'] at hinv
  have : ((j : ℂ) - j') * (2 * Real.pi * Complex.I) = 0 := by linear_combination hinv
  rcases mul_eq_zero.1 this with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exact absurd h Complex.two_pi_I_ne_zero

/-- The projective system `π₁(a, D_n)` (`RamcovGX.tex:1414`): countable sets, and maps
`π₁(a, D_{n+1}) → π₁(a, D_n)` with infinite fibres. -/
theorem fibS_tower (a : ℂ) (ha : a ∈ fibSᶜ) :
    Countable (PiOneU fibS a (fibD 0)) ∧ ∀ (k : ℕ) (c : PiOneU fibS a (fibD k)),
      Infinite (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {c}) ∧
        Countable (PiOneU fibS a (fibD (k + 1))) :=
  ⟨countable_piOneU_fibD a ha 0, fun k c =>
    ⟨infinite_fiber_piOneUMap_fibD a k c, countable_piOneU_fibD a ha (k + 1)⟩⟩

theorem nonempty_piOneU_fibD_zero (a : ℂ) (ha : a ∈ fibSᶜ) : Nonempty (PiOneU fibS a (fibD 0)) := by
  obtain ⟨hq, hqS⟩ := fibQ_mem 0
  obtain ⟨γ, hγ⟩ := isPathConnected_fibS_compl.joinedIn a ha (fibQ 0) hqS
  exact ⟨Quotient.mk _ ⟨γ.toContinuousMap, γ.source, hγ, by
    show γ 1 ∈ fibD 0
    rw [γ.target]; exact hq⟩⟩

/-- **`ex:consider_fiber_above_homeomorphic`** (`RamcovGX.tex:1409`). For `S = {1/n} ∪ {0} ⊆ ℂ` (skeletal, with `ℂ ∖ S`
semilocally simply connected), the fibre above `0` of the maximal covering `\widetilde Y^S`
possibly branched over `S` is homeomorphic to `ℤ^ℕ` with the product ("weak") topology, hence is not
locally compact. -/
theorem fiber_above_homeomorphic (y₀ : (fibSᶜ : Set ℂ)) :
    IsSkeletal fibS ∧ SemilocallySimplyConnected (fibSᶜ : Set ℂ) ∧
      Nonempty ((SpreadEnd.base : MaxBranchedCover fibS y₀ → ℂ) ⁻¹' {0} ≃ₜ (ℕ → ℤ)) ∧
      ¬ LocallyCompactSpace ((SpreadEnd.base : MaxBranchedCover fibS y₀ → ℂ) ⁻¹' {0}) := by
  set a : ℂ := (y₀ : ℂ)
  have ha : a ∈ fibSᶜ := y₀.2
  set 𝓤 : Set (Set ℂ) := range fibD
  obtain ⟨Φ, -, hemb, hrange⟩ := general_fiber_path_universal isSkeletal_fibS
    semilocallySimplyConnected_fibS y₀ ha (maxBase_base y₀) 𝓤
    (by rintro _ ⟨k, rfl⟩; exact isCNbhd_fibD k) fibD_basis
  -- the tower
  let A : ℕ → Type := fun k => PiOneU fibS a (fibD k)
  let f : ∀ k, A (k + 1) → A k := fun k => piOneUMap (fibD_succ_subset k)
  obtain ⟨hcount0, hfib⟩ := fibS_tower a ha
  haveI : Nonempty (A 0) := nonempty_piOneU_fibD_zero a ha
  haveI : Countable (A 0) := hcount0
  have hfib' : ∀ k (c : A k), Infinite (f k ⁻¹' {c}) ∧ Countable (f k ⁻¹' {c}) := fun k c =>
    ⟨(hfib k c).1, by haveI := (hfib k c).2; infer_instance⟩
  -- threads over `𝓤` versus threads over `ℕ`
  have chain : ∀ x ∈ TowerLim f, ∀ n m (h : n ≤ m),
      piOneUMap (S := fibS) (a := a) (fibD_subset_iff.2 h) (x m) = x n := by
    intro x hx n m h
    induction m, h using Nat.le_induction with
    | base => exact piOneUMap_self _ _
    | succ m hnm ih =>
      rw [← piOneUMap_piOneUMap (fibD_succ_subset m) (fibD_subset_iff.2 hnm)]
      show piOneUMap _ (f m (x (m + 1))) = _
      rw [hx m]; exact ih
  let ρ : (∀ U : 𝓤, PiOneU fibS a U) → ∀ k, A k := fun F k => F ⟨fibD k, mem_range_self k⟩
  let sec : (∀ k, A k) → ∀ U : 𝓤, PiOneU fibS a U := fun x U =>
    piOneUMap U.2.choose_spec.subset (x U.2.choose)
  have hsec : ∀ x ∈ TowerLim f, ∀ (U : 𝓤) (k : ℕ) (hk : fibD k ⊆ U), k ≤ U.2.choose →
      sec x U = piOneUMap hk (x k) := by
    intro x hx U k hk hle
    show piOneUMap _ (x U.2.choose) = _
    rw [← chain x hx k _ hle, piOneUMap_piOneUMap]
  have hidx : ∀ k : ℕ, (⟨fibD k, mem_range_self k⟩ : 𝓤).2.choose = k := fun k =>
    fibD_injective (⟨fibD k, mem_range_self k⟩ : 𝓤).2.choose_spec
  have hρmem : ∀ F ∈ range Φ, ρ F ∈ TowerLim f := by
    intro F hF k
    rw [hrange] at hF
    exact hF ⟨fibD (k + 1), mem_range_self _⟩ ⟨fibD k, mem_range_self _⟩ (fibD_succ_subset k)
  have hσmem : ∀ x ∈ TowerLim f, sec x ∈ range Φ := by
    intro x hx
    rw [hrange]
    intro U V h
    have hm := U.2.choose_spec
    have hn := V.2.choose_spec
    have hle : V.2.choose ≤ U.2.choose := fibD_subset_iff.1 (by rw [hm, hn]; exact h)
    show piOneUMap h (piOneUMap _ (x U.2.choose)) = piOneUMap _ (x V.2.choose)
    rw [piOneUMap_piOneUMap, ← chain x hx _ _ hle, piOneUMap_piOneUMap]
  have hρσ : ∀ x ∈ TowerLim f, ρ (sec x) = x := by
    intro x hx
    funext k
    show sec x ⟨fibD k, mem_range_self k⟩ = x k
    rw [hsec x hx _ k subset_rfl (by rw [hidx]), piOneUMap_self]
  have hσρ : ∀ F ∈ range Φ, sec (ρ F) = F := by
    intro F hF
    have hF' := hF
    rw [hrange] at hF'
    funext U
    exact hF' ⟨fibD U.2.choose, mem_range_self _⟩ U U.2.choose_spec.subset
  let Θ : range Φ ≃ₜ TowerLim f :=
    { toFun := fun F => ⟨ρ F.1, hρmem F.1 F.2⟩
      invFun := fun x => ⟨sec x.1, hσmem x.1 x.2⟩
      left_inv := fun F => Subtype.ext (hσρ F.1 F.2)
      right_inv := fun x => Subtype.ext (hρσ x.1 x.2)
      continuous_toFun := (continuous_pi fun k =>
        (continuous_apply (⟨fibD k, mem_range_self k⟩ : 𝓤)).comp
          (continuous_subtype_val (p := (· ∈ range Φ)))).subtype_mk _
      continuous_invFun := (continuous_pi fun (U : 𝓤) =>
        (continuous_of_discreteTopology (f := piOneUMap (S := fibS) (a := a)
          U.2.choose_spec.subset)).comp ((continuous_apply U.2.choose).comp
            (continuous_subtype_val (p := (· ∈ TowerLim f))))).subtype_mk _ }
  let ζ : (ℕ → ℕ) ≃ₜ (ℕ → ℤ) :=
    Homeomorph.piCongrRight fun _ => Equiv.intEquivNat.symm.toHomeomorphOfDiscrete
  let Ψ := hemb.toHomeomorph.trans (Θ.trans ((towerHomeomorph f hfib').trans
    ((prodNatPiHomeomorph (A 0)).trans ζ)))
  refine ⟨isSkeletal_fibS, semilocallySimplyConnected_fibS, ⟨Ψ⟩, fun h => ?_⟩
  haveI := h
  haveI : LocallyCompactSpace (ℕ → ℤ) := Ψ.symm.isOpenEmbedding.locallyCompactSpace
  exact not_locallyCompactSpace_nat_pi (α := ℤ) inferInstance

end FiberExample

end GX
