import Causal.Model.Cone
import Causal.Minkowski

/-!
# The massive-particle model spaces `E_α = ℝ × C_α`, `α > 0`

No label is marked: every label below also covers `κ = 0`, the extreme BTZ model `E_0`, which
the paper does not construct (its printed metric, `ETT.tex:1330`, makes the singular line
timelike; finding of an earlier wave). For `α > 0` each is proved in full, with no `sorry`:

`defi:causal_Ealpha` — `ETT.tex:1335` (the causality, and the singular line timelike and
locally chronal); `rem:btz_pas_tarentin` — `ETT.tex:1358` (the `α > 0` half);
`rem:sing_tarentin` — `ETT.tex:1364` (the model `E_α`, not `E_{≥0}`-manifolds);
`rem:pushup` — `ETT.tex:1374`; `cor:model_minimal` — `ETT.tex:1386`;
`lem:IJ_calc` — `ETT.tex:1441`; `lem:densite_modele` — `ETT.tex:1464` ((a)(b), and in causally
convex open subsets).

> For $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$. [...] For $\alpha>0$ the singular line is timelike, hence locally chronal.
> (`defi:causal_Ealpha`)

> Every point of a $\mass{\geq 0}$-manifold is strongly tarentin in the future, and the points
> which fail to be strongly tarentin in the past are exactly the BTZ points
> (`rem:btz_pas_tarentin`). Every $\mass{\geq0}$-manifold is a tarentin topological spacetime.
> (`rem:sing_tarentin`)

> For every $\kappa\geq 0$ the causality of $\mass{\kappa}$ is absolutely minimal.
> (`cor:model_minimal`)

> For every $\kappa\geq 0$ and every $p\in \mass{\kappa}$,
> $\ring J^\pm(p)\cap Z^\mp(\mass{\kappa})=I^\pm(p).$ (`lem:IJ_calc`)

> (a) $J^+(p)=\overline{I^+(p)}$; (b) $J^-(p)=\overline{I^-(p)}$ if $\kappa>0$ [...] The same
> holds in any causally convex open subset of $\mass{\kappa}$, with $J^\pm$ and $I^\pm$ taken in
> that subset. (`lem:densite_modele`)

## What is proved

`E_α := ℝ × C_α` (`Massive`), the static spacetime over the flat cone of
`Causal.Model.Cone`, with `massive α := staticCausality (Cone α)`: `x ≤_U y` iff a
future causal curve (the graph of a 1-Lipschitz map into `C_α`) joins them in `U`. Every theorem
of `Causal.Static` applies (`C_α` is a proper geodesic space): causal, causally
arc-connected, absolutely minimal, push-up in every open set, tarentin with `Z^± = E_α`, strongly
causal, globally hyperbolic; `Int J^±(p) ∩ Z^∓ = I^±(p)`; `J^±(p) = closure I^±(p)`, also in
causally convex open sets. The singular line `{r = 0}` is a chronal curve in every open set
containing it, and its points are chronologically related (`singLine_lt`,
`singLine_locallyChronal`). **`E_{2π} ≅ E^{1,2}`** (`massiveTwoPi_iso`): `C_{2π} ≅ ℝ²` gives a
bijection which is a strong morphism (DEC-10) both ways; strong morphisms transport along any
isometry of space (`staticCausality.strongMorphism_of_isometryEquiv`).

## Hypothesis checklist

| paper | here |
|---|---|
| `κ ≥ 0` | ⚠ `α > 0` only: `E_0` is not constructed (no label marked) |
| `E_{≥0}`-manifolds (`rem:btz_pas_tarentin`, `rem:sing_tarentin`) | the model spaces `E_α` only; manifolds are the `(G,X)` machinery (`Causal.GXStructure`) |
| `lem:densite_modele` (b) for `κ > 0` | ✓; the proof's "J^±(p) is the closure of its interior" (cited) is not used |

## SCOPE (disclosed)

* **Causal curves across the singular line.** The paper defines `≤_U` by future causal curves
  (`ETT.tex:1337`) and does not say what such a curve is where it meets `{r = 0}`. Read, as in
  `Causal.Static`: the graph over the time axis of a 1-Lipschitz map into `C_α` for its
  metric; chronological curves are `c`-Lipschitz for one `c < 1` (Static's SCOPE: the same `≪_U`
  as "speed `< 1` at every point"). In the regular part this is the causal cone of
  `−dt² + dr² + r²dθ²`.
* `C_α` is defined by its distance formula, argued equal to the length metric of
  `dr² + r² dθ²` in `Causal.Model.Cone`'s SCOPE.
* "On any `E_{≥0}`-manifold there is then a unique causal structure inducing that of `E_α` in
  every chart" (`ETT.tex:1339`) is the `(G,X)` part, not addressed here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Metric

/-! ### Transport along an isometry -/

section Transport

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A static curve is carried by a distance-preserving map of space. -/
theorem StaticCurve.map {f : X → Y} (hf : ∀ x y, dist (f x) (f y) = dist x y) {L : ℝ}
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hU : MapsTo (Prod.map id f) U U') {γ : ℝ → X} {a b : ℝ}
    (h : StaticCurve L U γ a b) : StaticCurve L U' (f ∘ γ) a b :=
  ⟨fun τ hτ τ' hτ' => by simp only [Function.comp, hf]; exact h.lip τ hτ τ' hτ',
    fun τ hτ => hU (h.mem τ hτ)⟩

theorem staticLe.map {f : X → Y} (hf : ∀ x y, dist (f x) (f y) = dist x y)
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hU : MapsTo (Prod.map id f) U U') {p q : ℝ × X}
    (h : staticLe U p q) : staticLe U' (Prod.map id f p) (Prod.map id f q) := by
  obtain ⟨h1, γ, hp, hq, hγ⟩ := h
  exact ⟨h1, f ∘ γ, by simp [hp], by simp [hq], hγ.map hf hU⟩

theorem staticLt.map {f : X → Y} (hf : ∀ x y, dist (f x) (f y) = dist x y)
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hU : MapsTo (Prod.map id f) U U') {p q : ℝ × X}
    (h : staticLt U p q) : staticLt U' (Prod.map id f p) (Prod.map id f q) := by
  obtain ⟨h1, L, hL, γ, hp, hq, hγ⟩ := h
  exact ⟨h1, L, hL, f ∘ γ, by simp [hp], by simp [hq], hγ.map hf hU⟩

variable [GeodesicSpace X] [GeodesicSpace Y]

/-- **An isometry of space is a strong morphism of the static spacetimes** (DEC-10). -/
theorem staticCausality.strongMorphism_of_isometryEquiv (e : X ≃ᵢ Y) :
    StrongMorphism (staticCausality X) (staticCausality Y) (Prod.map id e) where
  continuous := continuous_id.prodMap e.continuous
  isOpenMap := IsOpenMap.id.prodMap e.toHomeomorph.isOpenMap
  map_le U V hV _ _ h := staticLe.map e.dist_eq (fun z hz => by
    have : z ∈ (V : Set (ℝ × X)) := hz
    rw [hV] at this; exact this) h
  map_lt U V hV _ _ h := staticLt.map e.dist_eq (fun z hz => by
    have : z ∈ (V : Set (ℝ × X)) := hz
    rw [hV] at this; exact this) h

end Transport

/-! ### The model space `E_α` -/

/-- **`E_α`**, `α > 0`: the static spacetime `ℝ × C_α` over the flat cone of angle `α`, the
metric `−dt² + dr² + r² dθ²` (`ETT.tex:1327`). -/
abbrev Massive (α : ℝ) : Type := ℝ × Cone α

/-- **The causality of `E_α`** (`defi:causal_Ealpha`): `x ≤_U y` (resp. `x ≪_U y`) iff a future
causal (resp. chronological) curve joins them in `U`. -/
noncomputable abbrev massive (α : ℝ) [Fact (0 < α)] : Causality (Massive α) :=
  staticCausality (Cone α)

variable {α : ℝ} [Fact (0 < α)] {p q : Massive α}

theorem massive_le_top_iff : (massive α).le ⊤ p q ↔ dist p.2 q.2 ≤ q.1 - p.1 :=
  staticCausality.le_top_iff

theorem massive_lt_top_iff : (massive α).lt ⊤ p q ↔ dist p.2 q.2 < q.1 - p.1 :=
  staticCausality.lt_top_iff

/-- **The singular line** `sing(E_α) = {r = 0}`. -/
def singLine (α : ℝ) : Set (Massive α) := {p | p.2 = Cone.apex}

/-- The regular part `reg(E_α)`, its complement. -/
def regPart (α : ℝ) : Set (Massive α) := (singLine α)ᶜ

/-- The singular line is the graph of a constant map: a chronal curve of `Causal.Curves` in
every open set containing it. -/
theorem singLine_chronalCurveOn {W : Opens (Massive α)} {a b : ℝ}
    (h : ∀ τ ∈ Icc a b, ((τ, Cone.apex) : Massive α) ∈ W) :
    (massive α).ChronalCurveOn W (fun τ => (τ, (Cone.apex : Cone α))) a b :=
  staticCausality.chronalCurveOn_graph (L := 0) zero_lt_one
    ⟨fun _ _ _ _ => by simp, h⟩

/-- **The singular line is timelike** (`defi:causal_Ealpha`, `α > 0`). -/
theorem singLine_lt {t t' : ℝ} (h : t < t') :
    (massive α).lt ⊤ ((t, Cone.apex) : Massive α) (t', Cone.apex) := by
  rw [massive_lt_top_iff]; simpa using h

/-- **The singular line is locally chronal** (`defi:causal_Ealpha`, `α > 0`): around each of its
points, in every open set, it is a chronal curve, and its points are chronologically related in
that open set. -/
theorem singLine_locallyChronal {W : Opens (Massive α)} {t : ℝ}
    (ht : ((t, Cone.apex) : Massive α) ∈ W) :
    ∃ ε > 0, (massive α).ChronalCurveOn W (fun τ => (τ, (Cone.apex : Cone α))) (t - ε) (t + ε) ∧
      ∀ s ∈ Icc (t - ε) (t + ε), ∀ s' ∈ Icc (t - ε) (t + ε), s < s' →
        (massive α).lt W ((s, Cone.apex) : Massive α) (s', Cone.apex) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 W.isOpen _ ht
  have hmem : ∀ τ ∈ Icc (t - ρ / 2) (t + ρ / 2), ((τ, Cone.apex) : Massive α) ∈ W := by
    intro τ hτ
    refine hball ?_
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
    rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
  refine ⟨ρ / 2, by linarith, singLine_chronalCurveOn hmem, fun s hs s' hs' hss => ?_⟩
  exact ⟨hss, 0, zero_lt_one, fun _ => Cone.apex, rfl, rfl,
    ⟨fun _ _ _ _ => by simp, fun τ hτ => hmem τ ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩⟩

/-! ### The properties of `Static.lean`, instantiated -/

/-- `defi:causal_Ealpha`: `I^±_U(A)` is open. -/
theorem massive_isOpen_I (U : Opens (Massive α)) (A : Set (Massive α)) :
    IsOpen ((massive α).Iplus U A) ∧ IsOpen ((massive α).Iminus U A) :=
  ⟨(massive α).isOpen_Iplus, (massive α).isOpen_Iminus⟩

theorem massive_isCausal : (massive α).IsCausal := staticCausality.isCausal

/-- `cor:model_minimal`'s premise: `E_α` is causally arc-connected. -/
theorem massive_causallyArcConnected : (massive α).CausallyArcConnected :=
  staticCausality.causallyArcConnected

/-- `cor:model_minimal` for `α > 0`: the causality of `E_α` is absolutely minimal. -/
theorem massive_absolutelyMinimal : (massive α).AbsolutelyMinimal :=
  staticCausality.absolutelyMinimal

/-- `rem:pushup` for `E_α`: push-up in every open set. -/
theorem massive_pushUp : (massive α).PushUp := staticCausality.pushUp

theorem massive_pushUpOn (W : Opens (Massive α)) : (massive α).PushUpOn W :=
  staticCausality.pushUpOn W

/-- `rem:btz_pas_tarentin`, `α > 0`: every point is strongly tarentin in the future. -/
theorem massive_Zplus : (massive α).Zplus = univ := staticCausality.Zplus_eq

/-- `rem:btz_pas_tarentin`, `α > 0`: every point is strongly tarentin in the past. -/
theorem massive_Zminus : (massive α).Zminus = univ := staticCausality.Zminus_eq

/-- `rem:sing_tarentin` for the model space `E_α`. -/
theorem massive_tarentin : (massive α).Tarentin := staticCausality.tarentin

theorem massive_stronglyCausal : (massive α).StronglyCausal := staticCausality.stronglyCausal

theorem massive_globallyHyperbolic : (massive α).GloballyHyperbolic :=
  staticCausality.globallyHyperbolic

/-- `lem:IJ_calc` for `α > 0`: `Int J^±(p) ∩ Z^∓ = I^±(p)`. -/
theorem massive_IJ_calc (p : Massive α) :
    interior ((massive α).Jplus ⊤ {p}) ∩ (massive α).Zminus = (massive α).Iplus ⊤ {p} ∧
      interior ((massive α).Jminus ⊤ {p}) ∩ (massive α).Zplus = (massive α).Iminus ⊤ {p} :=
  ⟨staticCausality.interior_Jplus_inter_Zminus p, staticCausality.interior_Jminus_inter_Zplus p⟩

/-- `lem:densite_modele` (a)(b) for `α > 0`. -/
theorem massive_densite (p : Massive α) :
    (massive α).Jplus ⊤ {p} = closure ((massive α).Iplus ⊤ {p}) ∧
      (massive α).Jminus ⊤ {p} = closure ((massive α).Iminus ⊤ {p}) :=
  ⟨(staticCausality.closure_Iplus p).symm, (staticCausality.closure_Iminus p).symm⟩

/-- `lem:densite_modele` (a)(b), `α > 0`, in a causally convex open subset `V`: `J^±_V(p)` is
the closure of `I^±_V(p)` in `V`. -/
theorem massive_densite_of_causallyConvexIn {V : Opens (Massive α)}
    (hV : (massive α).CausallyConvexIn (V : Set (Massive α)) ⊤) (hp : p ∈ V) :
    (massive α).Jplus V {p} = closure ((massive α).Iplus V {p}) ∩ V ∧
      (massive α).Jminus V {p} = closure ((massive α).Iminus V {p}) ∩ V :=
  ⟨staticCausality.Jplus_eq_closure_Iplus_of_causallyConvexIn hV hp,
    staticCausality.Jminus_eq_closure_Iminus_of_causallyConvexIn hV hp⟩

/-! ### `E_{2π}` is Minkowski space -/

instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The identification `E_{2π} → E^{1,2}`, `(t, x) ↦ (t, x)` through `C_{2π} ≅ ℝ²`. -/
noncomputable def massiveTwoPiToMinkowski : Massive (2 * Real.pi) → Minkowski 2 :=
  Prod.map id Cone.coneTwoPiIsoEuclidean

/-- **`E_{2π} = E^{1,2}`** (`ETT.tex:1328`): the identification is a bijective strong morphism
whose inverse is a strong morphism, i.e. an isomorphism of topological spacetimes. -/
theorem massiveTwoPi_iso :
    Function.Bijective massiveTwoPiToMinkowski ∧
      StrongMorphism (massive (2 * Real.pi)) (minkowski 2) massiveTwoPiToMinkowski ∧
      StrongMorphism (minkowski 2) (massive (2 * Real.pi))
        (Prod.map id Cone.coneTwoPiIsoEuclidean.symm) ∧
      Function.LeftInverse (Prod.map id Cone.coneTwoPiIsoEuclidean.symm) massiveTwoPiToMinkowski ∧
      Function.RightInverse (Prod.map id Cone.coneTwoPiIsoEuclidean.symm)
        massiveTwoPiToMinkowski := by
  have hl : Function.LeftInverse (Prod.map id Cone.coneTwoPiIsoEuclidean.symm)
      massiveTwoPiToMinkowski := fun x =>
    Prod.ext rfl (Cone.coneTwoPiIsoEuclidean.symm_apply_apply x.2)
  have hr : Function.RightInverse (Prod.map id Cone.coneTwoPiIsoEuclidean.symm)
      massiveTwoPiToMinkowski := fun x =>
    Prod.ext rfl (Cone.coneTwoPiIsoEuclidean.apply_symm_apply x.2)
  exact ⟨⟨hl.injective, hr.surjective⟩,
    staticCausality.strongMorphism_of_isometryEquiv Cone.coneTwoPiIsoEuclidean,
    staticCausality.strongMorphism_of_isometryEquiv Cone.coneTwoPiIsoEuclidean.symm, hl, hr⟩

end Causal
