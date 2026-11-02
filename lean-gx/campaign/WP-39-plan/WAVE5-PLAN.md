# gx wave 5 — Section 4 (uniformization of BTZ-manifolds): dispatch plan

Drafted 2026-11-02 by a read-only planning agent against hub 78dc3d4 (lean-causal CBG graduated at 259242f);
saved by the master session. Rulings Q1–Q7 below are put to the author before dispatch.

## Packages (all scaffold first, `lean-gx/scaffold/GXScaffold/`)
- WP-39a Lorentz/Bridge (M): (ℝ³,nullQ) ≃ Causal.Minkowski 2; NullIsom0 ≃* Causal.Flat.isom 2; GX.IsRigidAction from
  isAnalyticAction_isom; gxGroupoid bridge; universal cover bridge; developing_theorem → Causal.Flat.IsDevelopingPair.
- WP-39b BTZ/Model (L): E₀ (white hole GX.btz_whitehole_isom0 transported), Sing/Reg, D(BTZ̃)=J⁺(Δ), parabolic holonomy,
  T_BTZ; prop:BTZ_virt_tame (l.2252).
- WP-39c BTZ/Rigid (L): LocalModel fields rigid (lem:liouville), localUnique_sing (B21 prop:isom_strong via E₀,∞ normaliser),
  localUnique_sing_adherent (θ-loop holonomy), localUnique_reg, regularChart, sing_mem, typeAgreement, isOpen/dense_regY, t2Y.
- WP-39d BTZ/VirtTame (M): ex:follows_proposition_brunswic_cauchy (l.1927), prop:BTZ_manifold_virt_tame (l.2262),
  prop:manifold_admits_galoisian_maximal (l.2308) via isVirtuallyTame_of_descending.
- WP-39e BTZ/Causality (L): causality on 𝕄 ⊕ E₀ from causal curves (DEC-33); f=τ−r/2, h=τ+r monotone; I⁺(p) local form;
  Iminus_eq_empty, past_local, Iplus_of_lt; J^±(V) open incl. BTZ; absolutelyMinimalOn_Y, chartIso_mem, coneSliceFuture,
  coneSlicePast (BTZ: K = J⁺_O(y) ∩ {τ+r=c}).
- WP-39f BTZ/LocalModel (XL): assemble 𝔐E₀; global fields singularFlatAxioms, timeFunction (via strict `geroch_sing_i_imp_ii` after DEC-78's split:
  gx supplies SingularFlatAxioms + ModelMeasures on E₀-manifolds), curvesExtend, isCompact_* (Flat/CBGCompact templates), secondCountable_of_cauchy (countably many lines).
- WP-39g BTZ/CBG (L): hA3f (lem:passe_pgcd), hA3p, hA4f (Sbierski τ_q, Lemma 3.11); Geometry.ofLocalModelOfBTZ; cbg for E₀.
- WP-39h BTZ/Topology (M): defi:BTZtop (l.2281), prop:quotient_chart (l.2286), rem:tamifying_topology_generated_open (l.2293).
- WP-39i BTZ/Spear (L): B21 Lemma 2.3 (gluedChartedSpace), Lemma 2.4, full future BTZ rays.
- WP-39j BTZ/Surgery (L): B21 Lemmas 2.6(ii)–2.8, Cor 2.11; Σ* Cauchy in Reg M, IsCauchyComplete.
- WP-39k BTZ/AbsMax (L): Prop 2.16 via lemma K (isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp), Lemmas 2.12–2.15,
  Prop 2.17, Cor 2.18 ⇒ AbsMax (fun _ => True) RegM.
- WP-39l BTZ/Manifolds (M–L): l.2317–2359 defs and lemmas, lem:increasing_map (∀ x y ∈ M̃).
- WP-39m BTZ/Holonomy (M/L): Reg M as FlatSpacetime; a loxodromic in ρ(π₁ Reg M) (Q2); ρ faithful, discrete, torsion-free.
- WP-39n BTZ/Uniformization (L): prop:globally_hyperbolic_cauchy_complete_manifolds (corrected, counterexample {τ<0}),
  theo:globally_hyperbolic_cauchy_complete_cauchy_maximal (DEC-28) from uniformization + equality_of_absMax.
Order: a; b; c,e,h; d,f; g; i,l; j,m; k; n. Critical path f→g→i→j→k→n.

## Lakefile and build discipline
Preferred: git-pinned dependency (clone in lean-gx/.lake/packages/Causal; no interference with the Barbot session's builds):
  [[require]] name = "Causal", git = "/home/maxbrain/Dropbox/LeanArticles", rev = <pinned sha>, subDir = "lean-causal"
`lake update Causal` only; check mathlib rev unchanged. Import gate in make check: `import Causal.` only in
{GX,scaffold/GXScaffold}/{BTZ,Lorentz}/; never the root, never CausalScaffold.*; no `open Causal GX`.

## Risks (from the planner)
timeFunction on every GH E₀-manifold (SingularGeroch is scaffold; flatGerochGH regular-only); SliceFutureBTZ has no cone slice
at BTZ points; bridges may not be definitional; AbsMax over Type 0; Models scaffold blocks strict graduation of §4.
Defects: D-11 (future_complete false; {τ<0}), D-12(a)–(f), D-1/2/5/6/8/10, "Lemma 2.4" → 2.3, ex l.1927 includes θ=2π
(E_{2π} regular; B21 Prop 1.3 assumes α ≠ 2π).

## Rulings: DEC-74 (E_θ family, θ ≠ 2π, massive cones), DEC-75 (loxodromic proved in 2+1), DEC-76 (π₁(Σ∖sing) non-abelian, s ≥ 1), DEC-77 (readings: no time reversal; M̃ with T_BTZ; Cauchy-maximal = IsETTMaximal; corrected future_complete); DEC-78 (Barbot side: SingularGeroch split).
WP-39d grows to cover the massive cones E_α (DEC-74); WP-39m proves the loxodromic (DEC-75).
