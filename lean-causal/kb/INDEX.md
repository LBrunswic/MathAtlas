# Knowledge base — working in `lean-causal`

What working in this library is like: conventions, patterns, pitfalls. Read before you start;
propose an entry when you finish, if you learned something the next session would otherwise
rediscover. One fact per entry.

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-open-sets-not-subtypes.md) | convention | Everything is indexed by an open set; no subtype of `M` in a statement |
| [0002](entries/0002-past-from-future-dual.md) | pattern | Prove the future statement, get the past one from `C.dual` |
| [0003](entries/0003-induction-generalizes-hypotheses.md) | pitfall | `induction h` on `TransGen` rewrites every hypothesis mentioning the endpoint |
| [0004](entries/0004-names-at-this-pin.md) | pitfall | Deprecated and renamed lemmas at mathlib `fabf563a`; a deprecation is a build failure |
| [0005](entries/0005-build-your-own-module.md) | house-rule | Iterate with `lake env lean`, build only your own module |
| [0006](entries/0006-docstring-contract.md) | house-rule | The module docstring is a contract, and the ledger reads its first 4000 characters |
| [0007](entries/0007-neighbourhoods-not-sequences.md) | pattern | Second countability is almost never needed: argue on neighbourhoods and directed families |
| [0008](entries/0008-opens-inf-membership.md) | pattern | Membership in `V ⊓ W` and transport along `≤` of open sets |
| [0009](entries/0009-subdivision.md) | pattern | The Lebesgue-number step is `exists_subdivision_Icc` |
| [0010](entries/0010-dot-notation-on-unfolded-props.md) | pitfall | `h.foo` fails when the type of `h` unfolds to a `∀` |
| [0011](entries/0011-never-outrun-the-paper.md) | house-rule | A Lean statement narrower than the paper's is never its certificate |
| [0012](entries/0012-model-facts-as-hypotheses.md) | pattern | The singular part's model facts are named hypotheses, witnessed on a line |
| [0013](entries/0013-measures-on-open-sets.md) | convention | A measure on an open `U` is a measure on `M` with `μ Uᶜ = 0` |
| [0014](entries/0014-no-gluing-axiom.md) | pitfall | No gluing axiom: a counterexample may exploit it, and must say so |
| [0015](entries/0015-graduation-checklist.md) | house-rule | Graduating a scaffold file: what the gates do not catch by themselves |
| [0016](entries/0016-namespace-shadowing.md) | pitfall | Names that resolve to the wrong lemma inside `namespace Causality` |
| [0017](entries/0017-curves-over-intervals.md) | pattern | Curves over an interval, inextensibility, and the two traps of "maximal under extension" |
| [0018](entries/0018-charts-and-maximal-atlases.md) | pattern | Causalities through charts: transport, `ChartIso`, the maximal atlas |
| [0019](entries/0019-discrete-counterexamples.md) | pitfall | A discrete counterexample is non-local, and says nothing about local causalities |
| [0020](entries/0020-static-spacetimes.md) | pattern | Model spaces are static spacetimes over a geodesic space; cheap local counterexamples |
| [0021](entries/0021-metric-from-a-formula.md) | pattern | A space given by a distance formula with identifications: `SeparationQuotient` |
| [0022](entries/0022-rulings-and-printed-forms.md) | house-rule | After a ruling, the strengthened theorem is principal and the printed form becomes a `Prop` |
| [0023](entries/0023-maximal-chains-of-the-order.md) | pattern | Maximal chains of the causal order, and abstract Section 4 |
| [0024](entries/0024-two-papers-one-library.md) | house-rule | Two papers in one library: Barbot labels are `bthm:`/`bprop:`/…, modules under `Flat/` |
| [0025](entries/0025-scaffold-root-and-axiom-sweep.md) | pitfall | A scaffold module not imported by the scaffold root is invisible to the axiom sweep |
| [0026](entries/0026-ett-section4-on-cbg.md) | pattern | ETT §4 is stated through the CBG library, via `CommonSubDev` |
| [0027](entries/0027-chart-iso-transport.md) | pattern | Transport curves, causal arc-connectedness and push-up through a `ChartIso` |
| [0028](entries/0028-minkowski-facts-under-flat.md) | pitfall | Minkowski facts may already exist under `Causal.Flat`: grep `Flat/` first |
| [0029](entries/0029-btz-points-and-plainness.md) | pitfall | A BTZ point never witnesses a failure of causal plainness |
| [0030](entries/0030-causal-relations-need-not-be-closed.md) | pitfall | A causal relation need not be closed, even locally: test against `chronoMinkowski` |
| [0031](entries/0031-limit-adjoining-with-le.md) | pattern | Adjoining a curve's limit point needs only `p ≤ c t`: the `*_of_le` lemmas |
| [0032](entries/0032-closed-le-gives-strict-function.md) | pattern | With `≤` closed, an admissible past measure gives a strictly increasing continuous function |
| [0033](entries/0033-e0-model.md) | pattern | E₀ is `Causal.E0 = ℝ × ℂ`, with its `BTZAxioms` instance `E0.btzAxioms` |
| [0034](entries/0034-typecheck-module-chains.md) | pattern | Typechecking a chain of new scaffold modules without `lake build` |
| [0035](entries/0035-verbatim-ports.md) | pattern | A gx → Causal port compiles verbatim; check it by a line-set comparison |
| [0036](entries/0036-non-borel-real.md) | pattern | A subset of ℝ that is not Borel: `exists_not_measurableSet_real` |
| [0037](entries/0037-spokes-local-counterexample.md) | pattern | A cheap local counterexample with ≤ neither closed nor plain: spokes in an achronal slice |
| [0038](entries/0038-non-local-relations-and-curves.md) | pitfall | Non-local relations leave causal curves, inextensibility and Cauchy surfaces unchanged |
| [0039](entries/0039-isrigid-satisfiable.md) | pitfall | The causal `IsRigid` is satisfiable on a connected, non-trivial base |
| [0040](entries/0040-equivalent-is-directional.md) | pitfall | `CommonSubExtension.Equivalent` is directional: fix the reading before refuting uniqueness |
| [0041](entries/0041-plain-minimal-pushup.md) | pitfall | Plainness plus absolute minimality on a T1 space gives push-up: no local witness otherwise |
| [0042](entries/0042-cheap-open-relation-on-R.md) | pattern | A cheap open transitive relation on ℝ from two semicontinuous functions |
| [0043](entries/0043-corresponding-boundary-points.md) | pitfall | Corresponding boundary points in layer 1 are `Gluing.IsCorrespondingBoundaryPair`, not `CBG.Corresponds` |
| [0044](entries/0044-gluing-closedness-not-topology.md) | pitfall | Closed H, open C and a unique corresponding point are not topology |
| [0045](entries/0045-inextensibility-not-monotone-under-nesting.md) | pitfall | Inextensibility is not monotone under nesting |
| [0046](entries/0046-cutline-counterexample.md) | pattern | A cheap local counterexample for nesting questions: the cut line |
| [0047](entries/0047-model-free-lemmas-stranded.md) | pitfall | Model-free lemmas once stranded in model-importing modules: now in the ETT layer |
| [0048](entries/0048-causal-ladder-tactic.md) | pattern | The `causal_ladder` tactic, and regenerating its rules |
| [0049](entries/0049-locating-an-extension.md) | pattern | Locating an extension is a characterisation, and needs a chronal neighbour |
| [0050](entries/0050-isolated-line.md) | pattern | A cheap plain, causally open, arc-connected line with a chronologically isolated point |
| [0051](entries/0051-closed-half-line.md) | pattern | A model-free BTZ-like point: the endpoint of the closed half-line |
| [0052](entries/0052-same-le-defeq.md) | pattern | Two causalities with the same ≤ share J, diamonds, causal openness and GH by defeq |
| [0053](entries/0053-named-side-conditions.md) | house-rule | State new theorems with the named ladder side conditions |
| [0054](entries/0054-ers-uniqueness-skeleton.md) | pattern | ERS Thm 4.64's causal skeleton, and the half of Step 2 that is not layer 1 |
| [0055](entries/0055-static-cylinder-removed.md) | pattern | Slices of static spacetimes are Cauchy; removing a reachable cylinder kills every Cauchy surface |
| [0056](entries/0056-withlp-cosmic-string.md) | pattern | Hörmann's 3+1 conical spacetime as a static causality on an L² product |
| [0057](entries/0057-causal-iso-is-chartiso.md) | pitfall | A causal isomorphism is a global ChartIso; transport lemmas and opensCongr |
| [0058](entries/0058-time-function-not-causal.md) | pitfall | An ETT time function does not make a causality causal; strict increase does |
| [0059](entries/0059-e0-singular-flat-witness.md) | pattern | E₀ is a SingularFlatAxioms witness with a BTZ point |
| [0060](entries/0060-generated-port.md) | pattern | Generate a gx → Causal port by line ranges, and check it as verbatim blocks |
| [0061](entries/0061-stranded-model-free-lemmas.md) | convention | Model-free lemmas stranded under Causal.E0 / Causal.E0LM: hoist on demand |
| [0062](entries/0062-corresponding-toolkit.md) | pattern | The model-free corresponding-point toolkit is in the ETT layer |
| [0063](entries/0063-verbatim-hoist-check.md) | pattern | Checking a verbatim hoist: dump the environment before and after |
| [0064](entries/0064-causally-plain-of-locz.md) | pattern | Causal plainness from push-up and local Z±: causallyPlain_of_locZ; E₀ is causally plain |
| [0065](entries/0065-time-function-layer.md) | pattern | The time-function layer is in the ETT layer; HasTimeFunction and IsTimeFunction are incomparable |
| [0066](entries/0066-private-names-and-matchers-in-hoists.md) | pitfall | Hoisting renames private declarations; term-mode matches add auxiliary constants |
| [0067](entries/0067-gx-ae-atlases-ported.md) | pattern | gx's a.e. (G,X)-atlases are in lean-causal; Causal.IsComplete shadows mathlib's |
| [0068](entries/0068-port-type-check-and-omit.md) | pattern | Checking a gx → Causal port by elaborated types; omit changes types |
| [0069](entries/0069-rational-line.md) | pattern | The rational line: absolutely minimal, push-up, only constant causal curves |
| [0070](entries/0070-spacelike-line-not-tarentin.md) | pattern | The spacelike line is GH and not tarentin; transfers that read only ≤ need ≤ at M only |
| [0071](entries/0071-sbierski-prop-3-7-a3-free.md) | pattern | Sbierski Prop 3.7 (i) ⇒ (ii) without A3; (iii) fails at BTZ points |
| [0072](entries/0072-chronology-three-strengths.md) | pattern | Chronology at points comes in three strictly different strengths |
| [0073](entries/0073-jump-and-gated-lines.md) | pattern | Two cheap non-local separations: the jump line and the gated line |
| [0074](entries/0074-half-lit-line.md) | pattern | The half-lit line: an absolutely minimal witness for the DEC-8 gap, valid in either reading |
| [0075](entries/0075-pushup-of-minimal-local.md) | pattern | Local push-up gives push-up under absolute minimality on T1 spaces |
| [0076](entries/0076-chronal-diamond-tarentin.md) | pattern | Two-sided chronology near a point gives tarentin there: chronal_neighbours ⇒ tarentin |
| [0077](entries/0077-plain-of-pushup-chronal.md) | pattern | push_up ∧ chronal_neighbours ⇒ causally_plain; the plainness criterion is in the ETT layer |
| [0078](entries/0078-flat-time-cylinder.md) | pattern | The flat time cylinder: an absolutely minimal ETT spacetime with every local ladder property and ≪ total |
| [0079](entries/0079-rational-line-extras.md) | pattern | The rational line in the ladder: an either-reading witness against local causal openness |
| [0080](entries/0080-backward-ladder-call.md) | pattern | A ladder failure read backwards through a conjunctive edge is one causal_ladder call |
| [0081](entries/0081-lines-in-abstract-causality.md) | pattern | Straight lines in an abstract causality, and the slope-δ cone on ℝ × E |
| [0082](entries/0082-duplicate-theorem-across-modules.md) | pitfall | A theorem declared in two modules with the same type builds silently |
| [0083](entries/0083-narrowed-imports-change-proof-terms.md) | pitfall | Narrowing a moved declaration's imports can change its proof term |
| [0084](entries/0084-unions-of-local-developments.md) | pattern | Unions of local developments of pieces of S |
| [0085](entries/0085-theorem-4-64-in-a-region.md) | pattern | Theorem 4.64 in a region |
| [0086](entries/0086-ers-4-77-without-s-in-ui.md) | pitfall | ers_theorem_4_77 does not need S ⊆ Uᵢ |
| [0087](entries/0087-pde-developments-abstractly.md) | pattern | Developments of one PDE on a fixed background, abstractly |
| [0088](entries/0088-union-with-s-acausal.md) | pattern | A union of Cauchy open sets with S acausal in the union |
| [0089](entries/0089-ers-4-77-greatest-not-developments.md) | pitfall | ers_theorem_4_77_greatest is not the set of developments |
| [0090](entries/0090-halflit-dual.md) | pattern | The time-reversed half-lit line: an either-reading witness against causal openness in the future |
| [0091](entries/0091-time-reversed-witness.md) | pattern | A time-reversed witness: dual_* transport in haves, then causal_ladder on C.dual |
| [0092](entries/0092-one-way-membrane.md) | pattern | The one-way membrane: a planar ETT-layer causality without a model import |
| [0093](entries/0093-jplus-only-misses-jminus-step.md) | pitfall | J⁺-only causal openness does not carry the J⁻ step of prop:tarentin_topological_spacetime_causality's proof |
| [0094](entries/0094-maximal-by-zorn-without-rigidity.md) | pattern | Maximal developments by Zorn, without rigidity |
| [0095](entries/0095-universe-order-and-ladder-parser.md) | pitfall | Universe order, and tools/ladder.py's parser |
| [0096](entries/0096-directed-union-cauchy.md) | pattern | A directed union of Cauchy open sets |
| [0097](entries/0097-zorn-split-by-cofinality.md) | pattern | Zorn with chains split by cofinality |
| [0098](entries/0098-dec25-cac-pushup-uniqueness.md) | pattern | Over DEC-25 atlases, cac, push-up and uniqueness need neither hreg nor (b′) |
| [0099](entries/0099-isatlascausality-ulift.md) | pattern | IsAtlasCausality's index types: lift isomorphic charts with ULift |
| [0100](entries/0100-massa-model-family.md) | pattern | The E≥0 model family MassAModel and its facts |
| [0101](entries/0101-aechart-trans-two-lines.md) | pattern | IsAEChart composed with a maximal-atlas chart; ℝ ⊔ ℝ as a DEC-25 manifold |
| [0102](entries/0102-ealpha-regular-charts.md) | pattern | The regular charts of E_κ and hreg |
| [0103](entries/0103-static-isometric-chartiso.md) | pattern | Static spacetimes: an isometric chart of space times the identity of time is a ChartIso |
| [0104](entries/0104-cone-discs-sector-bound.md) | pitfall | Discs in flat sectors of the cone; the sector bound |
| [0105](entries/0105-rotations-time-axis.md) | pattern | Rotations of E^{1,2} about the time axis |
| [0106](entries/0106-e0-singular-gx.md) | pattern | E₀ as a singular (G,X)-manifold: E0GX.singularGX |
| [0107](entries/0107-e0-holonomy.md) | pattern | Two sector charts of E₀ differ by a holonomy power |
| [0108](entries/0108-maximal-atlas-chartiso-pitfall.md) | pitfall | Chart isomorphisms do not pass to the maximal a.e. atlas for free |
| [0109](entries/0109-locally-connected-product.md) | pitfall | Pitfall: LocallyConnectedSpace (X × Y) at this pin |
| [0110](entries/0110-seg-causality.md) | pattern | A cheap causality with empty chronology for (G,X)-counterexamples |
| [0111](entries/0111-chronology-on-polygonal-causality.md) | pattern | A chronology on a polygonal causality: a side condition closed in the start, open in the end |
| [0112](entries/0112-chronal-neighbours-without-pushup.md) | pattern | Chronal neighbours without push-up, in either reading: the chronal one-way membrane |
| [0113](entries/0113-arc-causality.md) | pattern | A causality carried by a family of arcs (arcCausality) |
| [0114](entries/0114-comb-coordinates.md) | pattern | Choose a planar comb's coordinates for the proof |
| [0115](entries/0115-gh-without-tarentin.md) | pitfall | Global hyperbolicity without tarentin: neither a time function nor strong causality |
| [0116](entries/0116-densite-at-e0-without-charts.md) | pattern | lem:densite_modele at E₀ needs no chart: push-up, Z⁺ = E₀ and the closed cones |
| [0117](entries/0117-e0-strongly-causal-open.md) | pitfall | E₀ is StronglyCausalOpen, but not through StronglyCausal.stronglyCausalOpen |
| [0118](entries/0118-sdiff-beside-inter-does-not-parse.md) | pitfall | `A ∩ B \ C` does not parse: write `(A ∩ B) \ C` |
| [0119](entries/0119-bprime-at-e0.md) | pattern | (b′) at E₀: every a.e. isomorphism chart E₀ ⇀ E₀ is a chart isomorphism |
| [0120](entries/0120-rigidity-without-covering.md) | pattern | Rigidity at a singular point without covering spaces: one slit box, the limit at the axis, continuity across the slit |
| [0121](entries/0121-det-of-explicit-linear-map.md) | pattern | The determinant of an explicit linear map of ℝ × ℝ × ℝ |
| [0122](entries/0122-reflection-witness-oq82.md) | pattern | The reflection θ ↦ −θ of E₀: a chart isomorphism that SO₀ excludes |
| [0123](entries/0123-ioo-mem-nhds-is-a-membership.md) | pitfall | `Ioo_mem_nhdsGT` is a set membership: state the `∀ᶠ` first |
| [0124](entries/0124-eventual-constancy-omega-one.md) | pattern | Eventual constancy on ω₁ and on well orders of uncountable cofinality |
| [0125](entries/0125-omega-one-and-clubs.md) | pattern | ω₁ and clubs at this Mathlib pin |
| [0126](entries/0126-ordinal-deprecations-sierpinski.md) | pitfall | Ordinal deprecations, Sierpiński space and T0Space Prop at this pin |
| [0127](entries/0127-absolute-minimality-by-rational-subdivision.md) | pattern | Absolute minimality without arc-connectedness, by rational subdivision |
| [0128](entries/0128-causal-openness-by-time-translation.md) | pattern | Causal openness of a polygonal causality without push-up, by time translation |
| [0129](entries/0129-notched-plane-closed-subspace.md) | pattern | A causality on a closed subspace of ℝ²: the notched plane |
| [0130](entries/0130-pushup-from-open-chronology.md) | pattern | Push-up on a polygonal causality from the openness of I±_U alone |
| [0131](entries/0131-plainness-via-dual-locz.md) | pattern | Causal plainness when the future chronology fails on a thin set: causallyPlain_of_locZ on C.dual |
| [0132](entries/0132-plain-not-open.md) | pattern | Causal plainness gives no causal openness, in either reading: the notched plane |
| [0133](entries/0133-chart-transfer-isochartscover.md) | pattern | Model facts pass through isomorphic charts: Causal.SFATransfer over IsoChartsCover |
| [0134](entries/0134-e0-manifolds-api.md) | pattern | E₀-manifolds with their natural causality: Causal.SFALocalE0 |
| [0135](entries/0135-chart-facts-vs-minimality.md) | pitfall | I⁻(p) = ∅ at a BTZ point is not a chart fact: it uses absolute minimality |
| [0136](entries/0136-sing-closed-skeletal-already-strict.md) | pitfall | isClosed_sing and interior_sing are already strict for every singular (G,X)-manifold |
| [0137](entries/0137-ealpha-singular-gx.md) | pattern | E_κ as a singular (G,X)-manifold: Causal.EAlphaGX.singularGX κ |
| [0138](entries/0138-continuation-ring-boxes.md) | pattern | Continuing a chart of E_κ around the line: disc charts on a small circle, no wide sector |
| [0139](entries/0139-kappa-two-pi-both-sides.md) | pattern | κ = 2π from both sides, with no case split on κ ∈ 2πℤ |
| [0140](entries/0140-faithful-action-group-equality.md) | pattern | A faithful action turns « acts as » into a group equality |
| [0141](entries/0141-portly-reg-without-homeomorphism.md) | pattern | reg(E_κ) is portly without a homeomorphism C_κ ≅ ℂ |
| [0142](entries/0142-curves-extend-theorem-second-countable.md) | pattern | CurvesExtend is a theorem on T1, second countable spaces |
| [0143](entries/0143-direct-limits-trimming-curves.md) | pattern | Direct limits and trimming of curves over intervals |
| [0144](entries/0144-transfinite-recursion-in-proof.md) | pattern | Transfinite recursion inside a proof, and dependent maps φ i j (h : r i j) |
| [0145](entries/0145-def-needs-open-classical.md) | pitfall | A def needs open Classical for dif_pos |
| [0146](entries/0146-null-frontiers-e0-without-charts.md) | pattern | Lebesgue-null frontiers at E₀ without charts: chronological rays, the shear, polar coordinates |
| [0147](entries/0147-tofinite-same-null-sets.md) | pattern | A finite measure with the null sets of an s-finite one: Measure.toFinite |
| [0148](entries/0148-property3-local-form.md) | pitfall | Property 3 of an admissible measure does not restrict to a causally convex open set by itself |
| [0149](entries/0149-model-measures-e0.md) | pattern | ModelMeasures with a BTZ point: Causal.E0.modelMeasures |
| [0150](entries/0150-pgrep-matches-itself.md) | pitfall | `pgrep -f "lake build"` matches the waiting shell itself |
| [0151](entries/0151-static-null-frontiers-admissible.md) | pattern | Null frontiers and admissible measures on any static ℝ × X |
| [0152](entries/0152-measures-at-ealpha.md) | pattern | Measures at E_κ: the Borel σ-algebra of Cone κ is declared once, in Causal.MeasuresEAlpha |
| [0153](entries/0153-polar-atom-at-apex.md) | pitfall | Pushing a measure by Cone.polar puts an atom at the apex |
| [0154](entries/0154-massa-model-family-instance.md) | pitfall | The E≥0 model family's singular structures: massAModelSingularGX, and when it does not fire |
| [0155](entries/0155-e0-axis-not-reached-from-ealpha.md) | pattern | No a.e. isomorphism chart joins E₀'s axis to an E_κ: a causal proof, no holonomy |
| [0156](entries/0156-bprime-at-ealpha.md) | pattern | (b′) at E_κ, κ > 0: Causal.BPrimeEAlpha.chartIso_of_isAEChart |
| [0157](entries/0157-slit-box-timelike-axis.md) | pattern | The slit box at a timelike axis: work in parameter space, recover the angle mod κ′ |
| [0158](entries/0158-static-shift-chartiso.md) | pattern | A time translation times a space isometry is a ChartIso of static spacetimes |
| [0159](entries/0159-e-models-bprime-assembly.md) | pattern | (b′) over the whole E≥0 family, and the three corollaries at every E≥0-manifold: Causal.EModelsBPrime |
| [0160](entries/0160-subfamily-natural-causality.md) | pattern | A sub-family's natural causality is the family's: use the uniqueness clause of massA_singular_all |
| [0161](entries/0161-sfa-local-every-manifold.md) | pattern | SingularFlatAxioms' chartwise fields at every E≥0-manifold: Causal.SFALocal |
| [0162](entries/0162-btz-point-charts-into-e0.md) | pattern | At a BTZ point every isomorphic chart is into E₀ |
| [0163](entries/0163-family-facts-by-match.md) | pitfall | Family-indexed model facts: pattern-match on o, and read Sing through a membership lemma |
| [0164](entries/0164-measures-through-charts.md) | pattern | Admissible measures through a chart isomorphism: choose the model's set first |
| [0165](entries/0165-chart-image-not-convex.md) | pitfall | U causally convex in M does not make its chart image causally convex in the model |
| [0166](entries/0166-family-measurable-instances.md) | pattern | The measurable structure of the E≥0 model family |
| [0167](entries/0167-translation-line-development.md) | pattern | Translation lines without a classification of 1-manifolds: Causal.LineDevelopment.exists_development |
| [0168](entries/0168-inextensible-from-the-ends.md) | pattern | Inextensibility from the ends, and locality of curves in the parameter |
| [0169](entries/0169-strictmono-onto-interval.md) | pattern | Every open interval containing 0 is the range of a strictly increasing φ : ℝ → ℝ with φ 0 = 0 |
| [0170](entries/0170-allrelated-witness.md) | pattern | A cheap non-causal witness on any space: allRelated |
| [0171](entries/0171-addcircle-at-this-pin.md) | pitfall | AddCircle at this pin: explicit periods, and CompactSpace needs AddCircle.Real |
| [0172](entries/0172-e0-ball-local-forms.md) | pattern | Inside a ball of E₀ centred on the axis, the ball's relations are E₀'s global ones |
| [0173](entries/0173-global-btz-one-chart.md) | pattern | Global BTZ facts at an E≥0-manifold, one chart at a time |
| [0174](entries/0174-t1-first-countable-from-charts.md) | pattern | Every E≥0-manifold is T1 and first countable from its charts |
| [0175](entries/0175-btz-line-every-manifold.md) | pattern | The BTZ line at every Hausdorff E≥0-manifold: Causal.SFALine.line |
| [0176](entries/0176-tau-translation-transitions.md) | pattern | Two X_A-charts into E₀ at a BTZ point differ along the axis by a τ-translation |
| [0177](entries/0177-massive-line-atlas.md) | pattern | The translation atlas of sing_κ(M), κ > 0, and massive_line at every Hausdorff E≥0-manifold |
| [0178](entries/0178-isclosed-sing-name-resolution.md) | pitfall | Inside Causal.X with open SFALocal, isClosed_sing resolves to the root Causal.isClosed_sing |
| [0179](entries/0179-epi-sfa-witness.md) | pattern | E_π: a SingularFlatAxioms witness with a non-empty massive line |
| [0180](entries/0180-sfa-every-manifold.md) | pattern | SingularFlatAxioms at every E≥0-manifold in one name: Causal.SFAManifolds.singularFlatAxioms |
| [0181](entries/0181-ealpha-connected.md) | pattern | E_κ is connected: SFAManifolds.massive_connectedSpace (a theorem, not an instance) |
| [0182](entries/0182-rows-at-m-pattern.md) | pattern | The singular-flat rows at M without SingularFlatAxioms: Causal.SingularRowsLocal |
| [0183](entries/0183-universe-metavariables-strict-forall.md) | pitfall | A strict theorem quantifying ∀ {M : Type u}, used as a term, needs its universe explicit |
| [0184](entries/0184-e0-natural-over-family.md) | pattern | E₀ with its natural causality over the whole family |
| [0185](entries/0185-open-subset-e0-manifold.md) | pattern | An open subset of a singular (G,X)-manifold is one, and of an E₀-manifold an E₀-manifold |
| [0186](entries/0186-e0-causal-curves-axis.md) | pattern | A causal curve of E₀ into a BTZ point stays on the axis and cannot jump over an axis point |
| [0187](entries/0187-k-rows-every-manifold.md) | pattern | The Section 3.3 K rows at every E≥0-manifold: Causal.SingularRowsK |
| [0188](entries/0188-cone-shell-not-cauchy.md) | pattern | A non-vacuous S for cor:K_ordre_Sigma without a Cauchy surface: the cone shell |
| [0189](entries/0189-measure-geroch-rows-at-m.md) | pattern | The measure and Geroch rows at M: Causal.SingularRowsGeroch |
| [0190](entries/0190-admissible-measure-forces-causal.md) | pattern | A causality carrying an admissible measure is causal |
| [0191](entries/0191-borel-inside-proof.md) | pattern | A statement with no measure need not carry [MeasurableSpace M] to call a lemma that does |
| [0192](entries/0192-bubble-meets-k-iff-persists.md) | pattern | When a bubble meets K: iff it persists near p |
| [0193](entries/0193-spokes-k-equals-i-without-pushup.md) | pattern | Spokes: a cheap local witness with K⁻(o) = I⁻(o) while push-up fails at o |
| [0194](entries/0194-explicit-set-argument-in-obtain.md) | pitfall | In `obtain ⟨…⟩ := thm isOpen_Ioi …`, give a set argument only the goal fixes explicitly |
| [0195](entries/0195-cauchy-surface-separates-causal-only.md) | pattern | A Cauchy surface separates with no splitting and no global hyperbolicity |
| [0196](entries/0196-point-between-on-curve.md) | pattern | A point of γ between two points of c lies on c, with no closed J^±(x) |
| [0197](entries/0197-btz-point-above-every-cauchy-surface.md) | pattern | A BTZ point in J⁺(S) ∖ S for every Cauchy surface S when sing₀ ≠ ∅ |
| [0198](entries/0198-chronology-in-causal-sfa.md) | pattern | Chronology at every point of a causal SingularFlatAxioms spacetime |
| [0199](entries/0199-jminus-open-from-pushup.md) | pattern | J⁻ of every open set is open under push-up and Z⁺ = M |
| [0200](entries/0200-diamond-compact-at-e-manifolds.md) | pattern | J⁺(Σ) ∩ J⁻(p) is compact at every globally hyperbolic E≥0-manifold, with no limit curves |
| [0201](entries/0201-cauchy-diamond-rows-hypothesis-free.md) | pattern | CauchyDiamond's rows hold with no named hypothesis at every pair of E≥0-manifolds |
| [0202](entries/0202-geroch-moreover-any-causal-flow.md) | pattern | Geroch's « Moreover » from any causal flow; state splittings with IsCausalFlow |
| [0203](entries/0203-e0-tau-flow.md) | pattern | E₀'s τ-translation as a mathlib Flow, causal and null |
| [0204](entries/0204-no-chronal-flow-with-btz.md) | pattern | No chronal flow once some point has I⁻ = ∅ |
| [0205](entries/0205-flow-tube-equalities.md) | pattern | Flow-tube equalities J^±(S) = φ(S × ℝ±) with no closedness |
| [0206](entries/0206-iscausalflow-stranded-in-splitting.md) | pitfall | IsCausalFlow lives in Causal.Splitting, whose closure is not model-free |
| [0207](entries/0207-jplus-open-at-btz-points.md) | pattern | J⁺ of every open set is open at a SingularFlatAxioms spacetime, BTZ points included, with no causality |
| [0208](entries/0208-diamond-past-compact.md) | pattern | J⁻(Σ) ∩ J⁺(p) is compact at every globally hyperbolic E≥0-manifold: A2's second field |
| [0209](entries/0209-btz-point-below-every-cauchy-surface.md) | pattern | A BTZ point below every Cauchy surface when sing₀ ≠ ∅ |
| [0210](entries/0210-singularpastat-sequence-instead-of-line.md) | pattern | At a BTZ point, SingularPastAt's sequence stands in for the line when no causality is available |
| [0211](entries/0211-cauchy-extension-not-onto.md) | pattern | A Cauchy extension that is not onto between E≥0-manifolds: {T < a} ⊂ E₀ |
| [0212](entries/0212-curvesextend-is-image-containment.md) | pitfall | CurvesExtend gives only image containment, never an extension of the parametrised curve |
| [0213](entries/0213-inclusion-emorphism-from-chartiso.md) | pattern | The inclusion of an open set is an IsEMorphism once it is a ChartIso |
| [0214](entries/0214-root-le-of-lt-in-causality.md) | pitfall | Inside namespace Causal.Causality, le_of_lt resolves to Causality.le_of_lt |
| [0215](entries/0215-second-countable-from-cauchy-surface.md) | pattern | Second countability of an E≥0-manifold from a second countable Cauchy surface |
| [0216](entries/0216-reg-second-countable.md) | pattern | Reg(M) of a connected, Hausdorff singular (Isom 𝐌³, 𝐌³)-manifold is second countable |
| [0217](entries/0217-singular-points-of-cauchy-surface-discrete.md) | pattern | The singular points of a Cauchy surface form a discrete subspace |
| [0218](entries/0218-inextensible-through-second-countable.md) | pattern | Through-hypotheses and SplitBy on T1, second countable spaces |
| [0219](entries/0219-agent-grep-wrapper.md) | pitfall | The agent shell's grep can silently find nothing in the paper sources |
| [0220](entries/0220-cauchy-embedding-open-embedding.md) | pattern | A Cauchy embedding is an open embedding: instances on N suffice |
| [0221](entries/0221-causal-ladder-no-facts.md) | pitfall | causal_ladder's fact rules, and why CurvesExtend is not one yet |
| [0222](entries/0222-gatearc-witness.md) | pattern | gateArc: a cheap Cauchy embedding that is not onto |
| [0223](entries/0223-causal-ladder-dual.md) | pattern | causal_ladder across time reversal (Rules imports Dual) |
| [0224](entries/0224-aesop-rule-pattern-guard.md) | pattern | A forward rule that grows its term needs an aesop rule pattern |
| [0225](entries/0225-aesop-depth-limit.md) | pitfall | aesop's depth limit counts forward steps: long conjunctions and nested reversals |
| [0226](entries/0226-ers-section4-second-countable.md) | pattern | ERS §4 on second countable backgrounds: the two suffixes |
| [0227](entries/0227-binders-diff.md) | pattern | Check 'the original less some binders' mechanically |
| [0228](entries/0228-lake-no-build-dry-run.md) | pattern | lake build --no-build is a dry run |
| [0229](entries/0229-inextensible-through-t1.md) | pattern | InextensibleThrough on a smaller open needs only T1 on second countable spaces |
| [0230](entries/0230-gluing-two-forms.md) | pattern | Gluing has two Lean forms; which constructions keep which |
| [0231](entries/0231-gluing-proof-routes.md) | pattern | Proving a concrete causality glues hereditarily: three routes |
| [0232](entries/0232-gluing-jump-lemma.md) | pattern | Refuting gluing: a relation never crosses between opens with disjoint closures |
| [0233](entries/0233-gluing-pullback-open.md) | pattern | Pullback preserves gluing along open maps only |
| [0234](entries/0234-gluing-galileo.md) | pattern | Galileo's spacetime does not glue for n ≥ 1 |
| [0235](entries/0235-gluing-linear-order.md) | pattern | The causality of a linear order glues iff its intervals are connected enough |
| [0236](entries/0236-value-allow-opaque.md) | pitfall | ConstantInfo.value? misses theorem bodies without allowOpaque |
| [0237](entries/0237-prod-membership-point.md) | pitfall | Give the point explicitly in ×ˢ membership proofs |
| [0238](entries/0238-forward-rule-instance-cost.md) | pitfall | A forward rule with instance arguments pays a failing synthesis at every goal |
| [0239](entries/0239-static-causally-plain.md) | pattern | Static spacetimes, hence E_α and Minkowski, are causally plain |
| [0240](entries/0240-causally-plain-on-restrict.md) | pitfall | No lemma restricts CausallyPlain to CausallyPlainOn W |
| [0241](entries/0241-corresponding-compact.md) | pattern | DEC-160's gluing compactness is Gluing.CorrespondingCompact |
| [0242](entries/0242-continuous-extension-not-compact.md) | pitfall | A continuous extension at corresponding points does not give CorrespondingCompact |
| [0243](entries/0243-sub-arc-curves.md) | pattern | The sub-arc form of the curves theorem |
| [0244](entries/0244-trim-keeps-inextensible.md) | pattern | Constant end pieces do not affect inextensibility |
| [0245](entries/0245-cauchy-inf.md) | pattern | A Cauchy surface Cauchy in A and in B is Cauchy in A ∩ B |
| [0246](entries/0246-lemma-k-ett-layer.md) | pattern | The Lemma K family is ETT-layer; its model corollaries are in Causal.Model.LemmaKModels |
| [0247](entries/0247-model-path-shortest.md) | pitfall | model_path shows one shortest chain: check each direct import before a hoist |
| [0248](entries/0248-model-stranded-duplicates.md) | pattern | Two ETT-layer re-proofs can now cite their originals |
| [0249](entries/0249-one-sided-future-base.md) | convention | The one-sided chronal and endpoint notions have the future as base |
| [0250](entries/0250-rw-chronal-neighbours.md) | pitfall | rw [ChronalNeighbours, foo_iff (C := C.dual)] no longer finds the future side |
| [0251](entries/0251-definition-body-refactor-check.md) | pattern | Checking a definition-body refactor that keeps every statement |
| [0252](entries/0252-emit-lean-ignores-args.md) | pitfall | tools/ladder.py emit-lean --help runs emit-lean |
| [0253](entries/0253-cauchy-separation.md) | pattern | lem:Sigma_separe's model-free steps are in Causal.CauchySeparation |
| [0254](entries/0254-hoist-check-ledger-files.md) | pitfall | Before a hoist, check the ledger rows listing the moved declarations' file |
| [0255](entries/0255-hoist-universe-variable.md) | pitfall | A hoisted declaration under variable {M : Type*} must keep its universe parameter |
| [0256](entries/0256-cited-twins.md) | convention | Twins under different names, kept because both are cited |
