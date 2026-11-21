import Causal.Causality
import Causal.Properties
import Causal.StrongCausality
import Causal.GlobalHyperbolicity
import Causal.Reachable
import Causal.Generated
import Causal.Local
import Causal.Minimal
import Causal.Subdivision
import Causal.Lines
import Causal.Measure
import Causal.Curves
import Causal.ArcConnected
import Causal.LinesCurves
import Causal.TransparentLine
import Causal.Galileo
import Causal.LinesReachable
import Causal.PushUp
import Causal.MeasureRemarks
import Causal.MeasureSum
import Causal.MeasureLocal
import Causal.Pushout
import Causal.Morphism
import Causal.PushoutCausal
import Causal.Chains
import Causal.Inextensible
import Causal.Cauchy
import Causal.Geroch
import Causal.GXStructure
import Causal.Static
import Causal.Minkowski
import Causal.SingularFlat
import Causal.CauchyExtension
import Causal.CauchyDiamond
import Causal.ChainsCurves
import Causal.ChainsOrder
import Causal.Model.Cone
import Causal.Model.Massive
import Causal.CompactCauchy
import Causal.CurvesExtend
import Causal.Flat.Bieberbach
import Causal.Flat.Form
import Causal.Flat.Geroch.ConeNull
import Causal.Port.GXBasic
import Causal.Port.UniversalCover
import Causal.Flat.Achronal
import Causal.Flat.InducedLength
import Causal.Flat.IsomCausal
import Causal.Flat.Isometries
import Causal.Flat.Penrose
import Causal.Port.Developing
import Causal.Flat.AchronalDomains
import Causal.Flat.Cosmological
import Causal.Flat.Developing
import Causal.Flat.FlatSpacetime
import Causal.Splitting
import Causal.Flat.Externals
import Causal.Flat.Geroch.ChartNull
import Causal.Flat.LipschitzGraph
import Causal.Flat.Quotient
import Causal.LemmaKBare
import Causal.LemmaKReduction
import Causal.LemmaKSC
import Causal.LemmaKObstruction
import Causal.LevinUtility
import Causal.LemmaKLocal
import Causal.LemmaKSCLocal
import Causal.Flat.Develop
import Causal.Flat.Examples
import Causal.Flat.Laoucapulse
import Causal.Flat.SecondCountable
import Causal.Flat.Lox.CentralFix
import Causal.Flat.Lox.CommuteOnFix
import Causal.Flat.Lox.EllipticCommonFix
import Causal.Flat.Lox.FiniteIndexND
import Causal.Flat.Lox.FixLoxodromic
import Causal.Flat.Lox.LatticeTrivial
import Causal.Flat.Lox.NullLevelFix
import Causal.Flat.Lox.RegularLattice
import Causal.Flat.Lox.SelbergMono
import Causal.Flat.Lox.TwoNullNormalForm
import Causal.Flat.Abel
import Causal.Flat.CauchyComplete
import Causal.Flat.TwistedProduct
import Causal.Flat.Cla.G9PairLin
import Causal.Flat.Geroch.ChartMeasure
import Causal.Flat.Lox.ClosedSubgroupNhds
import Causal.Flat.Lox.MisnerBieberbach
import Causal.Flat.Lox.MisnerLimitSet
import Causal.Flat.Lox.NilpotentFix
import Causal.Flat.Cla.CCComponent
import Causal.Flat.Cla.SmoothCone
import Causal.Flat.Geroch.Reach
import Causal.Flat.Lox.LevelComplete
import Causal.Flat.Lox.PerpInvariant
import Causal.Flat.Lox.QuotientComplete
import Causal.Flat.Lox.RestrictFix
import Causal.Flat.Lox.RestrictLimitSet
import Causal.Flat.Lox.RestrictOrient
import Causal.Flat.Lox.UnipotentCentre
import Causal.Flat.Nonlox.BTrivial
import Causal.Flat.Nonlox.EllipticBieberbach
import Causal.Flat.Nonlox.NullFrame
import Causal.Flat.Nonlox.SpacelikeSpan
import Causal.Flat.Nonlox.TranslationLTP
import Causal.Flat.Nonlox.UnipotentFrame
import Causal.Flat.Nonlox.UnipotentLTP
import Causal.Flat.Nonlox.UnipotentRestriction
import Causal.Flat.Cla.SmoothGlue
import Causal.Flat.Lox.MisnerFrame
import Causal.Flat.Lox.RestrictUnipotent
import Causal.Flat.Nonlox.NullSlices
import Causal.Flat.Cla.SmoothCap
import Causal.Flat.Nonlox.UnipotentUpToFrame
import Causal.Flat.Lox.MisnerRestrict
import Causal.Flat.Nonloxodromic
import Causal.Flat.Lox.SecondNullFix
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.Flat.Cla.CompactComplete
import Causal.Flat.Cla.CoverComp
import Causal.Flat.Cla.FiniteCover
import Causal.Flat.Cla.G9Pair
import Causal.Flat.Cla.LTPConvex
import Causal.Flat.Cla.LTPEnlarge
import Causal.Flat.Cla.LocallyCauchy
import Causal.Flat.Cla.RegularComplete
import Causal.Flat.Cla.TameNested
import Causal.Flat.Cla.UnipEnvelope
import Causal.Flat.Cla.CoverMax
import Causal.Flat.Cla.G9
import Causal.Flat.Cla.UnipComplete
import Causal.Flat.Cla.CoverMGH
import Causal.Flat.Classification
import Causal.Flat.Lox.PastProper
import Causal.Flat.TheoremBInputs
import Causal.Flat.GerochFlat
import Causal.Flat.CBGCompact
import Causal.SubExtension
import Causal.GXSingular
import Causal.Port.Portly
import Causal.Port.SingularAtlas
import Causal.GXSingularDEC25
import Causal.SingularGeroch
import Causal.CBG.CausalConvex
import Causal.CBG.Geometry
import Causal.CBG.ETTSection4
import Causal.CBG.Injective
import Causal.CBG.FamilyGluing
import Causal.CBG.Bound
import Causal.CBG.Corresponding
import Causal.CBG.Pgcd
import Causal.CBG.NoCorresponding
import Causal.CBG.Ppcm
import Causal.CBG.Maximal
import Causal.CBG.FromModel
import Causal.Flat.CBGSlice
import Causal.Flat.CBGGerm
import Causal.Flat.CBG
import Causal.LemmaK
import Causal.Flat.LimitesGeneral
import Causal.Flat.AgissonsGeneral
import Causal.Flat.LipLength
import Causal.Flat.LaoucapulseVolume
import Causal.Flat.QuoFull
import Causal.Flat.Semicomplete
import Causal.Flat.SplittingFull
import Causal.Flat.BieberbachZassenhaus
import Causal.Flat.BieberbachAbelian
import Causal.Flat.BieberbachMinSet
import Causal.Flat.BieberbachEffective
import Causal.Flat.BieberbachProof
import Causal.Flat.GromovBase
import Causal.Flat.GromovBounded
import Causal.Flat.GromovUnbounded
import Causal.Flat.GromovProof
import Causal.Flat.SelbergBase
import Causal.Flat.SelbergResidue
import Causal.Flat.SelbergTorsion
import Causal.Flat.SelbergMatrix
import Causal.Flat.SelbergProof
import Causal.Flat.MaxUnipHirsch
import Causal.Flat.MaxUnipCocycle
import Causal.Flat.MaxUnipFitting
import Causal.Flat.MaxUnipProof
import Causal.Flat.ACDReduction
import Causal.Flat.ACDHall
import Causal.Flat.ACDNull
import Causal.Flat.ACDLoxodromic
import Causal.Flat.ACDProof
import Causal.Flat.BarbotUnconditional
import Causal.Flat.AffUnipFitting
import Causal.Flat.AffUnipCocycle
import Causal.Flat.AffUnipProof
import Causal.Flat.AffACDBase
import Causal.Flat.AffACDTriang
import Causal.Flat.AffACDLocal
import Causal.Flat.AffACDProof
import Causal.Remarks.BTZPoints
import Causal.Remarks.Tarentin
import Causal.Remarks.MassiveManifold
import Causal.LimitCurves
import Causal.Port.E0Model
import Causal.Port.E0Causality
import Causal.Port.E0Axioms
import Causal.MinkowskiMeasure
import Causal.KBorelien
import Causal.CBG.ETTSubExtension
import Causal.CBG.SubExtensionAbstract
import Causal.GluingHausdorff
import Causal.NestedCausalities
import Causal.DeuxPushup
import Causal.LocateExtension
import Causal.LadderLocal
import Causal.Ladder.Basic
import Causal.Ladder.Rules
import Causal.Ladder.Test
import Causal.CompactMinimal
import Causal.CurveComponents
import Causal.DependenceDomain
import Causal.ErsUniqueness
import Causal.CausalIsoInvariance
import Causal.Model.EAlphaCauchy
import Causal.Port.E0Strong
import Causal.Port.E0SingularFlat
import Causal.Port.E0ModelRows
import Causal.CorrespondingPoints
import Causal.CorrespondingSpacelike
import Causal.CauchyDual
import Causal.Model.CurvesExtendModels
import Causal.Model.InjectiveMinkowski
import Causal.NestedConverse
import Causal.NestedTransfer
import Causal.SbierskiProp37
import Causal.ChronalNeighbourBridge
import Causal.PushUpNotOpen

/-!
# Causal — topological spacetimes

The strict library of *Topological spacetimes (I): from scratch to Geroch's and
Choquet-Bruhat--Geroch's theorems*. `sorry` is a compile error here. Every module announces the
paper labels it certifies in its docstring, in the form the ledger reads
(`papers/ett/ledger/`).

Since 2026-11-02 it also holds the Barbot campaign (*Globally hyperbolic flat space-times*,
`docs/BARBOT.md`): `Causal.Flat.*`, `Causal.Port.*`, `Causal.CompactCauchy`, `Causal.CurvesExtend`,
`Causal.Splitting`, `Causal.LemmaKBare`, `Causal.LemmaKReduction`, whose labels are b-prefixed and read by
`papers/barbot/ledger/` (kb/0024), with the label-free Lemma K work of DEC-92
(`Causal.LemmaKSC`, `Causal.LemmaKObstruction`, `Causal.LevinUtility`, `Causal.LemmaKLocal`,
`Causal.LemmaKSCLocal`) and Lemma K's statement of record in ETT's setting (DEC-93,
`Causal.LemmaK`: causally open, second countable); the 2026-11-02 proof-gap round's
`Causal.Flat.LaoucapulseVolume` (DEC-102), `Causal.Flat.QuoFull`, `Causal.Flat.Semicomplete`
(DEC-103) and `Causal.Flat.SplittingFull` (DEC-100); the proof of Bieberbach I through virtual
abelianity (DEC-110: `Causal.Flat.BieberbachZassenhaus`, `…Abelian`, `…MinSet`, `…Effective`,
`Causal.Flat.BieberbachProof`); the proof of Barbot's Prop 9.1 external `BenoistNoLox` by Gromov's
classification on `ℍᵈ`, without Zariski closure (DEC-111: `Causal.Flat.GromovBase`, `…Bounded`,
`…Unbounded`, `Causal.Flat.GromovProof`); and, graduated the same day, the CBG work
(`Causal.CBG.*`, `Causal.Flat.CBG`, `Causal.Flat.CBGGerm`, `Causal.Flat.CBGSlice`,
`docs/CBG-DESIGN.md`). Since 2026-11-03 the Barbot external `SelbergLemma` is proved for every
finite-dimensional real `V` by congruence subgroups (DEC-115: `Causal.Flat.SelbergBase`,
`…Residue`, `…Torsion`, `…Matrix`, `Causal.Flat.SelbergProof`). The last two externals,
`MaxUnipotentSubspace` (Fried–Goldman–Hirsch: `Causal.Flat.MaxUnipHirsch`, `…Cocycle`,
`…Fitting`, `Causal.Flat.MaxUnipProof`) and `AuslanderCarriereDalbo` (a Lorentz
Zassenhaus–Frobenius argument: `Causal.Flat.ACDReduction`, `…Hall`, `…Null`, `…Loxodromic`,
`Causal.Flat.ACDProof`), are proved too (DEC-121), and `Causal.Flat.BarbotUnconditional` states
Theorems A and B with no external hypothesis. Since 2026-11-08 both are proved in the PRINTED
generality of `Aff(n, ℝ)` (DEC-123), the Isom forms becoming corollaries: Prop 5.2 for every
nilpotent group of affine transformations (`Causal.Flat.AffUnipFitting`, `…Cocycle`,
`Causal.Flat.AffUnipProof`) and Thm 5.1 for every discrete subgroup of `Aff(n, ℝ)`
(`Causal.Flat.AffACDBase`, `…Triang`, `…Local`, `Causal.Flat.AffACDProof`).
-/
