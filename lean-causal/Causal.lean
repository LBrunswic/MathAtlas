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
import Causal.SingularGeroch
import Causal.CBG.CausalConvex
import Causal.CBG.Geometry
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
`Causal.LemmaK`: causally open, second countable); and, graduated the same day, the CBG work
(`Causal.CBG.*`, `Causal.Flat.CBG`, `Causal.Flat.CBGGerm`, `Causal.Flat.CBGSlice`,
`docs/CBG-DESIGN.md`).
-/
