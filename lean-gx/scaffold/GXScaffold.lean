import GXScaffold.Basic
import GXScaffold.BBS.HSSingularities
import GXScaffold.BBS.PSL2NormalForms
import GXScaffold.BBS.HSPositive
import GXScaffold.BBS.HSDegree
import GXScaffold.BBS.HSAntipodal
import GXScaffold.BBS.HSClassification
import GXScaffold.BBS.HSRemarkReadings
import GXScaffold.BBS.HSCausal
import GXScaffold.BBS.HSLinkRemarks
import GXScaffold.BBS.HSCheminsing
import GXScaffold.BBS.HSPositiveMass
import GXScaffold.Interaction.PuncturedSphere
import GXScaffold.Interaction.TheoremM
import GXScaffold.Interaction.TheoremMTheta
import GXScaffold.Spherical.TroyanovAngles
import GXScaffold.Spherical.ThurstonSuspension
import GXScaffold.Interaction.FunnelGTilde
import GXScaffold.BTZ.MaxExtension
import GXScaffold.BTZ.CommonReg
import GXScaffold.BTZ.CauchySpear
import GXScaffold.BTZ.LineStructure
import GXScaffold.BTZ.RichardsSplit
import GXScaffold.BTZ.AdmissibleLinear
import GXScaffold.BTZ.Admissible
import GXScaffold.BTZ.SurfaceGroupNonMetabelian

/-! The scaffold library of the paper `gx`. Modules here may carry tagged `sorry`s; every module has graduated to `GX` except the 3+1 research modules (`Interaction`, T-3p1-theorem-m and T-3p1-theorem-m-theta, sorry-free, kept here as research until the author reads them), BBS § 3.3's classification (`BBS.HSSingularities`, T-bbs-hs-singularities to T-bbs-hs-link-types, sorry-free; `BBS.PSL2NormalForms`, sorry-free, which imports the research module `Interaction.FunnelGTilde` and graduates with it), the angle-tied Troyanov statement (`Spherical.TroyanovAngles`, two tagged sorrys: T-gx-troyanov, T-gx-troyanov-suspension), and the btz § 5 modules under `BTZ` (`MaxExtension`, `CommonReg`, `CauchySpear`, `LineStructure`, `RichardsSplit`, `AdmissibleLinear`, `Admissible`, `SurfaceGroupNonMetabelian`); the `btzprop:reg_complete` chain (`CompleteCauchy` to `RegComplete`) graduated to `GX.BTZ` (T-btz-reg-complete-graduate). -/
