import Mathlib.Probability.Kernel.Basic

/-!
# EGF — package root (wave 0 placeholder)

The library of `papers/egf`: *Ergodic Generative Flows* (ICML 2025), formalized in a package of
its own at the hub's pin (DEC-133). Wave 0 only checks that the package builds against the hub's
Mathlib; the definitions and the headline `EGF.main_universality` arrive in `EGF/` module by module
(T-egf-headline).
-/

namespace EGF

/-- Package marker (wave 0). -/
def packageName : String := "EGF"

end EGF
