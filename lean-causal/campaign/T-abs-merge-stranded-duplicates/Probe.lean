import Causal.Cauchy
import Causal.Ers475CauchyForm
import Causal.Flat.CBG
import Causal.Flat.CBGSlice
import Causal.LemmaK
import Causal.CBG.Ppcm

/-! T-abs-merge-stranded-duplicates: every full name resolves, and the axioms of each merged
constant. Read-only probe; not part of any library. -/

open Causal

#check @Causal.Causality.IsCauchySurfaceOn.of_inter_eq
#check @Causal.CBG.isCauchySurfaceOn_congr
#check @Causal.CBG.isCauchySurfaceOn_congr'
#check @Causal.Causality.causallyOpenFuture_of_pushUp
#check @Causal.Causality.causallyOpen_of_pushUp
#check @Causal.Causality.PushUp.causallyOpenFuture_of_chronalPastNeighbours
#check @Causal.Causality.PushUp.causallyOpen_of_chronalNeighbours
#check @Causal.Causality.Jplus_inter_Jminus_eq
#check @Causal.Causality.IsAcausal.Jplus_inter_Jminus

#print axioms Causal.Causality.IsCauchySurfaceOn.of_inter_eq
#print axioms Causal.CBG.isCauchySurfaceOn_congr
#print axioms Causal.CBG.isCauchySurfaceOn_congr'
#print axioms Causal.Causality.causallyOpenFuture_of_pushUp
#print axioms Causal.Causality.causallyOpen_of_pushUp
#print axioms Causal.Causality.PushUp.causallyOpenFuture_of_chronalPastNeighbours
#print axioms Causal.Causality.PushUp.causallyOpen_of_chronalNeighbours
#print axioms Causal.Causality.Jplus_inter_Jminus_eq
#print axioms Causal.Causality.IsAcausal.Jplus_inter_Jminus
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen
#print axioms Causal.timelikeLine_causallyOpen

-- The CBG twins' proof terms are now identical: equal `Expr.hash` of their values in the
-- before/after dump (scratch/dump_cmp.py), 2539726639 for both.
