import CausalScaffold.GerochEquiv
import CausalScaffold.GXSingular
import CausalScaffold.MinkowskiMeasure
import CausalScaffold.SingularGeroch
import CausalScaffold.SubExtension

/-!
# CausalScaffold

Work on *Topological spacetimes (I)* which is not in the strict library yet: either a proof is
missing (a tagged `sorry`), or the file rests on a reading of the paper which awaits the author's
ruling. Each module says which. Never imported by `Causal`.

The modules of the campaign of 2026-09-27 (DEC-9) land here, one package per agent; graduation
into `Causal/` is a file move and is the master session's. Every module is imported here, so
that `scripts/AxiomSweep.lean` sweeps it: a module not imported is a module the gate cannot see.
-/
