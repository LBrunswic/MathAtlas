# 0054 — Anonymous constructor fails over projOfAff: use a local instance or letI

*Found 2026-11-22 by T-bz-poche-nonconstant; recorded by the master session.*

Pitfall: the anonymous constructor of a structure with an instance-implicit parameter (IsPocheProjNC under projOfAff, which is not a global instance) synthesizes the ChartedSpace instance instead of unifying it. It fails with « failed to synthesize ChartedSpace (S n) V ». Fix: `attribute [local instance] projOfAff` in a section, or `letI` in the proof. Under `letI := transportChartedSpace …` you cannot reuse a lemma stated for projOfAff: Lean reports « synthesized type class instance is not definitionally equal ». Re-prove the field instead.
