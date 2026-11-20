# 0010 — Segments through a developing map

*Found 2026-11-20 by T-bz-c2-projection; recorded by the master session.*

(M, N) is a segment of a locally affine V iff some compact set containing M and N carries p
injectively onto [p M, p N] (`isAffSegment_iff_of_isDeveloping`, from Mathlib's
`Set.InjOn.exists_mem_nhdsSet`; `Benzecri.Chapter2.Projection`). Build segments by lifting through p
and concatenating (`IsAffSegment.extend`), never by hand-made charts. Automorphisms carry segments to
segments (`IsAffSegment.image_smul_aut`) and act along a segment as one element of GA(n)
(`IsAffSegment.exists_eqOn_smul`), with no connectedness of V.
