---
id: 0011
title: Two tools for building cone spheres from charts of models
kind: pattern
created: 2026-11-20
---
`GX.isAEMorphismOf_maximalAEAtlas_of_forall`: a map that reads the charts of one generating atlas as
charts of another is an a.e. morphism between the maximal atlases. `GX.XAChart.ofIsOpenEmbedding`: an
open embedding of a connected model that is an a.e. morphism gives an X_α-chart. The football
(`GX.Spherical.Football`) is built with them: two copies of C_θ glued by the half-turn
(`GX.halfTurn_smul_stereoInv`: stereoInv(v) ↦ stereoInv(1/v), `GX.det_flipIsom`); reuse them for
T-gx-troyanov-triangle (T-gx-cone-football).
