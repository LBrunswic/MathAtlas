---
id: 0020
title: Convex spherical s-gons: GX.SphPolygon, built from the polar polygon inscribed in a circle
kind: pattern
created: 2026-11-21
---
Found by T-gx-troyanov-polygon. `GX.SphPolygon` (`GX.Spherical.TroyanovPolygon`) records the side normals, the two sides at each vertex, and three conditions (pos, vertex_sep, cover). To build a polar polygon with prescribed sides β_k, inscribe it in a circle of radius r about the north pole: a chord of length β spans the azimuth arccos((cos β − cos² r)/sin² r) (`GX.chordGap`); run the intermediate value theorem in r (`GX.exists_polar_radius`, `GX.exists_polar_polygon`), with two cases according to whether the centre lies inside the polygon; then `GX.SphPolygon.ofCyclic`.
