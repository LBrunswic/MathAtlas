# 0030 — The cote along a line of H̊ through m

*Found 2026-11-21 by T-bz-c2-theoreme; recorded by the master session.*

With direction x ∈ ker l, take u := (Sphere.lbar l).smulRight ⟨x, hlx⟩ and v₀ := Sphere.nrep l m. Then `Sphere.coe_smul_vadd` gives ↑(t • u +ᵥ m) = s(v₀ + t x), and `AffineMap.map_vadd` gives z(t • u +ᵥ m) = t * z.linear u + z m. This is the template of Remarque 2's hsal (`Poches.lean`) and of 4° (`theoreme_quatrieme`).
