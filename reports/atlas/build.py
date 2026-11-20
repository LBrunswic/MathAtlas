import json
D=open("data.json",encoding="utf-8").read()
HUB={
 "clusters":[{"id":"geo","title":"Lorentzian and (G,X) geometry"},{"id":"gfn","title":"Generative flows"},{"id":"other","title":"Other papers"},{"id":"libs","title":"Lean libraries"}],
 "papers":{
  "ett":{"short":"ETT","cluster":"geo","authors":"L. Brunswic","title":"Topological spacetimes (I): from scratch to Geroch's and Choquet-Bruhat–Geroch's theorems","home":"lean-causal","source":"legacy ETT.tex",
    "summary":"Causal theory for topological spaces with a causality and no smooth structure, so singular spacetimes (cones E_α, BTZ lines) are first-class. The library proves Geroch (i)⇒(ii)⇒(iii), Lemma K through Levin's theorem, and the universal maximal Cauchy development.",
    "headline":["Causal.geroch_i_imp_ii","Causal.geroch_ii_imp_iii","Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen","Causal.CBG.cbg_ett"],
    "open":"Singular §3–§4 material is proved under named model hypotheses until gx supplies the instance; the CBG rows are not yet anchored; Geroch (iii)⇒(i) is cited; five scaffold sorrys; open questions OQ-10…20."},
  "barbot":{"short":"Barbot","cluster":"geo","authors":"T. Barbot · J. Geom. Phys. 53 (2005)","title":"Globally hyperbolic flat space-times","home":"lean-causal (Causal.Flat)","source":"arXiv math/0402257",
    "summary":"Theorems A and B (classification of Cauchy-complete and Cauchy-compact GH flat spacetimes) proved with no hypothesis beyond the paper's. Selberg, Bieberbach I, Auslander–Carrière–Dal'bo, Fried–Goldman–Hirsch and Gromov (in place of Benoist) were proved on the way.",
    "headline":["Causal.Flat.barbot_A_unconditional","Causal.Flat.barbot_B_geroch_unconditional","Causal.Flat.selbergLemma","Causal.Flat.affAuslanderCarriereDalbo"],
    "open":"Only the five terminal rows, off the spine of Theorems A and B: convex cocompactness (Sullivan), the thrice-punctured-sphere computation, CMC foliations."},
  "gx":{"short":"gx","cluster":"geo","authors":"L. Brunswic · Geom. Dedicata (2024)","title":"On branched coverings of singular (G,X)-manifolds","home":"lean-gx","source":"arXiv 2010.10610",
    "summary":"Singular (G,X)-manifolds, Fox completion, branched coverings and their Galois correspondence, the singular developing theorem, tame and virtually tame singularities, and the uniformization of BTZ-manifolds in its ruled form.",
    "headline":["GX.btz_uniformization","GX.galois_correspondence","GX.singular_developing_theorem","GX.developing_theorem","GX.e0_cbg"],
    "open":"Six rows partial by ruling (corrected forms or a named external: Troyanov). Thirteen rows after \\end{document} are terminal."},
  "benzecri":{"short":"Benzécri","cluster":"geo","authors":"J.-P. Benzécri · Bull. SMF 88 (1960)","title":"Sur les variétés localement affines et localement projectives — Ch. 1","home":"lean-benzecri","source":"Numdam scan, transcription",
    "summary":"Locally projective and affine manifolds, affine cones and the functorial equivalence with locally projective manifolds, and Theorem A: V × S¹ is locally affine for compact locally projective V.",
    "headline":["Benzecri.theoremA","Benzecri.coneEquivalence","Benzecri.ConeCex.not_t2Space_coneBase_dim"],
    "open":"The p. 238 universal-cover sentence needs a universal cover, which lean-gx has and mathlib does not. The transcription awaits the author's check."},
  "bbs":{"short":"BBS → 3+1","cluster":"geo","authors":"Barbot–Bonsante–Schlenker review and research notes","title":"Collisions of particles in locally AdS spacetimes I, toward 3+1","badge":"research · no ledger",
    "summary":"A review of BBS against gx with a layered roadmap (suspensions, links by signature, Riemannian and Lorentzian branches), and an append-only log of 3+1 ideas: Theorem M (momentum conservation at a 2+1 interaction) and Theorem G (spacelike total momentum forms a black hole), both unverified.",
    "headline":["GX.Suspension.Conic","GX.Suspension.Celestial","GX.Suspension.Affine"],
    "open":"BBS-Q1…Q8, the funnel lemma, Theorem M in Lean; codimension-2 strata need an interface ruling (BBS-Q7)."},
  "gfnbounds":{"short":"GFN Bounds","cluster":"gfn","authors":"Brunswic et al.","title":"Universality and Convergence of Generative Flows — Apps A, B, H","home":"lean (GFNBoundsLean, read-only)","closed":94,"target":94,"badge":"98 rows · 4 terminal",
    "summary":"Universality, the stable bounds, the Silva et al. comparison and the doubling-graph counterexample, in the GFNBoundsLean submodule pinned at 2e9865c. Not written from this hub.",
    "headline":[],"open":"Four terminal remarks."},
  "egf":{"short":"EGF","cluster":"gfn","authors":"Brunswic et al. · ICML 2025","title":"Ergodic Generative Flows","source":"camera-ready",
    "summary":"Generative flows whose forward policy is a finite family of diffeomorphisms; universality from ergodicity. Ledger only: the Lean anchor named in STORY.md does not exist yet.","headline":[],"open":"All of it; first in the author's priority order (DEC-4)."},
  "nonacyclic":{"short":"Non-acyclic GFN","cluster":"gfn","authors":"","title":"Non-acyclic GFlowNets","badge":"blocked · OQ-3",
    "summary":"Only a PDF snapshot exists; the TeX source has not been located (OQ-3), so no ledger can be built.","headline":[],"open":"Locate the source."},
  "syracuse":{"short":"Syracuse","cluster":"other","authors":"L. Brunswic","title":"On non-trivial cycles of the 3x+1 problem","summary":"An extension of Terras's method constraining non-trivial cycles through upper bounds and cyclotomic arithmetic. Ledger only.","headline":[]},
  "dyniso":{"short":"dyniso","cluster":"other","authors":"","title":"Orthogonal hyper-connections: why the Birkhoff polytope breaks dynamical isometry","summary":"Bistochastic skip mixing contracts the non-Perron spectrum over depth; orthogonal skips restore dynamical isometry. Ledger only.","headline":[]},
  "yamabe":{"short":"Yamabe gap","cluster":"other","authors":"L. Brunswic","title":"The Yamabe gap: inhomogeneity measure and morphological driver of cosmic expansion","summary":"The averaged scalar curvature of a void is governed by the Yamabe energy of its leaves; bounds on punctured flat tori. Ledger only.","headline":[]}
 },
 "libs":{
  "lean-causal":{"what":"Topological spacetimes, flat Lorentzian geometry","stats":"11,851 decls · 0 strict sorry","cells":[["11,851","strict declarations"],["195","modules"],["5","scaffold sorrys"]],"about":"Strict library Causal (ETT layer and Causal.Flat for Barbot), scaffold CausalScaffold. Mathlib only."},
  "lean-gx":{"what":"Singular and branched (G,X)-manifolds, BTZ","stats":"11,887 decls · 0 sorry","cells":[["11,887","strict declarations"],["46","modules"],["0","sorry"]],"about":"Entirely strict. Pins lean-causal; only GX.BTZ and GX.Lorentz may import Causal (DEC-33)."},
  "lean-benzecri":{"what":"Locally affine and projective manifolds","stats":"2,447 decls · 0 sorry","cells":[["2,447","strict declarations"],["27","modules"],["0","sorry"]],"about":"Mathlib only by design (DEC-112); a generalization layer is planned."},
  "lean":{"what":"GFNBoundsLean (read-only submodule)","stats":"94/98 rows closed","cells":[["94","rows closed"],["98","rows"],["2e9865c","pin"]],"about":"Not written from this hub (DEC-2). Absorbing it in-tree is OQ-1."}
 },
 "edges":[
  {"from":"ett","to":"barbot","short":"library","why":"Barbot is formalized on the ETT library: flat spacetimes are ETT spacetimes, and Lemma K, Geroch and CBG are shared (DEC-34)."},
  {"from":"barbot","to":"gx","short":"Thm A","why":"gx §4 classifies the regular part Reg M with Barbot's Theorem A, imported from lean-causal (DEC-26, DEC-30, DEC-34)."},
  {"from":"ett","to":"gx","short":"CBG, causality","why":"gx's BTZ section uses ETT's causality and proves Choquet-Bruhat–Geroch for E₀-manifolds on ETT's CBG (DEC-29, DEC-33)."},
  {"from":"gx","to":"bbs","short":"suspensions","why":"The 3+1 programme's first layers (conic and celestial suspensions, links in affine spaces) are built in lean-gx."},
  {"from":"benzecri","to":"bbs","short":"cones","why":"N7 of the 3+1 notes: Benzécri's affine cones systematize the suspension construction; this motivated the Benzécri campaign (DEC-112)."},
  {"from":"gx","to":"benzecri","short":"universal cover","dashed":True,"why":"Benzécri's one open row needs a universal cover; lean-gx builds it, but lean-benzecri stays mathlib-only until the generalization layer exists."},
  {"from":"gfnbounds","to":"egf","short":"GFN line","dashed":True,"why":"Both belong to the generative-flow line; EGF is to be rebuilt from the Lean, and the GFN library is to be absorbed in-tree after the freeze (OQ-1)."},
  {"from":"lean-causal","to":"lean-gx","short":"pinned import","why":"lean-gx's lakefile pins lean-causal; the import gate restricts it to GX.BTZ and GX.Lorentz."}
 ],
 "provenance":"Generated 2026-11-20 on node1 from papers/*/ledger/ledger.json (lean-causal and lean-gx at 18d8c16, lean-benzecri at 6cbca77) and the package checks of the same day. Statement text is the labelled legacy TeX."
}
t=open("template.html",encoding="utf-8").read()
out=t.replace("__DATA__",D).replace("__HUB__",json.dumps(HUB,ensure_ascii=False))
open("atlas.body.html","w",encoding="utf-8").write(out)
print(len(out))
