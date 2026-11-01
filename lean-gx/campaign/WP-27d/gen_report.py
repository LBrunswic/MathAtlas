import json, sys
sorry_count = int(sys.argv[1]) if len(sys.argv) > 1 else 2
s1_closed = sorry_count == 0
ex_sorries = []
if sorry_count >= 1:
    ex_sorries = [
        {"decl": "GX.carthesian_piOne_S₂", "obstruction": "pi_1(R^3 minus S2) = Z at every base point: the degree map (winding of psi + i z, psi a signed distance to the planar sine curve P) is defined and homotopy invariant, but its injectivity on pi_1 needs a homotopy equivalence between R^3 minus S2 and R^3 minus S1 (the deformation (x,y,z) -> (x, y + 2 s psi/(|psi|+|z|), z) into R^3 minus the strip R x [-1,1] x {0}, then the radial expansion in (y,z)) together with the conjugation-by-track lemma for homotopic maps on fundamental groups at moving base points; not formalized in this package"},
        {"decl": "GX.carthesian_S₂_almostTrivial", "obstruction": "reduces (through GX.AlmostTrivialAt.of_mid and the homotopy form) to the injectivity of the degree on pi_1(R^3 minus S2) (the obstruction of GX.carthesian_piOne_S₂) plus loops of every degree inside every small ball around O (crossing a pocket of A+ downwards and one of A- upwards) and the path-connectedness of B(O,r) minus S2; the paper's own argument ('Y minus closed B(S2,eps) is homeomorphic to Y minus S1', l.1227) is not used"}
    ]
labels = [
 {"label": "def:almost_trivial_loop", "tex_lines": [1210, 1213], "status": "closed", "marked": True,
  "decls": ["GX.AlmostTrivialCC", "GX.OmegaSet", "GX.MemOmega", "GX.AlmostTrivial", "GX.AlmostTrivialAt", "GX.AlmostTrivial.almostTrivialCC", "GX.AlmostTrivialCC.almostTrivial", "GX.almostTrivialCC_iff", "GX.eventually_almostTrivialAt_iff", "GX.eventually_homotopic_family", "GX.OmegaHomotopic.mem_connectedComponentIn"],
  "hypotheses": [
    {"paper": "X Hausdorff, locally path-connected", "here": "weakened", "note": "not used by the definition"},
    {"paper": "U open, x in closure U", "here": "weakened", "note": "not used by the definition"}],
  "sorries": [],
  "findings": ["l.1201 calls 'same connected component of the compact-open Omega(x,y,U)' and 'homotopic with respect to U' equivalent. Homotopic => same component holds in general (GX.OmegaHomotopic.mem_connectedComponentIn); for almost triviality the converse is proved when U is open and semilocally simply connected and X locally path-connected (GX.almostTrivialCC_iff: for each open V the set of loops homotopic w.r.t. U to a loop of Omega(x,x,V cap U) is clopen in Omega(x,x,U), being decided by the middle of the loop, whose compact-open perturbations are homotopies in U up to short end connections, by homotopy lifting in the universal cover of U). Without semilocal simple connectivity of U the 'equivalently' is not established (the clopen argument needs it: without it a compact-open perturbation of the middle of a loop need not be homotopic to it; no counterexample to the 'equivalently' is proved)."],
  "questions": []},
 {"label": "ex:consider_carthesian_coordinates_usual", "tex_lines": [1214, 1260], "status": "partial", "marked": False,
  "decls": ["GX.cartS₁", "GX.cartS₂", "GX.IsHomTrivial", "GX.IsHomTrivial.almostTrivial", "GX.IsHomTrivial.almostTrivialCC", "GX.carthesian_S₁_trivial", "GX.CartPiOneZ", "GX.carthesian_piOne_S₁", "GX.carthesian_piOne_S₁_at", "GX.cartDeg", "GX.cartDeg_bijective", "GX.carthesian_piOne_S₂", "GX.cartHE", "GX.cartKappa", "GX.cartLambda", "GX.cartΦ", "GX.cartR", "GX.cartYp", "GX.fgMulEquivOfHomotopyEquiv", "GX.cartDeg₂", "GX.cartDeg₂_mk", "GX.carthesian_S₂_almostTrivial", "GX.cart_middle_homotopic", "GX.cartCirc", "GX.cWinding_cartCirc", "GX.isPathConnected_ball_diff_cartS₂", "GX.cartLoopSubgroup", "GX.carthesian_S₂_not_trivial", "GX.not_isHomTrivial_cartγ", "GX.cartγ", "GX.cartγ_memOmega", "GX.cartPl", "GX.cartAp", "GX.cartAm", "GX.cartPsi", "GX.cartF₀", "GX.cartW", "GX.cartPsiW", "GX.cartFW", "GX.cartM", "GX.wind_const_family", "GX.sgnDist", "GX.continuousOn_sgnDist"],
  "hypotheses": [],
  "sorries": ex_sorries,
  "findings": [
    "l.1216: S2 is printed as {y = sin(1/x)} union a segment, which in R^3 is a surface (z free); read with z = 0 on the graph (the planar topologist's sine curve), as the proof's 'plane {z=0}' and claim 1 require",
    "l.1243-1244: H'(s,t) = (0, lambda_s t, 0) lies on the segment of S2; with gamma(t) = (0,0,t) near the ends it should read (0, 0, lambda_s t) and (0, 0, -lambda_s t)",
    "l.1218: 'The isomorphism is given by the number of turns around S_i' — for S1 this is GX.cartDeg (winding of y + iz), proved bijective",
    "l.1229-1257 (fourth claim): the mod 2 intersection numbers can be replaced by windings around 0 of psi + i z, psi a signed distance to the planar curve P: globally psi > 0 above P; locally psi* > 0 only on the finitely many pockets of A+ met at an intermediate time (they are cut off at x = 1/(pi/2 + 2 pi k) and x = -1/(3 pi/2 + 2 pi k), where sin(1/x) = 1). The winding of psi + i z along the reparametrised homotopy stays -pi, that of psi* + i z is +pi near the end of the homotopy, and the two agree at the intermediate time. Formalized as GX.not_isHomTrivial_cartγ for the loop t -> (0, 4 sin^2(pi t), sin(pi t) cos(pi t)) (it leaves O upwards over the limit segment, crosses z = 0 once at (0,4,0) in A+, and returns from below); the paper's normalisation through c (l.1236-1241) is replaced by an explicit frame reparametrisation (GX.cartM).",
    "l.1222: the paper's loop 'gamma(t) = (0,0,t) for t < 1/4' is not needed; any loop leaving O over the limit segment and crossing the plane only in A+ works",
    "l.1218, l.1224 ('left to the reader', first claim for S2): proof supplied by an explicit homotopy equivalence R^3 minus S2 ~ R^3 minus S1 (GX.cartHE): (x,y,z) -> (x, y + 2s psi/(|psi|+|z|), z) pushes the plane points above/below P off the strip R x [-1,1] x {0}, and the radial expansion (x,w) -> (x, (1 + s/|w|) w) of w = (y,z) maps R^3 minus S1 into the complement of that strip; the transfer to pi_1 is Mathlib's equivalence of fundamental groupoids",
    "l.1225-1228 (third claim): the paper's step 'Y minus closed B(S2,eps) is homeomorphic to Y minus S1' is not used; instead the middle of the loop is homotopic in Y minus S2 to a path of B minus S2 because pi_1(Y minus S2) = Z is generated by a small circle around an arc of S2 inside B (in the plane x = 1/(2 pi k)), and B minus S2 is path-connected (GX.cart_middle_homotopic)"],
  "questions": ["All four claims are proved, with no sorry, for S2 = (planar topologist's sine curve with its limit segment) x {0}, i.e. with z = 0 on the graph (GX.cartS₂). As printed (l.1216), {y = sin(1/x)} is a surface of R^3 (z free) and S2 is then not even closed; no ruling accepts the z = 0 reading yet, so the row is left partial and unmarked: does the author confirm S2 = {(x, sin(1/x), 0) : x != 0} union {x = z = 0, |y| <= 1}? If so the row is closed in full.", "Reading (g) (DEC-56): homotopically trivial = homotopic with fixed ends to the constant loop through loops of Omega(O,O,U), the constant loop reached only at the end (GX.IsHomTrivial)."]},
 {"label": "def:almost_homotopic_paths", "tex_lines": [1262, 1266], "status": "closed", "marked": True,
  "decls": ["GX.AlmostHomotopicCC", "GX.AlmostHomotopicCC.mem", "GX.MemOmega.of_loop", "GX.AlmostHomotopic", "GX.AlmostHomotopic.almostHomotopicCC", "GX.AlmostHomotopicCC.almostHomotopic", "GX.almostHomotopicCC_iff"],
  "hypotheses": [{"paper": "X Hausdorff, LPC; U open; (x,y) in U x closure U", "here": "weakened", "note": "not used; x in U is forced by the definition (GX.AlmostHomotopicCC.mem)"}],
  "sorries": [], "findings": [], "questions": []},
 {"label": "rem:implicitely_two_almost_homotopic", "tex_lines": [1268, 1269], "status": "closed", "marked": True,
  "decls": ["GX.AlmostHomotopicCC.ends", "GX.AlmostHomotopic.ends"], "hypotheses": [], "sorries": [], "findings": [], "questions": []},
 {"label": "lem:almost_homotopic_carac", "tex_lines": [1271, 1289], "status": "partial", "marked": False,
  "decls": ["GX.almost_homotopic_carac_cc", "GX.AlmostTrivialCC.of_carac", "GX.almost_homotopic_carac", "GX.splice", "GX.AlmostTrivialAt.exists_mid", "GX.AlmostTrivial.exists_mid", "GX.AlmostTrivialAt.of_mid", "GX.splice_omegaHomotopic"],
  "hypotheses": [
    {"paper": "X Hausdorff, first countable, connected, LPC", "here": "weakened", "note": "LPC carried; Hausdorff, first countable, connected not used"},
    {"paper": "U open", "here": "carried", "note": ""},
    {"paper": "(absent)", "here": "strengthened", "note": "U semilocally simply connected, for (i) => (ii) only; (ii) => (i) holds with no hypothesis (GX.AlmostTrivialCC.of_carac)"}],
  "sorries": [],
  "findings": ["l.1277: item (ii) prints gamma_{|[0,t_0]} * omega * gamma_{|[t_1,t_0]}; the last factor is gamma_{|[t_1,1]}",
    "l.1278-1279: the proof of (i) => (ii) starts from 'a homotopy H from gamma to some path gamma_0 in Omega(x,x,V)', i.e. it uses the homotopy form of l.1201; under DEC-55 the component of gamma need not contain such a homotopy. The step is proved here when U is semilocally simply connected (GX.almostTrivialCC_iff), which covers every use of the lemma in the paper (U = Y minus S with Y minus S slsc); in general it is open."],
  "questions": ["Is U meant to be semilocally simply connected (as it is in theo:ramified_covering_path and lem:almost_homotopic_carac2), or should (i) => (ii) hold for every open U of a Hausdorff, first countable, connected, locally path-connected X? Reading (b): '*' as any parameterization is made concrete by GX.splice."]},
 {"label": "lem:hausdorff_first_countable_connected", "tex_lines": [1290, 1305], "status": "partial", "marked": False,
  "decls": ["GX.hausdorff_first_countable_connected_cc", "GX.almostHomotopicCC_refl", "GX.AlmostHomotopicCC.symm", "GX.AlmostTrivialCC.symm", "GX.AlmostHomotopicCC.trans", "GX.hausdorff_first_countable_connected", "GX.GermEquiv", "GX.almostHomotopic_iff_germEquiv"],
  "hypotheses": [
    {"paper": "X Hausdorff, first countable, connected, LPC; U open", "here": "weakened", "note": "LPC and U open carried (for transitivity); the rest not used"},
    {"paper": "y in closure U", "here": "weakened", "note": "not used; x in U carried"},
    {"paper": "(absent)", "here": "strengthened", "note": "U semilocally simply connected, for transitivity only; reflexivity and symmetry hold in general"}],
  "sorries": [],
  "findings": ["l.1298-1303: the proof's indices drift (gamma_2^{-1}*gamma_1 for gamma_2^{-1}*gamma_3, gamma_{2|[0,t_1]} for gamma_{2|[0,t_2]}, omega_3 for omega_2, t_0 for t_1); the argument is sound once corrected, for the homotopy form",
    "Under DEC-55 the proof rests on lem:almost_homotopic_carac (i) => (ii), established here for U semilocally simply connected (see that row)."],
  "questions": ["Same question as lem:almost_homotopic_carac: is U semilocally simply connected?"]},
 {"label": "lem:almost_homotopic_carac2", "tex_lines": [1306, 1321], "status": "partial", "marked": False,
  "decls": ["GX.almost_homotopic_carac2_cc", "GX.almost_homotopic_carac2_of_isMaximal_cc", "GX.almost_homotopic_carac2", "GX.almost_homotopic_carac2_of_isMaximal", "GX.maxBranched_existsUnique_lift", "GX.maxBranched_lifting", "GX.lift_end_eq_of_almostHomotopic", "GX.almostHomotopic_of_lift_end_eq", "GX.IsStandardNbhd", "GX.IsSpread.hasBasis_standardNbhd"],
  "hypotheses": [
    {"paper": "widetilde Y^S maximal possibly branched over S", "here": "strengthened", "note": "S skeletal and Y minus S semilocally simply connected, Y T2/LPC/first countable/connected: what widetilde Y^S needs to exist (prop:universality)"}],
  "sorries": [],
  "findings": ["l.1313, l.1318: 'standard neighborhood' is used but never defined in the paper (reading (c), DEC-56: GX.IsStandardNbhd)"],
  "questions": []},
 {"label": "theo:ramified_covering_path", "tex_lines": [1322, 1383], "status": "partial", "marked": False,
  "decls": ["GX.ramified_covering_path", "GX.omegaEnd_isBranchedCovering", "GX.OmegaSpace", "GX.OmegaRel", "GX.omegaRel_equivalence", "GX.OmegaQuot", "GX.omegaEnd", "GX.omegaLift", "GX.continuous_omegaLift_one", "GX.isOpenMap_omegaLift_one", "GX.surjective_omegaLift_one", "GX.omegaLift_one_eq_iff"],
  "hypotheses": [
    {"paper": "Y first countable, connected, LPC, Hausdorff; S skeletal", "here": "carried", "note": ""},
    {"paper": "(absent)", "here": "strengthened", "note": "Y minus S semilocally simply connected: used by the proof (l.1349 'Since Y minus S is semi-locally simply connected') and needed for widetilde Y^S to be defined"}],
  "sorries": [],
  "findings": ["l.1322: the statement omits 'Y minus S semilocally simply connected', which its proof uses at l.1349 and without which the maximal covering widetilde Y^S (built from the universal cover of Y minus S) is not available"],
  "questions": ["Reading (d): X carries the quotient of the compact-open topology of Omega, by the literal almost homotopy (GX.OmegaRel, an equivalence relation by GX.omegaRel_equivalence)."]},
 {"label": "def:covering_branched_two_paths", "tex_lines": [1385, 1388], "status": "closed", "marked": True,
  "decls": ["GX.PHomotopic", "GX.FreePath", "GX.pHomotopic_equivalence"], "hypotheses": [], "sorries": [], "findings": [],
  "questions": ["Reading (e), accepted by DEC-56."]},
 {"label": "prop:general_fiber_path", "tex_lines": [1390, 1397], "status": "closed", "marked": True,
  "decls": ["GX.general_fiber_path", "GX.PiOneP", "GX.piOnePMap", "GX.compOfClass", "GX.isCoveringMap_restrict_compl"],
  "hypotheses": [{"paper": "p a covering branched over S", "here": "weakened", "note": "possibly branched over a skeletal S (as the branching locus is); X LPC, Y T1, locally connected are standing assumptions (l.815, l.962)"}],
  "sorries": [], "findings": ["'left to the reader' (l.1383): proof supplied"],
  "questions": ["Readings (e), (f), accepted by DEC-56."]},
 {"label": "prop:general_fiber_path_universal", "tex_lines": [1399, 1406], "status": "closed", "marked": True,
  "decls": ["GX.general_fiber_path_universal", "GX.PiOneU", "GX.FreeHomotopic", "GX.piOneUMap", "GX.pHomotopic_of_freeHomotopic", "GX.freeHomotopic_of_pHomotopic"],
  "hypotheses": [{"paper": "Y first countable connected LPC Hausdorff; S skeletal; Y minus S slsc", "here": "carried", "note": ""}],
  "sorries": [], "findings": ["'left to the reader' (l.1383): proof supplied"],
  "questions": ["Readings (e), (f), accepted by DEC-56."]},
 {"label": "ex:consider_fiber_above_homeomorphic", "tex_lines": [1409, 1416], "status": "closed", "marked": True,
  "decls": ["GX.fiber_above_homeomorphic", "GX.fibS", "GX.fibD", "GX.isSkeletal_fibS", "GX.semilocallySimplyConnected_fibS", "GX.fibS_tower", "GX.countable_piOneU_fibD", "GX.infinite_fiber_piOneUMap_fibD", "GX.argLift_freeHomotopic", "GX.towerHomeomorph", "GX.prodNatPiHomeomorph", "GX.not_locallyCompactSpace_nat_pi"],
  "hypotheses": [{"paper": "Y = R^2", "here": "carried", "note": "as C; S skeletal and C minus S slsc are proved, not assumed"}],
  "sorries": [],
  "findings": ["l.1414: 'the natural map pi_1(a,D_{n+1}) -> pi_1(a,D_n) has an infinite fiber above every point' is asserted without proof; it is supplied",
    "l.1415: 'the result follows' also needs the sets pi_1(a,D_n) countable and pi_1(a,D_1) countable nonempty; the limit is pi_1(a,D_1) x N^N, homeomorphic to Z^N",
    "l.1409: 'answers positively Problem 10.8 of MR2198590' is bibliographic and not formalized"],
  "questions": []}
]
rep = {
 "package": "WP-27d",
 "files": ["scaffold/GXScaffold/Branched/Paths.lean"],
 "builds": True,
 "sorry_count": sorry_count,
 "labels": labels,
 "extra_decls": ["GX.eventually_homotopic_family", "GX.homotopic_cancel_ends", "GX.eventually_almostTrivialAt_iff", "GX.AlmostTrivialCC.almostTrivial", "GX.almostTrivialCC_iff", "GX.AlmostTrivialCC.symm", "GX.omegaPath", "GX.affI", "GX.subpath_eq_affI", "GX.sgnDist", "GX.continuousOn_sgnDist", "GX.sgnDist_pos", "GX.sgnDist_neg", "GX.sgnDist_zero", "GX.wind_const_family", "GX.div_mem_slitPlane_of_sameSign", "GX.squareExt_eq", "GX.arg_ofReal_mul_I", "GX.arg_neg_ofReal_mul_I"],
 "kb_proposals": [
  "Compact-open components vs homotopy classes of Omega(x,x,U): GX.almostTrivialCC_iff (Branched/Paths) proves the literal almost triviality equals the homotopy form when U is open and slsc in an LPC space; the tool is GX.eventually_homotopic_family (a continuous family of paths in an LPC slsc space is, near q0, homotopic to w0 * delta(q0) * w1 for any short end connections, by liftHomotopy in GX.UniversalCover) — reuse it for any 'nearby paths are homotopic' step",
  "Mod 2 intersection numbers of curves with a surface can be replaced by windings of psi + i z around 0, psi a signed distance (GX.sgnDist, continuous on G when W is open and G minus (P union W) is open), lifted along families by GX.wind_const_family (liftHomotopy for exp, constant winding when the ends are opposite)",
  "Under `open unitInterval`, a binder named σ (e.g. in ∃ σ τ : I) breaks parsing: σ is unitInterval.symm"],
 "notes": "Reworked from WP-26e (3 sorries). DEC-55: the paper's notions are GX.AlmostTrivialCC / GX.AlmostHomotopicCC; the homotopy forms keep the names GX.AlmostTrivial / GX.AlmostHomotopic because GXScaffold.Branched.Galois and GaloisExamples consume them (both still typecheck against the rebuilt module, checked with lake env lean); at graduation the master may rename (AlmostTrivialCC -> AlmostTrivial) once Galois is reworked. GX.OmegaRel is now the literal relation and GX.OmegaQuot a Quot (no setoid needed); GX.omegaSetoid was removed (it was used nowhere else). GX.AlmostTrivial.exists_mid is now a wrapper of GX.AlmostTrivialAt.exists_mid (per-neighbourhood form). The fourth S2 claim is closed (GX.carthesian_S₂_not_trivial). `lake build GXScaffold.Branched.Paths` succeeds rebuilding only this module."
}
open('/home/maxbrain/Dropbox/LeanArticles/lean-gx/campaign/WP-27d/REPORT.json','w').write(json.dumps(rep, indent=2, ensure_ascii=False))
