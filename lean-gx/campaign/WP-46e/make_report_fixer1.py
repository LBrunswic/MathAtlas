import json, re
base = '/home/maxbrain/Dropbox/LeanArticles/lean-gx/'
rep = json.load(open(base + 'campaign/WP-46e/REPORT.json'))
src = open(base + 'scaffold/GXScaffold/BTZ/Surgery.lean').read()
sorry_count = len(re.findall(r'^\s*sorry\b', src, re.M))
P = 'GX.E0Surgery.'
g3 = [P + 'SurgeryData.' + n for n in ['isCauchySurface_sigmaStar', 'cuspUp', 'cuspDown', 'futSide', 'pastSide',
      'cuspUp_subset', 'cuspDown_subset', 'eq_of_mem_spearSet', 'sigmaStar_subset_sides', 'mem_sigmaStar_of_sides',
      'mem_sides_of_notMem_S0', 'closure_futSide_subset', 'closure_pastSide_subset', 'eventually_other',
      'eventually_futSide', 'eventually_pastSide', 'eventually_eq_of_sigmaStar', 'exists_pastSide', 'exists_futSide',
      'isClosed_preimage_futSide', 'isClosed_preimage_pastSide', 'futSide_of_le', 'pastSide_of_le',
      'eq_of_forall_mem_sigmaStar']] + \
     [P + 'SpearSurgeryDatum.' + n for n in ['le_vert', 'graphPt_mem', 'mem_Jminus_of_le_τS', 'mem_Jplus_of_τS_le',
      'v_lt_fcoord_of_mem_graphSet', 'eventually_le_coord', 'mem_spearSet_iff', 'paperOfY_ginv',
      'continuousAt_height_ginv', 'not_interior_of_mem_closure', 'exists_bound_G_annulus', 'exists_lt_G_near_axis']] + \
     [P + 'cauchy_facts', P + 'exists_open_of_BTZ']
for d in g3:
    short = d.split('.')[-1]
    assert re.search(r'(theorem|def) (\S+\.)?' + re.escape(short) + r'\b', src), d
bridge = [P + 'isSpacelikeDiscGraph_of_isSpacelikeGraph', P + 'lem_intersect_number_compact_pointwise']
for d in bridge:
    assert d.split('.')[-1] in src
labels = []
for l in rep['labels']:
    l = dict(l)
    k = l['label']
    if 'rem:curve_spear' in k:
        l['status'] = 'partial'
        l['marked'] = False
        l['hypotheses'] = l['hypotheses'] + [
            {'paper': 'an inextendible causal curve of any E_{>=0}-manifold M, any (blunt) spear neighbourhood',
             'here': 'strengthened',
             'note': "M globally hyperbolic (used for the closedness of the spear in M, isClosed_image_spearY, and for Reg M's limit facts, regM_facts: closed J^{+-}, strong causality, compact diamonds in exists_tendsto_of_monotone / exists_tendsto_atBot_of_monotone, against Inextensible.not_tendsto_atTop/atBot); the spears are those of a SpearSurgeryDatum (the K-3 past end 'below Sigma*' is read against its cusp G). DEC-116 (d) accepts the K-3 reading of the curve hypotheses; it does not mention global hyperbolicity of M (WP-44e AUDIT-1 m1, WP-46e AUDIT-1 M1). The remark is used only inside Prop 2.17's proof, where M is GH."},
            {'paper': '(none)', 'here': 'removed',
             'note': 'the unused hypothesis _hS : IsE0C1SpacelikeCauchy M S of rem_curve_spear is DROPPED (WP-46e fixer; its one caller, regM_isCauchyComplete_of_C1, is updated). rem_curve_spear now takes hGH and the surgery data only.'}]
        l['findings'] = l['findings'] + [
            "WP-46e fixer (AUDIT-1 M1): the row returns to PARTIAL and UNMARKED. rem_curve_spear carries the added hypothesis 'M globally hyperbolic', which the proof genuinely uses; without it the spear need not be closed in M (B21 Def 2.1's frontier condition) and an inextensible curve of a non-strongly-causal Reg M need not avoid limits, so the GH-free statement is not a corollary of this proof. It closes if the master confirms that DEC-116 (d) covers GH M (the remark's only use, B21 l.1093, is inside Prop 2.17 where M is GH)."]
        l['questions'] = ["Does DEC-116 (d) cover the added hypothesis 'M globally hyperbolic' (and the spears being those of a surgery datum, i.e. carrying the cusp G against which the past end is read)? If yes, rem:curve_spear closes and is marked with no code change; the remark is used only inside Prop 2.17's proof, where M is GH."]
    elif 'lem:intersect_number_compact' in k:
        l['decls'] = l['decls'] + [d for d in bridge if d not in l['decls']]
        for h in l['hypotheses']:
            if h['paper'].startswith('Sigma a spacelike surface in S'):
                h['note'] = ("read POINTWISE (DEC-117 'spacelike pointwise'): IsSpacelikeGraph g R (Lemma 2.7 at every point 0 < r <= R) with the height continuous on the closed solid cylinder {r <= R} (Sigma the graph of a continuous tau_Sigma over the closed disc): GX.E0Surgery.lem_intersect_number_compact_pointwise. "
                             "The integrated form IsSpacelikeDiscGraph g R (height strictly increasing along the causal order on {r <= R}, axis included), which lem_intersect_number_compact takes, is IMPLIED by the pointwise one: GX.E0Surgery.isSpacelikeDiscGraph_of_isSpacelikeGraph (WP-46e fixer, AUDIT-1 m1: off the axis height_lt_of_le; from an axis point, Lemma 2.7 integrated along the straight segment of the development, which leaves the axis at once, its endpoint by continuity of the height). Inhabited by Lemma 2.6(i)'s disc (lem_curve_extension_i). [accepted: DEC-117 (spacelike pointwise)]")
        l['findings'] = l['findings'] + ["WP-46e fixer (AUDIT-1 m1): the bridge pointwise => integrated is PROVED (isSpacelikeDiscGraph_of_isSpacelikeGraph: IsSpacelikeGraph + height continuous on {r <= R} => IsSpacelikeDiscGraph; no axis hypothesis is needed, the height on the axis being tau - g(0,0)), and Lemma 2.9 is stated in the pointwise reading as lem_intersect_number_compact_pointwise. The DEC-117 tag now attaches to the pointwise reading itself."]
    elif 'lem:curve_extension (i)' in k:
        for h in l['hypotheses']:
            if h['paper'] == 'graph spacelike':
                h['note'] = ("read pointwise on each smooth domain (DEC-117 'spacelike pointwise', as Lemma 2.7 states for a piecewise smooth graph): each of the two pieces is IsSpacelikeGraph (delta > 0 at every 0 < r <= R; delta = 1 for the slice, delta >= 1 for the outer piece with M = 1 + B^2 + 5TR) [accepted: DEC-117 (spacelike pointwise)]. "
                             "PROVED IN ADDITION (a stronger conclusion, not a reading): over the closed disc, axis included, the integrated form IsSpacelikeDiscGraph (height continuous on {r <= R}, strictly increasing along the causal order), obtained as tau = min(M/R, piece) (isSpacelikeDiscGraph_of_min). For a single pointwise-spacelike piece the integrated form follows from the pointwise one (isSpacelikeDiscGraph_of_isSpacelikeGraph); for the min of two pieces it is isSpacelikeDiscGraph_of_min.")
        l['findings'] = l['findings'] + ["WP-46e fixer (AUDIT-1 m1): the DEC-117 tag is reworded: the hypothesis/conclusion read under DEC-117 is 'spacelike pointwise on each piece'; the integrated disc form is an additional proved conclusion."]
    elif 'prop:abs_max' in k:
        l['status'] = 'partial'
        l['marked'] = False
        l['sorries'] = []
        l['decls'] = l['decls'] + [d for d in g3 if d not in l['decls']]
        for h in l['hypotheses']:
            if h['paper'].startswith('E_A-manifold'):
                h['note'] = 'E0-manifolds only (A = {0}), T2, connected, second countable. This is the only hypothesis not covered by a ruling: the row is partial for it alone (0 sorry). gx uses Prop 2.17 / Cor 2.18 for E0-manifolds only (DEC-28, SCOPE B-16); DEC-116 (b) ruled the analogous E0-only scope for Lemmas 2.3/2.4.'
        l['findings'] = [f for f in l['findings'] if not f.startswith('WP-46e: DEC-117 executed')] + [
            "WP-46e fixer: (G3) PROVED, SurgeryData.isCauchySurface_sigmaStar, 0 sorry (new §5g). B21 l.1093's 'by Remark 2.12 and Corollary 2.11 applied in each spear neighborhood' is made precise without intersection numbers: Sigma* cuts Reg M into a future side futSide = (J^+(S) minus the spears) union {height G_i >= 0 in spear i} and a past side pastSide = (J^-(S) minus the spears) union {height G_i <= 0}. (i) They cover Reg M and meet exactly along Sigma* (S acausal; J^+(S) cap J^-(S) = S). (ii) Both are closed in Reg M: a point of a spear in the closure of the outside is on the head or on the shaft (the open {f > v, r < R} lies in the spear); the head lies strictly below S (tau <= v + R/2 < tau_S), and a shaft point of J^+(S) is above C (else it would be in J^-(S) cap J^+(S) = S), i.e. has height G >= 0 by C = C*; limits inside a spear by continuity of the height read through the chart inverse. (iii) Along a causal curve of Reg M the future side propagates forward and the past side backward (the chart reading of the curve near a point, eventually_le_coord, with Lemma 2.7's monotone height; a curve leaves a spear forward only through the shaft, where the point is in J^+(S), and backward only through the head, which is in J^-(S)); with (ii), futSide is a future set and pastSide a past set along the curve (IsClosed.Icc_subset_of_forall_mem_nhdsWithin). (iv) Every inextensible causal curve of Reg M (reparametrised over R) meets both sides: by Remark 2.12 (hrem) every spear component has a point below the cusp (its past end is on the head or at the axis, where G -> +infinity uniformly while tau is bounded above); a spear component missing futSide ends on the shaft below C, in J^-(S), because a component with tau unbounded climbs above the cusp, bounded on the annulus r >= r(start). A curve missing futSide therefore lies in J^-(S), its future tail lies in the compact diamond J^+(d 0) cap J^-(s) (s a cluster point in compact S), converges, to a point of Reg M (BTZ points precede), against inextensibility. A curve missing the spears and pastSide lies in J^+(S), its past tail converges to q; q in Reg M contradicts inextensibility, and a BTZ q in J^+(S) is inside a spear (exists_open_of_BTZ: the BTZ line through q meets S in a BTZ point s <= q, on the ray of the spear covering s; q != vertex since the vertex is in I^-(S)), against the curve missing the spears. (v) Existence by connectedness of R, uniqueness: two points of the curve on Sigma* bound a segment on both sides, hence in Sigma*, along which the curve is locally constant (S acausal outside the spears; inside, the height is strictly monotone in the chart and the rim point is on S).",
            "WP-46e fixer: with (G3), Prop 2.17's first assertion of record, regM_isCauchyComplete_of_C1, has NO sorry beneath it (axiom sweep: every one of the 298 declarations of the file is on [propext, Classical.choice, Quot.sound]). Corollary 2.11's counting is not used by the proof: the sides argument replaces it (Cor 2.11 itself is proved separately as cor_intersect_number).",
            "WP-46e: DEC-117 executed: the topological GX.E0Surgery.regM_isCauchyComplete and the not-owed smoothing GX.E0Surgery.exists_isE0C1SpacelikeCauchy (G0) are DELETED. GXScaffold.BTZ.AbsMax.prop_abs_max (AbsMax.lean l.2039) still calls the former and no longer typechecks (re-confirmed by the fixer against the new olean: the single error of lake env lean on AbsMax.lean). TRANSITIVELY, everything importing AbsMax does not build until it is repointed: GXScaffold.BTZ.Uniformization (the headline) and the GXScaffold root (scaffold/GXScaffold.lean). The fix is outside this package's write set and is a one-line change: retire AbsMax.prop_abs_max, or repoint it to E0Surgery.regM_isCauchyComplete_of_C1 / cor_abs_max_C1 (which AbsMax already has, and which Uniformization's proofs use). The master must sequence this before any make check (WP-46e AUDIT-1 m2)."]
        l['questions'] = ["Prop 2.17's first assertion is now proved with 0 sorry for E0-manifolds (A = {0}), under the accepted readings (Cauchy-compact = IsE0C1SpacelikeCauchy, DEC-107/117; Cauchy-maximal = IsE0CauchyMaximal, DEC-77 (c); Cauchy-complete = the induced length, DEC-31). Is the E0-only scope accepted (as DEC-116 (b) did for Lemmas 2.3/2.4; gx uses Prop 2.17 / Cor 2.18 only for E0-manifolds, DEC-28)? If yes the row closes and is marked with no code change."]
    labels.append(l)
rep['round'] = 'fixer round 1 (after AUDIT-1) on the WP-46e file'
rep['sorry_count'] = sorry_count
rep['builds'] = True
rep['labels'] = labels
rep['extra_decls'] = rep['extra_decls'] + [d for d in bridge + g3 if d not in rep['extra_decls']]
rep['kb_proposals'] = rep['kb_proposals'] + [
    "A non-compact Cauchy surface by two closed sides: if F, P are closed in the spacetime, cover it, meet exactly along Sigma, F propagates forward and P backward along causal curves (local chart statements + IsClosed.Icc_subset_of_forall_mem_nhdsWithin), and every inextensible curve meets both, then Sigma is Cauchy once a causal curve inside Sigma is locally constant (GX.E0Surgery.SurgeryData.isCauchySurface_sigmaStar, §5g of GXScaffold.BTZ.Surgery). No compactness of Sigma and no intersection numbers are needed.",
    "Reading a causal curve of M in an injective E0-chart near one of its points: GX.E0Surgery.SpearSurgeryDatum.eventually_le_coord gives, for s near t, e s = psi(u) with u in a prescribed open V and x <= u after t, u <= x before (le_of_causalCurve on the segment). With E0.calculus_le (r and f = tau - r/2 are nondecreasing along <=) a curve can leave a spear forward only through the shaft and backward only through the head.",
    "A BTZ point q with s <= q for some s in a set S: s is BTZ and in the S0-component of q (SingularFlatAxioms.Jminus_subset_component); combine with IsFullFutureBTZRay.exists_eq_of_line to put q on a spear ray (GX.E0Surgery.exists_open_of_BTZ).",
    "Pointwise spacelike (Lemma 2.7 off the axis) + height continuous on the closed cylinder already implies the integrated 'height strictly increasing along <= on {r <= R}, axis included' (GX.E0Surgery.isSpacelikeDiscGraph_of_isSpacelikeGraph): integrate along the straight segment of the development from the axis point, which has r = s r(y) > 0 for s > 0."]
rep['notes'] = ("WP-46e FIXER ROUND 1 (after AUDIT-1). Backup of the pre-fixer file: campaign/WP-46e/Surgery.fixer1.pre.lean.bak. Report generator: make_report_fixer1.py (applied on top of the WP-46e REPORT). "
    "CLOSED: (G3) SurgeryData.isCauchySurface_sigmaStar (new §5g, the two closed sides of Sigma* in Reg M; 0 sorry). The file now has 0 sorry; regM_isCauchyComplete_of_C1 (Prop 2.17's first assertion of record) is sorry-free. "
    "AUDIT-1 M1 (major): rem_curve_spear's unused _hS is dropped (signature change; its only caller is in this file), its added hypothesis 'M globally hyperbolic' (+ the spears of a surgery datum) is listed as 'strengthened', and the row returns to PARTIAL/UNMARKED with a question asking whether DEC-116 (d) covers GH M. "
    "AUDIT-1 m1: the bridge isSpacelikeDiscGraph_of_isSpacelikeGraph (pointwise IsSpacelikeGraph + height continuous on {r <= R} => IsSpacelikeDiscGraph) is PROVED, and Lemma 2.9 is restated in the pointwise reading as lem_intersect_number_compact_pointwise; Lemma 2.6(i)'s tag is reworded (pointwise per piece is the reading; the disc form is an extra conclusion). "
    "AUDIT-1 m2: DOWNSTREAM BREAK, stated in full: AbsMax.lean l.2039 (AbsMax.prop_abs_max calls the deleted E0Surgery.regM_isCauchyComplete) fails, and therefore GXScaffold.BTZ.Uniformization (headline) and the GXScaffold root do not build until AbsMax.prop_abs_max is retired or repointed to regM_isCauchyComplete_of_C1 / cor_abs_max_C1. The master must fix AbsMax before any make check. No other file uses rem_curve_spear or isCauchySurface_sigmaStar (grepped). "
    "AUDIT-1 m3: `omit [SecondCountableTopology M] in` added before isSpacelikeLipschitz_sigmaStar; both ContinuousLinearMap.sub_apply uses replaced by sub_apply. lake env lean on the file now prints NO warning at all. "
    "prop:abs_max moves stated -> PARTIAL (0 sorry): its only uncovered hypothesis is the E0-only scope (A = {0}); question to the master. "
    "Build: taskset -c 0-11 lake build GXScaffold.BTZ.Surgery — success (8732 jobs), only Surgery rebuilt (40 s). Axiom sweep regenerated: campaign/WP-46e/Axioms.lean -> axioms.out, 298 declarations, every one on [propext, Classical.choice, Quot.sound] (one has no axiom), no sorryAx anywhere. "
    "Imports unchanged (DEC-33: only Causal.Flat.CauchyComplete; no open Causal; Causal.* names fully qualified). New names grepped against GX/ and scaffold/: the annulus bound was renamed exists_bound_G_annulus to avoid sharing the short name of E0Surgery.exists_bound_annulus; no other clash. All eight label strings are in the first 4000 characters of the module docstring; six are marked (Lemma 2.6, 2.7, 2.8, 2.9, 2.10, Cor 2.11). "
    "PREVIOUS (WP-46e): " + rep['notes'])
json.dump(rep, open(base + 'campaign/WP-46e/REPORT.json', 'w'), indent=2, ensure_ascii=False)
print('sorry_count', rep['sorry_count'])
for l in rep['labels']: print(l['label'][:80], l['status'], l['marked'], len(l['decls']))
