import json, re
base = '/home/maxbrain/Dropbox/LeanArticles/lean-gx/'
prev = json.load(open(base + 'campaign/WP-44e/REPORT.json'))
src = open(base + 'scaffold/GXScaffold/BTZ/Surgery.lean').read()
sorry_count = len(re.findall(r'^\s*sorry -- SORRY', src, re.M))
dec = "DEC-117 (readings accepted: spacelike pointwise; C^1 on the strip; the strip as the domain of completeness; the K-3 curve hypotheses)"
new_g4a = ["GX.E0Surgery.SurgeryData.isSpacelikeLipschitzAt_cusp", "GX.E0Surgery.SurgeryData.isSpacelikeLipschitzAt_cusp_interior", "GX.E0Surgery.SurgeryData.isSpacelikeLipschitzAt_cusp_rim", "GX.E0Surgery.SpearSurgeryDatum.eventually_regChart", "GX.E0Surgery.SpearSurgeryDatum.eventually_atlasChart", "GX.E0Surgery.isSpacelikeLipschitzAt_of_coneZeroSet", "GX.E0Surgery.isSpacelikeLipschitzAt_of_coneZeroSet'", "GX.E0Surgery.exists_ball_isConeIncreasingOn", "GX.E0Surgery.fderiv_chartHeight_pos", "GX.E0Surgery.fderiv_nullHeight_pos", "GX.E0Surgery.exists_nullShift", "GX.E0Surgery.isConeIncreasingOn_nullShift", "GX.E0Surgery.continuousOn_nullShift", "GX.E0Surgery.nullShift_unique"]
new_g5 = ["GX.E0Surgery.SurgeryData.completeSpace_sigmaStar", "GX.E0Surgery.SurgeryData.completeSpace_sigmaStar_of_delta", "GX.E0Surgery.SurgeryData.ofReal_abs_logRad_sub_le_edist", "GX.E0Surgery.SurgeryData.logRad", "GX.E0Surgery.SurgeryData.abs_deriv_logRad_le", "GX.E0Surgery.SurgeryData.exists_lipschitzOnWith_logRad", "GX.E0Surgery.sq_le_minkQ_of_tangent", "GX.E0Surgery.sq_div_le_nullQ_of_tangent", "GX.E0Surgery.SpearSurgeryDatum.delta", "GX.E0Surgery.ae_of_local"]
labels = []
for l in prev['labels']:
    l = dict(l)
    k = l['label']
    if 'prop:abs_max' in k:
        l['status'] = 'stated'
        l['marked'] = False
        l['decls'] = [d for d in l['decls'] if d not in ('GX.E0Surgery.regM_isCauchyComplete', 'GX.E0Surgery.exists_isE0C1SpacelikeCauchy')] + new_g4a + new_g5
        l['hypotheses'] = [h for h in l['hypotheses']]
        for h in l['hypotheses']:
            if h['paper'] == 'Cauchy-compact':
                h['here'] = 'read (DEC-107, DEC-117)'
                h['note'] = 'of record: regM_isCauchyComplete_of_C1 with IsE0C1SpacelikeCauchy (B21 l.227: a compact C^1 spacelike Cauchy surface). The topological regM_isCauchyComplete and the smoothing (G0) exists_isE0C1SpacelikeCauchy are DELETED (DEC-117).'
        src_g3 = re.search(r'sorry -- SORRY\(prop:abs_max\): \(G3\)(.*)', src).group(1).strip()
        l['sorries'] = [{'decl': 'GX.E0Surgery.SurgeryData.isCauchySurface_sigmaStar', 'obstruction': '(G3)' + ' ' + src_g3}]
        l['findings'] = [f for f in l['findings'] if 'not part of this row' not in f and 'AbsMax.prop_abs_max / cor_abs_max still consume' not in f] + [
          "WP-46e: (G4a) PROVED. Interior (r < R): the flat chart of Reg M read in a spear chart is g • (sector chart of E0) near the point (SpearSurgeryDatum.eventually_regChart: psi is locally a groupoid element, e0_flat_transition_aux, and an a.e.-atlas chart is g • a sector chart, btz_chart_eq_smul_btzPaperDev), so the chart picture of Sigma* is the zero set of the height chartHeight G g, C^1 with derivative positive on the closed future cone at the point (Lemma 2.7 in null coordinates: on the graph tau = G(r, theta), ds^2(w) = graphQuad(u) - 2 lambda w_r for w = lambda d_tau + u, fderiv_nullHeight_pos), hence c-cone-increasing on a ball for some c < 1 (exists_ball_isConeIncreasingOn: Riesz and the mean value theorem), and Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet concludes. Rim (r = R): in the frame g1 in which S is locally the graph of a c1-Lipschitz u (hS.reg), the function equal to the cusp height on {r <= R} and to the null-shift height sigma of S along the developed d_tau on {r > R} (exists_nullShift, by the intermediate value theorem; cone-increasing and Lipschitz) is continuous, because the two agree on the cylinder r = R (shifting along d_tau stays on the cylinder, where the cusp and S meet each tau-line at the same point, C = C*), and cone-increasing (a segment crossing the cylinder is cut at a crossing point); its zero set is Sigma* (the cusp inside the spear, S outside all spears). No implicit function theorem is needed.",
          "WP-46e: (G5) PROVED, by B21 Lemma 2.8's log r estimate (l.799-806) transported to the glued surface: for each spear the clamped log-radius log(min(r, R/2)) is 1-Lipschitz for the induced length of Sigma* (SurgeryData.ofReal_abs_logRad_sub_le_edist: along a path Lipschitz in charts, a.e. |d/dt log r| <= density, by Rademacher in a chart near each time, and on the cusp below R/2 the tangent bound ds^2 >= (dr/r)^2 from delta >= 1/r^2, sq_le_minkQ_of_tangent; where the clamp is active the function is locally constant or has a local maximum). A Cauchy sequence therefore stays in T = (S minus spears) union the graphs of the G_i over rho_i <= r <= R_i, which is compact (closed: a limit point of S minus spears on a spear is on the rim, an interior point having an open neighbourhood inside the spear); a subsequence converges in M, hence in Sigma* with its subspace topology, hence for the induced length (Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm). No path lifting to the strip is needed.",
          "WP-46e: SpearSurgeryDatum gains the field delta (delta >= 1/r^2 for the cusp on {r > 0}, Lemma 2.8(1)'s hypothesis with C = 1), which lem_curve_extension_ii's construction already had; lem_curve_extension_ii_shift now exports it (one more conjunct at the end) and exists_spearSurgeryDatum / exists_shrink pass it. Nothing outside this file uses either.",
          "WP-46e: DEC-117 executed: the topological GX.E0Surgery.regM_isCauchyComplete and the not-owed smoothing GX.E0Surgery.exists_isE0C1SpacelikeCauchy (G0) are DELETED. GXScaffold.BTZ.AbsMax.prop_abs_max (AbsMax.lean l.2039) still calls the former and no longer typechecks (the only error of lake env lean on AbsMax.lean against the new Surgery olean); it must be retired (or repointed to regM_isCauchyComplete_of_C1 via cor_abs_max_C1, which AbsMax already has) by the package owning AbsMax.",
        ]
        l['questions'] = []
    else:
        l['status'] = 'closed'
        l['marked'] = True
        l['questions'] = []
        for h in l.get('hypotheses', []):
            if h['here'] in ('read', 'read (K-3)', 'read (SCOPE K-3)', 'strengthened'):
                h['note'] = h['note'] + ' [accepted: ' + ('DEC-116 (d)' if 'curve_spear' in k else dec) + ']'
        l['findings'] = l.get('findings', []) + ['WP-46e: the reading this row rested on is accepted (' + ('DEC-116 (d)' if 'curve_spear' in k else 'DEC-117') + '); the row is closed and marked.']
    labels.append(l)
rep = {
  'package': 'WP-46e',
  'round': 'edits the WP-41j/WP-43b/WP-44e file under DEC-116 (d) and DEC-117',
  'files': ['scaffold/GXScaffold/BTZ/Surgery.lean'],
  'builds': True,
  'sorry_count': sorry_count,
  'labels': labels,
  'extra_decls': prev['extra_decls'] + [d for d in new_g4a + new_g5 if d not in prev['extra_decls']] + [
    "GX.E0Surgery.norm_comp_inr_lt_of_pos", "GX.E0Surgery.apply_ge_of_split", "GX.E0Surgery.nullHeight", "GX.E0Surgery.nullHeightExpl", "GX.E0Surgery.nullHeight_eq", "GX.E0Surgery.contDiffOn_nullHeight", "GX.E0Surgery.covector_pos", "GX.E0Surgery.surgery_aeChart_eventually_chartMap", "GX.E0Surgery.isom_smul_eq_add", "GX.E0Surgery.hasFDerivAt_isom_act", "GX.E0Surgery.contDiff_isom_smul", "GX.E0Surgery.chartHeight", "GX.E0Surgery.chartNull", "GX.E0Surgery.hasFDerivAt_chartHeight", "GX.E0Surgery.hasFDerivAt_chartNull_rad", "GX.E0Surgery.lipschitzWith_chartNull_rad", "GX.E0Surgery.tauDir", "GX.E0Surgery.chartMap_shift", "GX.E0Surgery.lorentz_apply_pos", "GX.E0Surgery.abs_log_sub_log_le", "GX.E0Surgery.SpearSurgeryDatum.mem_S0_iff'", "GX.E0Surgery.SpearSurgeryDatum.coord_mem_graphSet", "GX.E0Surgery.SpearSurgeryDatum.continuousAt_ginv_comp", "GX.E0Surgery.SurgeryData.logRad_le", "GX.E0Surgery.SurgeryData.eventually_logRad_const", "GX.E0Surgery.SurgeryData.eventually_logRad_formula", "GX.E0Surgery.SpearSurgeryDatum.isCompact_annulusGraph", "GX.E0Surgery.regChart_apply_eq", "GX.E0Surgery.mem_regChart_source_iff"],
  'kb_proposals': prev['kb_proposals'] + [
    "A spacelike graph is spacelike Lipschitz without any implicit function theorem: its height F (C^1, dF positive on the closed future cone at p0) is c-cone-increasing on a ball for c = (|dF o inr| + dF(1,0))/(2 dF(1,0)) < 1 (Riesz for |dF o inr| < dF(1,0), then the mean value theorem on segments), and Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet makes its zero set a Lipschitz graph (GX.E0Surgery.exists_ball_isConeIncreasingOn).",
    "IsSpacelikeLipschitzIn admits a frame: prove cone-increase of F o g^-1 on g • W in whatever frame g is convenient (e.g. the frame of another surface's Lipschitz graph), then move back with IsSpacelikeLipschitzIn.smul isom_strongMorphism (GX.E0Surgery.isSpacelikeLipschitzAt_of_coneZeroSet').",
    "Gluing two spacelike hypersurfaces along a cylinder ruled by null lines: use heights measured ALONG that null direction (the null-shift height of a Lipschitz graph, GX.E0Surgery.exists_nullShift, is cone-increasing and Lipschitz with no regularity), so they agree on the cylinder and the piecewise height is continuous and cone-increasing (cut segments at a crossing point).",
    "In E0, d_tau develops to a constant null vector: btzPaperDev (tau - s, r, theta) = btzPaperDev (tau, r, theta) - s • nullToMink (2, 0, 0) (GX.E0Surgery.chartMap_shift), so tau-shifts are translations in every flat chart.",
    "Completeness of an induced length by a Lipschitz exhaustion: if a function F on S is 1-Lipschitz for edist (prove it pathwise with le_localLength_of_lipschitzOnWith: Rademacher in ONE chart near each time, localDensity_chartSys_eq to read the density there, ae_of_local to globalise) and its sublevel sets are compact, Cauchy sequences converge (Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm turns subspace convergence into length convergence). Clamp log r at R/2 so the function is locally constant near rims (GX.E0Surgery.SurgeryData.logRad).",
  ],
  'notes': ("WP-46e edits scaffold/GXScaffold/BTZ/Surgery.lean (backup of the pre-package file: campaign/WP-46e/Surgery.pre.lean.bak; report generator make_report.py). "
    "CLOSED: (G4a) SurgeryData.isSpacelikeLipschitzAt_cusp (new §5f: interior and rim cases), (G5) SurgeryData.completeSpace_sigmaStar (new §5f: the clamped log-radius estimate and the compact exhaustion). "
    "DELETED (DEC-117): the topological regM_isCauchyComplete and (G0) exists_isE0C1SpacelikeCauchy. "
    "OPEN: (G3) SurgeryData.isCauchySurface_sigmaStar, one tagged sorry, re-described in its tag (the sides of Sigma* in Reg M). "
    "Rows: Lemmas 2.6 (i)(ii), 2.7, 2.8, 2.9, 2.10, Cor 2.11 and Remark 2.12 move partial -> CLOSED and are MARKED (their readings are accepted by DEC-117 / DEC-116 (d)); prop:abs_max's first assertion stays 'stated' (only G3 left). "
    "Structure change: SpearSurgeryDatum gains the field delta (delta >= 1/r^2 on the cusp); lem_curve_extension_ii_shift gains a final conjunct exporting it; no other file uses either (grepped). No other existing statement changed. "
    "DOWNSTREAM BREAK (expected under DEC-117): GXScaffold.BTZ.AbsMax.prop_abs_max (AbsMax.lean:2039) calls the deleted E0Surgery.regM_isCauchyComplete; lake env lean AbsMax.lean reports that single error. The package owning AbsMax must retire prop_abs_max (its C^1 replacement cor_abs_max_C1 already exists and Uniformization uses only that). "
    "Build: taskset -c 0-11 lake build GXScaffold.BTZ.Surgery — success (8732 jobs), only Surgery rebuilt. lake env lean on the file: 1 'declaration uses sorry' (G3); remaining warnings are linter-only (two deprecated ContinuousLinearMap.sub_apply uses; unused section variables, e.g. SecondCountableTopology now unused by the pre-existing isSpacelikeLipschitz_sigmaStar, whose signature was left unchanged). "
    "Axiom sweep: campaign/WP-46e/Axioms.lean -> axioms.out (every declaration of the file, 259): sorryAx only in SurgeryData.isCauchySurface_sigmaStar and the composition regM_isCauchyComplete_of_C1; (G4a), (G5), Remark 2.12 and all the Lemma rows are on [propext, Classical.choice, Quot.sound]. "
    "Imports unchanged (DEC-33: Causal.* names fully qualified, no open Causal). New names grepped against GX/ and scaffold/: GX.hasFDerivAt_isom_smul exists in GX/BTZ/Model.lean, so the new lemma is named hasFDerivAt_isom_act; no other clash. "
    "All eight label strings are in the first 4000 characters of the module docstring. "
    "PREVIOUS (WP-44e): " + prev['notes']),
}
json.dump(rep, open(base + 'campaign/WP-46e/REPORT.json', 'w'), indent=2, ensure_ascii=False)
print('sorry_count', rep['sorry_count'], 'labels', len(rep['labels']))
for l in rep['labels']: print(l['label'][:70], l['status'], l['marked'])
