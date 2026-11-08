import json
r = json.load(open('campaign/WP-46e/REPORT.json'))
acc = {'rem:curve_spear': 'DEC-125 (d) (Remark 2.12 with the added hypothesis M globally hyperbolic)',
       'prop:abs_max': "DEC-125 (e) (Prop 2.16 and Prop 2.17's first assertion for E0 only, A = {0})"}
for l in r['labels']:
    for k, dec in acc.items():
        if k in l['label']:
            l['status'] = 'closed'; l['marked'] = True
            for h in l['hypotheses']:
                if h['here'] == 'strengthened':
                    h['here'] = 'read'
                    h['note'] += f' [accepted: {dec}]'
            l['findings'].append(f'WP-47c: the reading this row rested on is accepted by {dec}; the row is closed and marked, docstrings only (no code change; 0 sorry; axioms propext/Classical.choice/Quot.sound, campaign/WP-47c/axioms.out).')
            l['questions'] = []
r['package'] = 'WP-47c'
r['round'] = 'DEC-125 (d)(e) application on the strict file (docstrings and REPORT only)'
r['previous'] = 'campaign/WP-46e/'
r['files'] = ['GX/BTZ/Surgery.lean']
r['builds'] = True
r['sorry_count'] = 0
r['notes'] = ("WP-47c edits the STRICT file GX/BTZ/Surgery.lean (module GX.BTZ.Surgery), docstrings only; backup "
  "campaign/WP-47c/Surgery.pre.lean.bak; report generator make_report.py (applied on top of campaign/WP-46e/REPORT.json). "
  "Under DEC-125 (d) brunswic2021cauchy:rem:curve_spear (GX.E0Surgery.rem_curve_spear, M globally hyperbolic) and under "
  "DEC-125 (e) brunswic2021cauchy:prop:abs_max, first assertion (GX.E0Surgery.regM_isCauchyComplete_of_C1, E0 only, A = {0}) "
  "move partial -> CLOSED and are MARKED in the module docstring; their hypothesis-checklist rows now read 'read (DEC-125 ...)'; "
  "the two declarations' docstrings cite the ruling. SCOPE (e)'s stale sentence (AbsMax/Uniformization/GXScaffold not "
  "building because AbsMax.prop_abs_max named the deleted regM_isCauchyComplete) is replaced: AbsMax has retired its "
  "topological route (prop_abs_max_C1 / cor_abs_max_C1); new SCOPE (f) records WP-47c. All 8 label strings are marked and in "
  "the first 4000 characters of the module docstring (offsets 1564..3384). No declaration, signature or proof changed; no "
  "name added. Checks: taskset -c 0-11 lake env lean -DwarningAsError=true GX/BTZ/Surgery.lean — clean, no output; "
  "taskset -c 0-11 lake build GX — success (8746 jobs, only GX.BTZ.Surgery and the GX root rebuilt; no Causal.* rebuilt). "
  "Axioms: campaign/WP-47c/Axioms.lean -> axioms.out, both certified decls on [propext, Classical.choice, Quot.sound]. "
  "PREVIOUS (WP-46e): " + r.get('notes', ''))
json.dump(r, open('campaign/WP-47c/REPORT.json', 'w'), indent=1, ensure_ascii=False)
print([(l['label'][:60], l['status'], l['marked']) for l in r['labels']])
