import json, re, sys
base = '/home/maxbrain/Dropbox/LeanArticles/lean-gx/'
prev = json.load(open(base + 'campaign/WP-43b/REPORT.json'))
src = open(base + 'scaffold/GXScaffold/BTZ/Surgery.lean').read()
st = json.load(open(base + 'campaign/WP-44e/state.json'))
rep = {
  'package': 'WP-44e',
  'round': 'edits the WP-41j/WP-43b file under DEC-107',
  'files': ['scaffold/GXScaffold/BTZ/Surgery.lean'],
  'builds': st['builds'],
  'sorry_count': len(re.findall(r'^\s*sorry -- SORRY', src, re.M)),
  'labels': [],
  'extra_decls': prev['extra_decls'] + st['extra_decls'],
  'kb_proposals': prev['kb_proposals'] + st['kb_proposals'],
  'notes': st['notes'] + ' PREVIOUS (WP-43b): ' + prev['notes'],
}
for l in prev['labels']:
  l = dict(l)
  key = l['label']
  if key in st['label_updates']:
    u = st['label_updates'][key]
    for k, v in u.items():
      if k in ('decls_add',):
        l['decls'] = l['decls'] + [d for d in v if d not in l['decls']]
      elif k == 'findings_add':
        l['findings'] = l.get('findings', []) + v
      elif k == 'questions':
        l['questions'] = v
      else:
        l[k] = v
  rep['labels'].append(l)
json.dump(rep, open(base + 'campaign/WP-44e/REPORT.json', 'w'), indent=2, ensure_ascii=False)
print('sorry_count', rep['sorry_count'], 'labels', len(rep['labels']))
