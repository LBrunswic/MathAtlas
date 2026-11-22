#!/usr/bin/env python3
"""Render the pattern-intersection chart (UpSet layout) as a self-contained HTML page."""
import json, html
runs = [('L10_g3', 'length ≤ 10, gaps ≤ 3'), ('L8_g4', 'length ≤ 8, gaps ≤ 4'), ('L14_g2', 'length ≤ 14, gaps ≤ 2')]
data = {k: json.load(open('data_%s.json' % k)) for k, _ in runs}
classes = [
  ('A', "w^a w′", "one growing block", "R1/WPow · decideR1", "proved"),
  ('B', "skeleton", "≥ 2 blocks, one shared exponent, equal slopes", "R1/Skel · R1 classification", "proved"),
  ('C', "tower", "(u^a v)^b y", "R1/Nested · R1/Tower", "proved"),
  ('D', "two exponents, same side", "u^a x v^b y, a, b independent, u and v on the same side of log₂3", "R1/TwoExp", "proved"),
  ('X', "two exponents, straddling", "u^a x v^b y, a, b independent, u and v on opposite sides", "R1/Straddle · decide_twoexp.py", "proved, conditional on Matveev"),
  ('E', "few descents", "≤ 2 gaps ≥ 2 (m-cycle, m ≤ 2)", "Steiner · Simons–de Weger", "literature"),
  ('F', "balanced", "Christoffel-type balanced", "Knight (Christoffel.lean)", "proved"),
]
payload = json.dumps({'runs': runs, 'data': data, 'classes': classes})
page = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>Pattern intersections — Syracuse gap words</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
.viz-root{color-scheme:light;--surface-1:#fcfcfb;--page:#f9f9f7;--text-primary:#0b0b0b;--text-secondary:#52514e;
 --muted:#898781;--grid:#e1e0d9;--axis:#c3c2b7;--series-1:#2a78d6;--dot-off:#e1e0d9}
@media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .viz-root{color-scheme:dark;--surface-1:#1a1a19;
 --page:#0d0d0d;--text-primary:#f0efec;--text-secondary:#c3c2b7;--muted:#898781;--grid:#2c2c2a;--axis:#383835;--series-1:#3987e5;--dot-off:#383835}}
:root[data-theme="dark"] .viz-root{color-scheme:dark;--surface-1:#1a1a19;--page:#0d0d0d;--text-primary:#f0efec;--text-secondary:#c3c2b7;
 --muted:#898781;--grid:#2c2c2a;--axis:#383835;--series-1:#3987e5;--dot-off:#383835}
html{background:#f9f9f7}@media (prefers-color-scheme:dark){html:not([data-theme="light"]){background:#0d0d0d}}html[data-theme="dark"]{background:#0d0d0d}html[data-theme="light"]{background:#f9f9f7}
body{margin:0}
.viz-root{font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif;color:var(--text-primary);background:var(--page);padding:24px;max-width:1100px;margin:auto}
h1{font-size:20px;margin:0 0 4px} .sub{color:var(--text-secondary);margin:0 0 16px}
.card{background:var(--surface-1);border:1px solid var(--grid);border-radius:8px;padding:16px 18px;margin-bottom:16px}
.filters{display:flex;gap:12px;align-items:center;margin-bottom:12px;color:var(--text-secondary)}
select{font:inherit;padding:4px 8px;border-radius:6px;border:1px solid var(--axis);background:var(--surface-1);color:var(--text-primary)}
.tiles{display:flex;gap:12px;flex-wrap:wrap}
.tile{flex:1;min-width:180px} .tile .v{font-size:28px;font-weight:600;font-variant-numeric:tabular-nums} .tile .l{color:var(--text-secondary)}
table.def{border-collapse:collapse;width:100%} table.def td,table.def th{padding:4px 8px;border-bottom:1px solid var(--grid);text-align:left;vertical-align:top}
table.def th{color:var(--text-secondary);font-weight:500}
.upset{display:grid;grid-template-columns:repeat(7,28px) 200px 1fr;column-gap:0;row-gap:2px;align-items:center}
.hdr{font-weight:600;text-align:center;color:var(--text-secondary);padding-bottom:4px}
.setsize{font-size:11px;color:var(--muted);text-align:center;font-variant-numeric:tabular-nums}
.cell{display:flex;justify-content:center;height:22px;align-items:center}
.dot{width:10px;height:10px;border-radius:50%;background:var(--dot-off)} .dot.on{background:var(--text-primary)}
.barwrap{position:relative;height:22px;border-left:1px solid var(--axis);margin-left:8px}
.bar{position:absolute;left:0;top:6px;height:10px;background:var(--series-1);border-radius:0 4px 4px 0;min-width:3px}
.wit{font:12px ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--text-secondary);padding-left:10px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.lab{position:absolute;top:2px;font-size:12px;color:var(--text-secondary);font-variant-numeric:tabular-nums;white-space:nowrap}
.row{display:contents} .row:hover .cell,.row:hover .barwrap{background:color-mix(in srgb,var(--series-1) 8%,transparent)}
.hit{cursor:default}
#tip{position:fixed;pointer-events:none;background:var(--surface-1);color:var(--text-primary);border:1px solid var(--axis);
 border-radius:6px;padding:8px 10px;font-size:12.5px;box-shadow:0 2px 10px rgba(0,0,0,.15);max-width:420px;display:none;z-index:10}
#tip .t{font-weight:600;margin-bottom:4px} #tip code{font-size:12px}
.cyc{color:var(--text-primary);font-weight:600}
details summary{cursor:pointer;color:var(--text-secondary)}
table.tbl{border-collapse:collapse;width:100%;font-size:12.5px} table.tbl td,table.tbl th{border-bottom:1px solid var(--grid);padding:3px 6px;text-align:left;vertical-align:top}
table.tbl td.n{text-align:right;font-variant-numeric:tabular-nums}
.note{color:var(--text-secondary);font-size:12.5px}
</style></head>
<body><div class="viz-root">
<h1>Pattern intersections of Syracuse gap words</h1>
<p class="sub">Each primitive cyclic gap word is tested against seven pattern classes (some rotation has the shape, growing exponents ≥ 2,
at most 4 letters of fixed material). Each row is one exact intersection region; hover a row for its shortest witnesses.</p>
<div class="card"><table class="def" id="defs"></table></div>
<div class="filters"><label for="run">Word range</label><select id="run"></select></div>
<div class="tiles"><div class="card tile"><div class="v" id="t-total"></div><div class="l">primitive cyclic words</div></div>
<div class="card tile"><div class="v" id="t-none"></div><div class="l">in no pattern class (the generic words)</div></div>
<div class="card tile"><div class="v" id="t-regions"></div><div class="l">nonempty intersection regions (of 127)</div></div></div>
<div class="card"><div class="upset" id="upset"></div>
<p class="note">Bars: number of words in exactly that region (the region “in no class” is shown in the tile above, not as a bar).
Filled dots mark the classes the region belongs to. The shortest witness of each region is listed beside it; hover a row for its decompositions, and the table below lists more witnesses.</p></div>
<div class="card"><details><summary>Table view: every region, its count and witnesses</summary><div id="tbl"></div></details></div>
<div id="tip" role="tooltip"></div>
</div>
<script>
const th = new URLSearchParams(location.search).get('theme'); if (th) document.documentElement.dataset.theme = th;
const P = __PAYLOAD__;
const cls = P.classes, letters = cls.map(c => c[0]);
const sel = document.getElementById('run');
P.runs.forEach(([k, lab]) => { const o = document.createElement('option'); o.value = k; o.textContent = lab; sel.appendChild(o); });
const defs = document.getElementById('defs');
defs.innerHTML = '<tr><th></th><th>class</th><th>shape</th><th>what covers it</th><th>status</th></tr>' +
  cls.map(c => `<tr><td><b>${c[0]}</b></td><td>${c[1]}</td><td>${c[2]}</td><td>${c[3]}</td><td>${c[4]}</td></tr>`).join('');
const tip = document.getElementById('tip');
function regionName(k) { return k ? k.split('').join(' ∩ ') + ' only' : 'in no class'; }
function wit(r) { return r.w.join(','); }
function render() {
  const D = P.data[sel.value], R = D.regions;
  const keys = Object.keys(R).filter(k => k !== '').sort((a, b) => R[b].count - R[a].count || a.localeCompare(b));
  const total = Object.values(R).reduce((s, v) => s + v.count, 0);
  const none = (R[''] || {count: 0}).count;
  document.getElementById('t-total').textContent = total.toLocaleString();
  document.getElementById('t-none').textContent = none.toLocaleString() + ' (' + Math.round(100 * none / total) + '%)';
  document.getElementById('t-regions').textContent = keys.length;
  const max = Math.max(...keys.map(k => R[k].count));
  const up = document.getElementById('upset'); up.innerHTML = '';
  letters.forEach(l => { const d = document.createElement('div'); d.className = 'hdr'; d.textContent = l; d.title = cls.find(c => c[0] === l)[1]; up.appendChild(d); });
  up.appendChild(Object.assign(document.createElement('div'), {className: 'hdr', style: 'text-align:left;padding-left:10px', textContent: 'shortest witness'}));
  up.appendChild(Object.assign(document.createElement('div'), {className: 'hdr', style: 'text-align:left;padding-left:12px', textContent: 'words in region'}));
  letters.forEach(l => { const n = keys.filter(k => k.includes(l)).reduce((s, k) => s + R[k].count, 0);
    up.appendChild(Object.assign(document.createElement('div'), {className: 'setsize', textContent: n})); });
  up.appendChild(Object.assign(document.createElement('div'), {className: 'setsize', style: 'text-align:left;padding-left:10px', textContent: '← class sizes'}));
  up.appendChild(document.createElement('div'));
  keys.forEach((k, i) => {
    const row = document.createElement('div'); row.className = 'row';
    letters.forEach(l => { const c = document.createElement('div'); c.className = 'cell hit';
      c.innerHTML = `<div class="dot${k.includes(l) ? ' on' : ''}"></div>`; row.appendChild(c); });
    const wt = document.createElement('div'); wt.className = 'wit hit'; wt.textContent = R[k].witnesses[0].w.join(',');
    row.appendChild(wt);
    const bw = document.createElement('div'); bw.className = 'barwrap hit';
    const pct = 100 * R[k].count / max;
    bw.innerHTML = `<div class="bar" style="width:calc(${pct}% - 40px)"></div>` +
      `<div class="lab" style="left:calc(max(${pct}% - 40px, 3px) + 6px)">${R[k].count}</div>`;
    row.appendChild(bw);
    [...row.children].forEach(el => {
      el.addEventListener('mousemove', e => {
        const r = R[k];
        tip.innerHTML = `<div class="t">${regionName(k)} — ${r.count} word${r.count > 1 ? 's' : ''}</div>` +
          r.witnesses.slice(0, 3).map(x => `<div><code>${wit(x)}</code>` +
            Object.entries(x.how).map(([c, h]) => `<br>&nbsp;&nbsp;${c}: <code>${h}</code>`).join('') + '</div>').join('') +
          (r.cycles.length ? `<div class="cyc">contains cycle words: ${r.cycles.map(w => w.join(',')).join('; ')}</div>` : '');
        tip.style.display = 'block';
        const x = Math.min(e.clientX + 14, window.innerWidth - tip.offsetWidth - 8);
        tip.style.left = x + 'px'; tip.style.top = (e.clientY + 14) + 'px';
      });
      el.addEventListener('mouseleave', () => { tip.style.display = 'none'; });
    });
    up.appendChild(row);
  });
  const allk = Object.keys(R).sort((a, b) => R[b].count - R[a].count);
  document.getElementById('tbl').innerHTML = '<table class="tbl"><tr><th>region</th><th>count</th><th>shortest witnesses (decompositions)</th><th>cycle words</th></tr>' +
    allk.map(k => `<tr><td>${regionName(k)}</td><td class="n">${R[k].count}</td><td>` +
      R[k].witnesses.slice(0, 3).map(x => `<code>${wit(x)}</code>` + (Object.keys(x.how).length ? ' — ' + Object.entries(x.how).map(([c, h]) => `${c}: <code>${h}</code>`).join('; ') : '')).join('<br>') +
      `</td><td>${R[k].cycles.map(w => w.join(',')).join('; ')}</td></tr>`).join('') + '</table>';
}
sel.addEventListener('change', render);
render();
</script></body></html>
'''
open('patterns_chart.html', 'w').write(page.replace('__PAYLOAD__', payload))
print('wrote patterns_chart.html', len(page))
