// Headless smoke test of the blueprint page: load it, click into a property, an implication, a pair,
// a transfer along a nesting, a counterexample with a conjunctive `from`, an open pair, a binder row
// and a roadmap target, at desktop and phone width, in both colour schemes; count page errors
// (uncaught exceptions). Exit 1 on any page error or on a click that does not open its panel.
// The page's ladder line against `tools/ladder.py check` is the Makefile's `agree`, not this file's.
//
// Implications are clicked where they are drawn: every segment of every implication (a single premise's
// arrow; a conjunction's segment per premise into its ∧ junction and the one out of it), on its line and
// 4 px beside it, plus every junction. The points come from the drawing's geometry alone (segmentPoints),
// never from the page's hit-testing, which is what is under test.
//
//   PLAYWRIGHT=<.../node_modules/playwright> node smoke.cjs index.html     (SHOTS=DIR keeps screenshots)
const path = require("path");
const pw = require(process.env.PLAYWRIGHT || "playwright");

const file = path.resolve(process.argv[2] || "index.html");
const shots = process.env.SHOTS || "";

async function run(browser, opts, label, steps) {
  const ctx = await browser.newContext(opts);
  const page = await ctx.newPage();
  const errors = [], consoleErrors = [], failed = [];
  page.on("pageerror", e => errors.push(String(e && e.message || e)));
  page.on("console", m => { if (m.type() === "error") consoleErrors.push(m.text()); });
  page.on("requestfailed", r => failed.push(r.url() + " " + (r.failure() || {}).errorText));
  await page.goto("file://" + file, { waitUntil: "networkidle" });
  const out = { label, checks: [] };
  const check = async (what, fn) => {
    try { const v = await fn(); out.checks.push([what, "ok", v]); }
    catch (e) { out.checks.push([what, "FAIL", String(e.message || e).split("\n")[0]]); }
  };
  await steps(page, check, out);
  if (shots) await page.screenshot({ path: path.join(shots, `blueprint-${label}.png`) });
  Object.assign(out, { pageErrors: errors, consoleErrors, failedRequests: failed });
  await ctx.close();
  return out;
}

const panelH2 = page => page.locator("#panel h2").first().innerText();
const OFF = 4;   // px beside the drawn line: a click as a reader makes it, not a pixel-exact one

/* In the page: for each drawn segment of each implication, the point of its line (or `off` px beside it,
   along the normal) farthest from every other implication's line, outside every node, other junction
   and other `under` label, inside the visible graph and under no HTML overlay (zoom tools, legend).
   `clr` is that point's distance in px to the nearest other implication's line; with `hi`, only points
   with clr <= hi count (a point inside another implication's hit area). */
function segmentPoints(off, hi = Infinity) {
  const world = document.querySelector("#world"), svg = world.ownerSVGElement, sr = svg.getBoundingClientRect();
  const k = world.getScreenCTM().a, step = Math.max(0.5, 1.5 / k);
  const scr = (el, p) => new DOMPoint(p.x, p.y).matrixTransform(el.getScreenCTM());
  const segs = [...world.querySelectorAll(".edge")].map(g => {
    const p = g.querySelector("path.vis"), n = p.getTotalLength(), pts = [];
    for (let d = 0; d <= n; d += step) pts.push(scr(p, p.getPointAtLength(d)));
    return { g, i: +g.dataset.i, p, n, pts }; });
  const own = el => +(el.closest(".edge, .junction") || { dataset: { i: -1 } }).dataset.i;
  const boxes = [...world.querySelectorAll(".node, .junction, .edge text")].map(el => ({ i: el.matches(".node") ? -1 : own(el), r: el.getBoundingClientRect() }));
  const right = Math.min(sr.right, innerWidth) - 2, bottom = Math.min(sr.bottom, innerHeight) - 2;
  return segs.map(S => {
    const others = segs.filter(o => o.i !== S.i).flatMap(o => o.pts), bx = boxes.filter(b => b.i !== S.i);
    let best = null;
    for (let t = 0.08; t <= 0.921; t += 0.01) {
      const a = scr(S.p, S.p.getPointAtLength(S.n * t)), b = scr(S.p, S.p.getPointAtLength(Math.min(S.n, S.n * t + 1))), c = scr(S.p, S.p.getPointAtLength(Math.max(0, S.n * t - 1)));
      const tx = b.x - c.x, ty = b.y - c.y, tl = Math.hypot(tx, ty) || 1;
      for (const sg of off ? [1, -1] : [0]) {
        const q = { x: a.x - sg * off * ty / tl, y: a.y + sg * off * tx / tl };
        if (q.x < sr.left + 2 || q.y < sr.top + 2 || q.x > right || q.y > bottom) continue;
        const top = document.elementFromPoint(q.x, q.y); if (!top || !svg.contains(top)) continue;
        if (bx.some(B => q.x > B.r.left - 6 && q.x < B.r.right + 6 && q.y > B.r.top - 6 && q.y < B.r.bottom + 6)) continue;
        let clr = Infinity; for (const o of others) clr = Math.min(clr, Math.hypot(o.x - q.x, o.y - q.y));
        if (clr <= hi && (!best || clr > best.clr)) best = { x: q.x, y: q.y, clr };
      }
    }
    return { i: S.i, seg: S.g.dataset.v + " → " + S.g.dataset.w, ...(best || { x: null }) };
  });
}
const implText = (page, i) => page.evaluate(i => { const e = DATA.ladder.implies[i]; return e.from.join(" ∧ ") + " ⇒ " + e.to; }, i);
/* Back to the ladder's overview (Escape), then click or tap (x, y): the panel's heading, once it is `want` or after 400 ms. */
const segmentPointsIn = (page, off, hi) => page.evaluate(`(${segmentPoints})(${off}, ${hi})`);
async function clickTo(page, x, y, want, tap) {
  await page.keyboard.press("Escape");
  await page.waitForFunction(() => location.hash === "#/ladder" && !document.querySelector("#panel h2.mono"), null, { timeout: 2000 });
  if (tap) await page.touchscreen.tap(x, y); else await page.mouse.click(x, y);
  await page.waitForFunction(w => { const h = document.querySelector("#panel h2"); return h && h.innerText === w; }, want, { timeout: 400 }).catch(() => {});
  return panelH2(page);
}
/* The open implication's panel against DATA: its witness, its `under` when it has one, its premises and conclusion. */
const edgePanel = page => page.evaluate(() => {
  const i = +decodeURIComponent(location.hash).split("/").pop(), e = DATA.ladder.implies[i], P = document.querySelector("#panel");
  const sec = name => { const h = [...P.querySelectorAll("h3")].find(h => h.textContent.trim() === name); return h && h.parentElement; };
  const bad = [], w = sec("Witness"), u = sec("under"), pr = sec("Premises and conclusion");
  if (!w || w.querySelector(".mono").textContent !== e.witness) bad.push("witness");
  if (e.under ? !u || u.querySelector("p").textContent !== e.under : !!u) bad.push("under");
  if (!pr || [...pr.querySelectorAll(".pl")].map(b => b.textContent).join("|") !== [...e.from, e.to].join("|")) bad.push("premises");
  if (bad.length) throw new Error("panel of " + e.from.join(" ∧ ") + " ⇒ " + e.to + " lacks " + bad.join(", "));
  return `witness ${e.witness}${e.under ? ", under" : ""}, ${e.from.length} premise(s)`; });
// the panel's heading once it differs from `before`
const nextH2 = async (page, before) => { await page.waitForFunction(b => { const h = document.querySelector("#panel h2"); return h && h.innerText !== b; }, before, { timeout: 5000 }).catch(() => {}); return panelH2(page); };
// the panel's heading once it is `want` (or after 5 s)
const toH2 = async (page, want) => { await page.waitForFunction(w => { const h = document.querySelector("#panel h2"); return h && h.innerText === w; }, want, { timeout: 5000 }).catch(() => {}); return panelH2(page); };
// the text of the panel section headed `name` (an h3, matched by its start)
const section = (page, name) => page.evaluate(n => { const h = [...document.querySelectorAll("#panel h3")].find(h => h.textContent.trim().toUpperCase().startsWith(n.toUpperCase())); return h ? h.parentElement.innerText : null; }, name);
/* The open transfer's panel against DATA: its title, its witness or counterexample, every id asked besides. */
const transferPanel = page => page.evaluate(() => {
  const k = +decodeURIComponent(location.hash).split("/").pop(), t = DATA.ladder.transfers[k], P = document.querySelector("#panel");
  const sec = name => { const h = [...P.querySelectorAll("h3")].find(h => h.textContent.trim() === name); return h && h.parentElement; };
  const bad = [], w = sec(t.kind === "witness" ? "Witness" : "Counterexample"), asked = sec("Asked besides");
  if (P.querySelector("h2").innerText !== transferTitle(t)) bad.push("title");
  if (!w || w.querySelector(".mono").textContent !== t.name) bad.push(t.kind);
  const got = asked ? [...asked.querySelectorAll(".pl")].map(b => b.textContent) : [];
  if (got.join("|") !== [...t.src, ...t.tgt].join("|")) bad.push("ids asked besides");
  if (bad.length) throw new Error("panel of transfer " + k + " lacks " + bad.join(", "));
  return `${transferTitle(t)}: ${t.name}, ${t.src.length} + ${t.tgt.length} ids asked besides`; });

(async () => {
  const browser = await pw.chromium.launch();
  const results = [];
  results.push(await run(browser, { viewport: { width: 1440, height: 900 }, colorScheme: "light" }, "desktop-light", async (page, check, out) => {
    out.counts = await page.evaluate(() => ({
      properties: DATA.ladder.props.length, nodesDrawn: document.querySelectorAll("#world .node").length,
      implications: DATA.ladder.implies.length, edgesDrawn: new Set([...document.querySelectorAll("#world .edge")].map(e => e.dataset.i)).size,
      within: DATA.ladder.summary.within, classified: DATA.ladder.summary.classified, illTyped: DATA.ladder.summary.ill_typed,
      impliedStanding: DATA.ladder.summary.implied_standing, transfers: DATA.ladder.transfers.length, violations: DATA.ladder.errors.length,
      consequences: DATA.ladder.cons.length, binders: DATA.binders.map(b => b.slug + ":" + b.rows.length).join(", "),
      targets: DATA.road.targets.length }));
    await check("the overview shows tools/ladder.py check's line and its violations", async () => {
      const [line, errs, shown] = await page.evaluate(() => [DATA.ladder.line, DATA.ladder.errors.length, document.querySelectorAll("#panel p.err").length]);
      const txt = await section(page, "tools/ladder.py check");
      if (!txt || !txt.includes(line)) throw new Error("the panel does not show " + line);
      if (shown !== errs) throw new Error(`${shown} violation(s) shown, ${errs} in DATA`);
      return line.replace(/^ladder: [^;]*; /, "") + ` (${errs} violation(s) shown)`; });
    const first = await page.evaluate(() => DATA.ladder.props.find(p => DATA.ladder.implies.some(e => e.from.includes(p.id)))?.id || DATA.ladder.props[0].id);
    await check("click property " + first, async () => {
      const before = await panelH2(page);
      await page.locator(`#world .node[data-id="${first}"]`).click();
      const h = await nextH2(page, before); if (h !== first) throw new Error("panel shows " + h); return h; });
    await page.click("#zfit");   // the whole ladder in view, as on load (selecting a property may have centred on it)
    for (const off of [0, OFF]) await check(`click every drawn segment of every implication ${off ? off + " px beside" : "on"} its line`, async () => {
      const pts = await segmentPointsIn(page, off, Infinity), miss = [], bad = [];
      for (const q of pts) {
        const want = await implText(page, q.i);
        if (q.x == null || q.clr < off + 3) { miss.push(want + " [" + q.seg + "]"); continue; }
        const h = await clickTo(page, q.x, q.y, want);
        if (h !== want) bad.push(`${want} [${q.seg}] at (${q.x.toFixed(0)},${q.y.toFixed(0)}) opened ${h}`);
      }
      if (miss.length) throw new Error("no clear point to click on " + miss.join("; "));
      if (bad.length) throw new Error(`${bad.length} of ${pts.length} clicks: ` + bad.slice(0, 3).join("; ") + (bad.length > 3 ? "; …" : ""));
      const n = await page.evaluate(() => DATA.ladder.implies.map(e => e.from.length > 1));
      const is = [...new Set(pts.map(q => q.i))];
      return `${pts.length} segments of ${is.length} implications (${is.filter(i => !n[i]).length} single-premise, ${is.filter(i => n[i]).length} conjunctive), each opened its own`; });
    await check("click on a line where another implication's hit area overlaps it: the nearer line wins", async () => {
      const pts = (await segmentPointsIn(page, 0, 6)).filter(q => q.x != null && q.clr >= 2.5), bad = [];
      for (const q of pts) { const want = await implText(page, q.i), h = await clickTo(page, q.x, q.y, want);
        if (h !== want) bad.push(`${want} [${q.seg}], another line ${q.clr.toFixed(1)} px away, opened ${h}`); }
      if (bad.length) throw new Error(`${bad.length} of ${pts.length} clicks: ` + bad.slice(0, 3).join("; "));
      return pts.length ? pts.length + " segments clicked within 6 px of another implication's line" : "no two lines that close in this drawing"; });
    await check("click every ∧ junction", async () => {
      const js = await page.evaluate(() => [...document.querySelectorAll("#world .junction")].map(j => { const r = j.getBoundingClientRect(); return { i: +j.dataset.i, x: r.x + r.width / 2, y: r.y + r.height / 2 }; }));
      if (!js.length) return "no conjunctive implication drawn";
      for (const j of js) { const want = await implText(page, j.i), h = await clickTo(page, j.x, j.y, want); if (h !== want) throw new Error(`junction of ${want} opened ${h}`); }
      return js.length + " junctions"; });
    for (const conj of [false, true]) await check(`${conj ? "a conjunctive" : "a single-premise"} implication's panel: witness, under, premises`, async () => {
      const i = await page.evaluate(c => { const I = DATA.ladder.implies, ok = e => (e.from.length > 1) === c;
        const j = I.findIndex(e => ok(e) && e.under); return j >= 0 ? j : I.findIndex(ok); }, conj);
      if (i < 0) return "none in the ladder";
      const q = (await segmentPointsIn(page, OFF, Infinity)).filter(q => q.i === i && q.x != null).sort((a, b) => b.clr - a.clr)[0], want = await implText(page, i);
      if (!q) throw new Error("no clear point to click on " + want);
      const h = await clickTo(page, q.x, q.y, want); if (h !== want) throw new Error("panel shows " + h);
      if (conj) { await page.mouse.move(q.x, q.y);   // one segment hovered: the whole implication lights up, nothing else
        const lit = await page.evaluate(i => [...document.querySelectorAll("#world .hov")].map(n => +n.dataset.i === i ? 1 : 0), i);
        const all = await page.evaluate(i => document.querySelectorAll(`#world .edge[data-i="${i}"], #world .junction[data-i="${i}"]`).length, i);
        if (lit.length !== all || lit.includes(0)) throw new Error(`hovering one segment lit ${lit.length} element(s), ${all} expected`);
        await page.mouse.move(2, 2); return want + ": " + await edgePanel(page) + `; hovering one segment lit its ${all - 1} segments and its junction`; }
      return want + ": " + await edgePanel(page); });
    await check("click a nesting, then a transfer along it", async () => {
      const X = await page.evaluate(() => DATA.ladder.props.find(p => (DATA.ladder.along[p.id] || []).length)?.id);
      if (!X) return "no transfer recorded";
      await page.keyboard.press("Escape"); await page.click("#zfit");
      await page.locator(`#world .node[data-id="${X}"]`).click();
      if (await toH2(page, X) !== X) throw new Error("the nesting's panel did not open");
      const b = page.locator('#panel button[data-go^="#/ladder/transfer/"]').first();
      const k = +(await b.getAttribute("data-go")).split("/").pop(), want = await page.evaluate(k => transferTitle(DATA.ladder.transfers[k]), k);
      await b.click(); const h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      return X + " -> " + await transferPanel(page); });
    await check("pairs view, click a classified cell", async () => {
      await page.click("#m-pairs");
      const before = await panelH2(page);
      await page.locator("#matrix td button.m-implied, #matrix td button.m-implied-standing").first().click();
      const h = await nextH2(page, before); if (!/⇒|⇏/.test(h)) throw new Error("panel shows " + h);
      out.matrixCells = await page.locator("#matrix table:not(.ttab) td button:not(.m-diag)").count();
      const within = await page.evaluate(() => DATA.ladder.summary.within);
      if (out.matrixCells !== within) throw new Error(`${out.matrixCells} cells drawn, tools/ladder.py counts ${within} pairs within one sort`);
      return h + ` (${out.matrixCells} cells, the ${within} pairs within one sort)`; });
    await check("pairs view, click a pair refuted by a counterexample with a conjunctive `from`", async () => {
      const q = await page.evaluate(() => { for (const [k, v] of Object.entries(DATA.ladder.pairs)) if (v.c === "fails" && DATA.ladder.fails[v.f].from.length > 1) { const [a, b] = k.split("|"); return {a, b, f:DATA.ladder.fails[v.f]}; } return null; });
      if (!q) return "no such counterexample";
      await page.locator(`#matrix td button[data-go="#/ladder/pair/${encodeURIComponent(q.a)}/${encodeURIComponent(q.b)}"]`).click();
      const want = `${q.a} ⇏ ${q.b}`, h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      const txt = await section(page, "Counterexample");
      const ids = await page.evaluate(() => { const h = [...document.querySelectorAll("#panel h3")].find(h => h.textContent.trim() === "Counterexample"); return [...h.parentElement.querySelector("li").querySelectorAll(".pl")].map(b => b.textContent); });
      if (!txt || !txt.includes(q.f.witness)) throw new Error("no witness " + q.f.witness);
      if (ids.join("|") !== [...q.f.from, q.f.to].join("|")) throw new Error("the counterexample lists " + ids.join(", "));
      return `${want}: ${q.f.witness}, a space with ${q.f.from.join(" ∧ ")} and without ${q.f.to}`; });
    await check("pairs view, an open pair shows its note", async () => {
      const c = page.locator("#matrix td button.m-open").first(); if (!(await c.count())) return "no open pair";
      const [, , , a, b] = decodeURIComponent(await c.getAttribute("data-go")).split("/"); await c.click();
      const want = `${a} ? ${b}`, h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      const note = await page.evaluate(([a, b]) => DATA.ladder.open.find(o => o.from === a && o.to === b).note, [a, b]);
      const txt = await section(page, "Recorded open"); if (!txt || !txt.includes(note)) throw new Error("the note is not shown");
      return `${want}: ${note.length} characters of note`; });
    await check("pairs view, click a transfer cell refuted by a counterexample", async () => {
      const c = page.locator("#ttab button.t-no:not(.thr)").first(); if (!(await c.count())) return "no counterexample in the transfer table";
      const k = +(await c.getAttribute("data-go")).split("/").pop(), want = await page.evaluate(k => transferTitle(DATA.ladder.transfers[k]), k);
      await c.click(); const h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      out.transferCells = await page.locator("#ttab td button").count();
      return await transferPanel(page) + ` (${out.transferCells} filled cells)`; });
    await check("an ill-typed pair says so", async () => {
      const q = await page.evaluate(() => { const k = Object.keys(DATA.ladder.pairs).find(k => DATA.ladder.pairs[k].c === "ill-typed"); return k ? k.split("|") : null; });
      if (!q) return "no two sorts";
      await page.evaluate(([a, b]) => { location.hash = `#/ladder/pair/${encodeURIComponent(a)}/${encodeURIComponent(b)}`; }, q);
      const want = `${q[0]} × ${q[1]}`, h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      const chip = await page.locator("#panel .chips .chip").first().innerText(); if (!/ill-typed/.test(chip)) throw new Error("chip " + chip);
      return want; });
    await page.click("#m-graph");
    await check("theme toggle: dark, then light, then back to auto", async () => {
      const bg = () => page.evaluate(() => getComputedStyle(document.documentElement).getPropertyValue("--bg").trim());
      const seen = [];
      for (let i = 0; i < 3; i++) { await page.click("#theme"); seen.push([await page.evaluate(() => document.documentElement.dataset.theme || "auto"), await bg()]); }
      const d = seen.find(x => x[0] === "dark"), l = seen.find(x => x[0] === "light");
      if (!d || !l || d[1] === l[1]) throw new Error("themes " + JSON.stringify(seen));
      if (seen[2][0] !== "auto") throw new Error("does not return to auto");
      return seen.map(x => x.join(" ")).join(", "); });
    await check("binders tab, click a row", async () => {
      await page.click("#tab-binders");
      const row = page.locator(".brow[data-go]").filter({ has: page.locator(".pl[data-go^='#/ladder/p/']") }).first();
      const lab = await row.getAttribute("data-go"), before = await panelH2(page);
      await row.click();
      const h = await nextH2(page, before); if (!(await page.locator("#panel .chips .mono").first().innerText()).length) throw new Error("no row label");
      const typeset = await page.waitForSelector("#tex mjx-container", { timeout: 15000 }).then(() => "MathJax typeset", () => "no MathJax in the statement");
      out.rowsDrawn = await page.locator(".brow[data-go]").count();
      return decodeURIComponent(lab) + " -> " + h + " (" + typeset + ")"; });
    await check("binder row: follow a ladder link", async () => {
      const b = page.locator("#panel .pl[data-go^='#/ladder/p/']").first();
      if (!(await b.count())) return "no ladder link in this row";
      const id = (await b.innerText()).trim(), before = await panelH2(page); await b.click();
      const h = await nextH2(page, before); if (h !== id) throw new Error("panel shows " + h); return h; });
    await check("roadmap tab, click a target", async () => {
      await page.click("#tab-roadmap");
      const c = page.locator(".tcard").first(); const id = decodeURIComponent((await c.getAttribute("data-go")).split("/").pop());
      const before = await panelH2(page); await c.click(); await nextH2(page, before); const chips = await page.locator("#panel .chips .mono").first().innerText();
      out.cardsDrawn = await page.locator(".tcard").count();
      if (chips !== id) throw new Error("panel shows " + chips); return id; });
  }));
  results.push(await run(browser, { viewport: { width: 390, height: 844 }, colorScheme: "dark", isMobile: true, hasTouch: true }, "phone-dark", async (page, check) => {
    await check("phone: tap a property", async () => {
      const id = await page.evaluate(() => DATA.ladder.props[0].id);
      const before = await panelH2(page);
      await page.evaluate(i => { location.hash = "#/ladder/p/" + encodeURIComponent(i); }, id);
      const h = await nextH2(page, before); if (h !== id) throw new Error("panel shows " + h); return h; });
    await check("phone: tap an implication beside its line", async () => {
      const q = (await segmentPointsIn(page, OFF, Infinity)).filter(q => q.x != null && q.clr >= OFF + 3);
      const n = await page.evaluate(() => DATA.ladder.implies.map(e => e.from.length > 1));
      const pick = q.filter(x => n[x.i]).sort((a, b) => b.clr - a.clr)[0] || q.sort((a, b) => b.clr - a.clr)[0];
      if (!pick) throw new Error("no implication drawn in view");
      const want = await implText(page, pick.i), h = await clickTo(page, pick.x, pick.y, want, true);
      if (h !== want) throw new Error(`tap on ${want} [${pick.seg}] opened ${h}`);
      return want + " [" + pick.seg + "]: " + await edgePanel(page); });
    await check("phone: open a nesting, tap a transfer", async () => {
      const X = await page.evaluate(() => DATA.ladder.props.find(p => (DATA.ladder.along[p.id] || []).length)?.id);
      if (!X) return "no transfer recorded";
      await page.evaluate(x => { location.hash = "#/ladder/p/" + encodeURIComponent(x); }, X);
      if (await toH2(page, X) !== X) throw new Error("the nesting's panel did not open");
      const b = page.locator('#panel button[data-go^="#/ladder/transfer/"]').last();
      await b.scrollIntoViewIfNeeded();
      const k = +(await b.getAttribute("data-go")).split("/").pop(), want = await page.evaluate(k => transferTitle(DATA.ladder.transfers[k]), k);
      const r = await b.boundingBox(); await page.touchscreen.tap(r.x + r.width / 2, r.y + r.height / 2);
      const h = await toH2(page, want); if (h !== want) throw new Error("panel shows " + h);
      return await transferPanel(page); });
    await check("phone: pairs view and its transfer table, no horizontal overflow", async () => {
      await page.click("#m-pairs"); await page.waitForSelector("#ttab", { timeout: 3000 }).catch(() => {});
      const w = await page.evaluate(() => [document.documentElement.scrollWidth, innerWidth, !!document.querySelector("#ttab")]);
      await page.click("#m-graph");
      if (w[0] > w[1] + 1) throw new Error("page is " + w[0] + "px wide at " + w[1]); return `${w[0]}/${w[1]}${w[2] ? ", transfer table drawn" : ""}`; });
    await check("phone: binders, open a row", async () => {
      await page.click("#tab-binders"); const before = await panelH2(page); await page.locator(".brow[data-go]").nth(1).click();
      const h = await nextH2(page, before); if (h === before) throw new Error("panel did not change"); return h; });
    await check("phone: no horizontal overflow", async () => {
      const w = await page.evaluate(() => [document.documentElement.scrollWidth, innerWidth]);
      if (w[0] > w[1] + 1) throw new Error("page is " + w[0] + "px wide at " + w[1]); return w.join("/"); });
  }));
  await browser.close();
  let bad = 0;
  for (const r of results) {
    console.log(`[${r.label}] page errors: ${r.pageErrors.length}; console errors: ${r.consoleErrors.length}; failed requests: ${r.failedRequests.length}`);
    if (r.counts) console.log("  read from the page: " + JSON.stringify(r.counts) + (r.matrixCells != null ? ` matrixCells=${r.matrixCells}` : "") + (r.transferCells != null ? ` transferCells=${r.transferCells}` : "") + (r.rowsDrawn != null ? ` rowsDrawn=${r.rowsDrawn}` : "") + (r.cardsDrawn != null ? ` cardsDrawn=${r.cardsDrawn}` : ""));
    for (const [w, s, v] of r.checks) console.log(`  ${s === "ok" ? "ok  " : "FAIL"} ${w}: ${v}`);
    for (const e of r.pageErrors) console.log("  page error: " + e);
    for (const e of r.consoleErrors) console.log("  console error: " + e);
    for (const e of r.failedRequests) console.log("  failed request: " + e);
    bad += r.pageErrors.length + r.checks.filter(c => c[1] !== "ok").length;
  }
  const total = results.reduce((a, r) => a + r.pageErrors.length, 0);
  console.log(`blueprint smoke: ${total} page error(s)` + (bad - total ? `, ${bad - total} failed check(s)` : ""));
  process.exit(bad ? 1 : 0);
})().catch(e => { console.error(e); process.exit(2); });
