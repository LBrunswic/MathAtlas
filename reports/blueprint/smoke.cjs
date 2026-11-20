// Headless smoke test of the blueprint page: load it, click into a property, an implication, a pair,
// a binder row and a roadmap target, at desktop and phone width, in both colour schemes; count page
// errors (uncaught exceptions). Exit 1 on any page error or on a click that does not open its panel.
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
// the panel's heading once it differs from `before`
const nextH2 = async (page, before) => { await page.waitForFunction(b => { const h = document.querySelector("#panel h2"); return h && h.innerText !== b; }, before, { timeout: 5000 }).catch(() => {}); return panelH2(page); };

(async () => {
  const browser = await pw.chromium.launch();
  const results = [];
  results.push(await run(browser, { viewport: { width: 1440, height: 900 }, colorScheme: "light" }, "desktop-light", async (page, check, out) => {
    out.counts = await page.evaluate(() => ({
      properties: DATA.ladder.props.length, nodesDrawn: document.querySelectorAll("#world .node").length,
      implications: DATA.ladder.implies.length, edgesDrawn: new Set([...document.querySelectorAll("#world .edge")].map(e => e.dataset.i)).size,
      pairs: DATA.ladder.summary && DATA.ladder.summary.pairs, classified: DATA.ladder.summary && DATA.ladder.summary.classified,
      consequences: DATA.ladder.cons.length, binders: DATA.binders.map(b => b.slug + ":" + b.rows.length).join(", "),
      targets: DATA.road.targets.length }));
    const first = await page.evaluate(() => DATA.ladder.props.find(p => DATA.ladder.implies.some(e => e.from.includes(p.id)))?.id || DATA.ladder.props[0].id);
    await check("click property " + first, async () => {
      const before = await panelH2(page);
      await page.locator(`#world .node[data-id="${first}"]`).click();
      const h = await nextH2(page, before); if (h !== first) throw new Error("panel shows " + h); return h; });
    await check("click an implication", async () => {
      const before = await panelH2(page);
      await page.locator("#world .edge path.hit").first().click({ force: true });
      const h = await nextH2(page, before); if (!h.includes("⇒")) throw new Error("panel shows " + h); return h; });
    await check("pairs view, click a classified cell", async () => {
      await page.click("#m-pairs");
      const before = await panelH2(page);
      await page.locator("#matrix td button.m-implied, #matrix td button.m-implied-c").first().click();
      const h = await nextH2(page, before); if (!/⇒|⇏/.test(h)) throw new Error("panel shows " + h);
      out.matrixCells = await page.locator("#matrix td button:not(.m-diag)").count(); return h; });
    await page.click("#m-graph");
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
    if (r.counts) console.log("  read from the page: " + JSON.stringify(r.counts) + (r.matrixCells != null ? ` matrixCells=${r.matrixCells}` : "") + (r.rowsDrawn != null ? ` rowsDrawn=${r.rowsDrawn}` : "") + (r.cardsDrawn != null ? ` cardsDrawn=${r.cardsDrawn}` : ""));
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
