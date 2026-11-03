import re, sys
base = "/home/maxbrain/Dropbox/LeanArticles/lean-gx/.lake/packages/Causal/lean-causal/Causal/CBG/"
G = open(base + "Geometry.lean", encoding="utf-8").read().split("\n")
F = open(base + "FromModel.lean", encoding="utf-8").read().split("\n")
def rng(L, a, b):  # 1-indexed inclusive
    return L[a-1:b]
def find(L, pat, start=1):
    for i in range(start-1, len(L)):
        if L[i].startswith(pat):
            return i+1
    raise SystemExit("not found: " + pat)
out = []
# A: structure + namespace LocalModel (Geometry.lean)
a0 = find(G, "/-- **Level B: a local model**")
a1 = find(G, "end LocalModel", a0)
out += rng(G, a0, a1)
# B: FromModel structural + ofLocalModelOfGermSlice
b0 = find(F, "/-! ### Level B ⇒ Level A: the structural fields")
b1 = find(F, "end Geometry", b0)
out += rng(F, b0, b1)
# C: B2 step
c0 = find(F, "/-! ### The B2 step of A3", b1)
c1 = find(F, "end LocalModel", c0)
out += rng(F, c0, c1)
# D: ModelStep minus two generic theorems
d0 = find(F, "section ModelStep", c1)
d1 = find(F, "end ModelStep", d0)
blk = rng(F, d0, d1)
g0 = next(i for i,l in enumerate(blk) if l.startswith("theorem trans_mem_maximalAtlas_of_mem"))
g1 = next(i for i,l in enumerate(blk) if l.startswith("variable {𝔐"))
blk = blk[:g0] + blk[g1:]
out += blk
# E: Assembly
e0 = find(F, "section Assembly", d1)
e1 = find(F, "end Assembly", e0)
out += rng(F, e0, e1)
# F: A4 cone slice
f0 = find(F, "/-! ### A4 from a cone-slice form of B4", e1)
f1 = find(F, "end LocalModel", f0)
out += rng(F, f0, f1)
# G: AssemblyNonBTZ
h0 = find(F, "/-! ### A3 at non-BTZ boundary points", f1)
h1 = find(F, "end AssemblyNonBTZ", h0)
out += rng(F, h0, h1)
# H: BTZ residual preds etc, minus singY_zero
i0 = find(F, "/-! ### A3 and A4 for a local model: derived", h1)
i1 = find(F, "end LocalModel", i0)
blk = rng(F, i0, i1)
s0 = next(i for i,l in enumerate(blk) if l.startswith("/-- A model without BTZ points satisfies the A3-future"))
blk = blk[:s0] + ["end LocalModel"]
out += blk
j0 = find(F, "namespace Geometry", i1)
j1 = find(F, "end Geometry", j0)
blk = rng(F, j0, j1)
s0 = next(i for i,l in enumerate(blk) if l.startswith("/-- **Level B ⇒ Level A for a model without BTZ points**"))
blk = blk[:s0] + ["end Geometry"]
out += blk
txt = "\n".join(out)
# transformations
txt = re.sub(r"\bLocalModel\b", "TLocalModel", txt)
txt = txt.replace("namespace Geometry", "namespace TGeometry").replace("end Geometry", "end TGeometry")
txt = txt.replace("Geometry.{u}", "Causal.CBG.Geometry.{u}").replace("PreGeometry.{u}", "Causal.CBG.PreGeometry.{u}")
txt = txt.replace("Causal.CBG.Causal.CBG.", "Causal.CBG.")
txt = txt.replace("Causal.CBG.Pre" + "Causal.CBG.", "Causal.CBG.Pre")
# typeAgreement: Tendsto form
old = "    MapClusterPt z₀ (𝓝[U] y₀) f →\n    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ singY α ↔ z₀ ∈ singY α)) ∧"
assert old in txt, "typeAgreement field"
txt = txt.replace(old, "    Tendsto f (𝓝[U] y₀) (𝓝 z₀) →\n    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ singY α ↔ z₀ ∈ singY α)) ∧")
old2 = "    (κ' q) f hloc hinjf hclus\n"
assert old2 in txt, "use site"
txt = txt.replace(old2, "    (κ' q) f hloc hinjf (TLocalModel.tendsto_chart (𝔐 := 𝔐) hAκ hpκ hqκ' hT)\n")
# tendsto_chart after mapClusterPt_chart
anchor = "\nomit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in\n/-- **B2 at a singular point, past side, in charts**"
assert anchor in txt
tc = '''
omit [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **The convergence form of `mapClusterPt_chart`** (new in the port): if `ψ → q` along `A` at
`p`, then `κ' ∘ ψ ∘ κ.symm → κ' q` along `κ '' A` at `κ p`. Feeds the convergence form of
`typeAgreement` in `germ_ext_nonBTZ`. -/
theorem tendsto_chart {κ : OpenPartialHomeomorph M 𝔐.Y} {κ' : OpenPartialHomeomorph N 𝔐.Y}
    {ψ : M → N} {A : Set M} (hA : A ⊆ κ.source) {p : M} (hp : p ∈ κ.source) {q : N}
    (hq : q ∈ κ'.source) (h : Tendsto ψ (𝓝[A] p) (𝓝 q)) :
    Tendsto (κ' ∘ ψ ∘ κ.symm) (𝓝[κ '' A] (κ p)) (𝓝 (κ' q)) := by
  have h1 : 𝓝[κ '' A] (κ p) = map κ (𝓝[A] p) := by
    rw [κ.map_nhdsWithin_eq hp, inter_eq_right.2 hA]
  rw [h1, tendsto_map'_iff]
  have h2 : (κ' ∘ ψ ∘ κ.symm) ∘ κ =ᶠ[𝓝[A] p] κ' ∘ ψ :=
    eventually_nhdsWithin_of_forall fun z hz => by simp [κ.left_inv (hA hz)]
  exact (((κ'.continuousAt hq).tendsto).comp h).congr' h2.symm
'''
txt = txt.replace(anchor, tc + anchor, 1)
QUAL = [l.strip() for l in open("/home/maxbrain/Dropbox/LeanArticles/lean-gx/campaign/WP-41g/scratch/qual.txt") if l.strip()]
for q in QUAL:
    txt = re.sub(r"(?<![\w.'])" + re.escape(q) + r"(?![\w'])", "Causal." + q, txt)
for q in [l.strip() for l in open("/home/maxbrain/Dropbox/LeanArticles/lean-gx/campaign/WP-41g/scratch/qualcbg.txt") if l.strip()]:
    txt = re.sub(r"(?<![\w.'])" + re.escape(q) + r"(?![\w'])", "Causal.CBG." + q, txt)
sys.stdout.write(txt + "\n")
