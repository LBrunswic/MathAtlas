# Part (b) of T-abs-sc-open-hoist: move IsEMorphismOn.chronalCurveOn_comp and
# Causality.ChronalHomotopyOn.homotopicRel out of Causal/Model/FlatSpaceCylinder.lean, byte for byte
# (the namespace prefix of the name becomes the enclosing namespace; full names unchanged).
# Asserts every edit. Run once: python3 -I move_b.py
import pathlib
R = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal")
fsc = R / "Model/FlatSpaceCylinder.lean"
src = fsc.read_text(encoding="utf-8")

start_cc = src.index("/-- **Push-forward of a chronal curve**")
start_hr = src.index("/-- **A chronal homotopy is a homotopy of paths relative to the endpoints**")
end_hr = src.index("namespace Flat\n")
block_cc = src[start_cc:start_hr]
block_hr = src[start_hr:end_hr]
assert block_cc.count("theorem IsEMorphismOn.chronalCurveOn_comp ") == 1
assert block_hr.count("theorem Causality.ChronalHomotopyOn.homotopicRel ") == 1
assert block_cc.endswith("\n\n") and block_hr.endswith("\n\n")
head = "/-! ### Two model-free lemmas -/\n\n"
assert src[start_cc - len(head):start_cc] == head
new_fsc = src[:start_cc - len(head)] + src[end_hr:]
fsc.write_text(new_fsc, encoding="utf-8")

# CauchyExtension: after causalCurveIn_comp, inside namespace IsEMorphismOn
ce = R / "CauchyExtension.lean"
s = ce.read_text(encoding="utf-8")
anchor = ("  ⟨hd.nonempty, hd.ordConnected, fun a ha b hb => h.causalCurveOn_comp hVW hVU (hd.curve a ha b hb)⟩\n\n")
assert s.count(anchor) == 1
moved_cc = block_cc.replace("theorem IsEMorphismOn.chronalCurveOn_comp ", "theorem chronalCurveOn_comp ", 1)
s = s.replace(anchor, anchor + moved_cc, 1)
ce.write_text(s, encoding="utf-8")

# TimelikeHomotopy: at the end of namespace ChronalHomotopyOn
th = R / "TimelikeHomotopy.lean"
t = th.read_text(encoding="utf-8")
anchor2 = "end ChronalHomotopyOn\n"
assert t.count(anchor2) == 1
moved_hr = block_hr.replace("theorem Causality.ChronalHomotopyOn.homotopicRel ", "theorem homotopicRel ", 1)
t = t.replace(anchor2, moved_hr + anchor2, 1)
th.write_text(t, encoding="utf-8")
print("ok", len(block_cc), len(block_hr))
