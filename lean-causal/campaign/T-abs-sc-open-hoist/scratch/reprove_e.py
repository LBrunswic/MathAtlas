# Part (e) of T-abs-sc-open-hoist: re-prove splitBy_of_t1_secondCountable (ErsSecondCountable) and
# IsCauchySurface.cover_of_t1_secondCountable (CauchySeparation) from the hoisted split; statements
# unchanged (the header lines are asserted unchanged). Run once: python3 -I reprove_e.py
import pathlib
R = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal")

p = R / "ErsSecondCountable.lean"
s = p.read_text(encoding="utf-8")
old = """/-- **A Cauchy surface of an open set splits it**, in a T1, second countable space:
`splitBy_of_inextensibleThrough` with `InextensibleThrough W` discharged. -/
theorem splitBy_of_t1_secondCountable [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : Opens M} (hS : C.IsCauchySurfaceOn W S) : C.SplitBy W S :=
  splitBy_of_inextensibleThrough hS (inextensibleThrough_of_t1_secondCountable C W)
"""
new = """/-- **A Cauchy surface of an open set splits it**, in a T1, second countable space:
`IsCauchySurfaceOn.mem_Jplus_union_Jminus` (`Causal.CurvesExtendSecondCountable`), whose statement
`SplitBy W S` is. Re-proved from it by T-abs-sc-open-hoist; before, it was
`splitBy_of_inextensibleThrough` with `InextensibleThrough W` discharged. -/
theorem splitBy_of_t1_secondCountable [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : Opens M} (hS : C.IsCauchySurfaceOn W S) : C.SplitBy W S :=
  fun _ hq => hS.mem_Jplus_union_Jminus hq
"""
assert s.count(old) == 1
s = s.replace(old, new, 1)
p.write_text(s, encoding="utf-8")

p = R / "CauchySeparation.lean"
s = p.read_text(encoding="utf-8")
old = """/-- Step (1): in a T1, second countable space, every point lies on an inextensible causal curve (the
constant one, extended), which meets a Cauchy surface `S` at a point comparable with it, so
`M = J⁺(S) ∪ J⁻(S)`. No causality, no global hyperbolicity. -/
theorem IsCauchySurface.cover_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurface S) (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  have hconst : C.CausalCurveIn ⊤ (Icc 0 1) (fun _ => x) :=
    (causalCurveOn_const (a := 0) (b := 1) (show x ∈ (⊤ : Opens M) from trivial)).causalCurveIn_Icc
      zero_le_one
  obtain ⟨J, γ, hγ, hsub⟩ := exists_inextensible_of_t1_secondCountable hconst
  obtain ⟨t, ht, htx⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have htx' : γ t = x := htx
  obtain ⟨σ, ⟨⟨s, hs, rfl⟩, hσS⟩, -⟩ := hS J γ hγ
  rcases le_total s t with hst | hts
  · left
    refine ⟨γ s, hσS, ?_⟩
    rw [← htx']
    exact hγ.1.le_of_le hs ht hst
  · right
    refine ⟨γ s, hσS, ?_⟩
    rw [← htx']
    exact hγ.1.le_of_le ht hs hts
"""
new = """/-- Step (1): in a T1, second countable space, every point lies on an inextensible causal curve (the
constant one, extended), which meets a Cauchy surface `S` at a point comparable with it, so
`M = J⁺(S) ∪ J⁻(S)`. No causality, no global hyperbolicity. The case `W = ⊤` of
`IsCauchySurfaceOn.mem_Jplus_union_Jminus` (`Causal.CurvesExtendSecondCountable`), from which it is
re-proved by T-abs-sc-open-hoist (`IsCauchySurface S` is `IsCauchySurfaceOn ⊤ S` by definition). -/
theorem IsCauchySurface.cover_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurface S) (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S :=
  IsCauchySurfaceOn.mem_Jplus_union_Jminus hS (show x ∈ (⊤ : Opens M) from trivial)
"""
assert s.count(old) == 1
s = s.replace(old, new, 1)
p.write_text(s, encoding="utf-8")
print("ok")
