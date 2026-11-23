import Causal.AbstractDev
import Causal.MaximalZorn
import Causal.CurvesExtendSecondCountable

/-! T-tac-curves-fact-rule: the declarations moved to `Causal.AbstractDev` (written in its source),
and the users this split concerns. Not built by lake (campaign/ is outside the globs). -/

#print axioms Causal.AbstractDev.ChainsInherit
#print axioms Causal.AbstractDev.Extends
#print axioms Causal.AbstractDev.IsCocone
#print axioms Causal.AbstractDev.IsCoherentChain
#print axioms Causal.AbstractDev.IsInextensible
#print axioms Causal.AbstractDev.IsInextensible.bijective
#print axioms Causal.AbstractDev.IsInextensible.isMaximal
#print axioms Causal.AbstractDev.IsIso
#print axioms Causal.AbstractDev.IsMaximal
#print axioms Causal.AbstractDev.IsMaximal.isInextensible
#print axioms Causal.AbstractDev.IsTower
#print axioms Causal.AbstractDev.IsTower.exists_cocone
#print axioms Causal.AbstractDev.IsTower.extend
#print axioms Causal.AbstractDev.MorphismsCompose
#print axioms Causal.AbstractDev.RigidEndomorphisms
#print axioms Causal.AbstractDev.SizeBound
#print axioms Causal.AbstractDev.Tower
#print axioms Causal.AbstractDev.Tower.LE
#print axioms Causal.AbstractDev.Tower.LE.refl
#print axioms Causal.AbstractDev.Tower.LE.trans
#print axioms Causal.AbstractDev.Tower.le_sUnion
#print axioms Causal.AbstractDev.Tower.sUnion
#print axioms Causal.AbstractDev.Tower.singleton
#print axioms Causal.AbstractDev.UniqueMorphisms
#print axioms Causal.AbstractDev.UniqueMorphisms.rigidEndomorphisms
#print axioms Causal.AbstractDev.allMor
#print axioms Causal.AbstractDev.allMor_separates
#print axioms Causal.AbstractDev.chrusciel_theorem_2_2
#print axioms Causal.AbstractDev.exists_isMaximal
#print axioms Causal.AbstractDev.exists_isMaximal_of_chainsInherit
#print axioms Causal.AbstractDev.exists_isMaximal_of_sequences
#print axioms Causal.AbstractDev.exists_isMaximal_of_uniqueMorphisms
#print axioms Causal.AbstractDev.exists_upperBound_of_uniqueMorphisms
#print axioms Causal.AbstractDev.isTower_sUnion
#print axioms Causal.AbstractDev.isTower_singleton
#print axioms Causal.AbstractDev.natMor
#print axioms Causal.AbstractDev.natMor_separates
#print axioms Causal.AbstractDev.not_sizeBound_ordinalMor
#print axioms Causal.AbstractDev.ordinalMor
#print axioms Causal.AbstractDev.ordinalMor_separates
#print axioms Causal.AbstractDev.sizeBound_self
#print axioms Causal.AbstractDev.twoMor
#print axioms Causal.AbstractDev.twoMor_rigid_not_unique

-- users
#print axioms Causal.exists_isMaximalDevelopment
#print axioms Causal.ers_remark_3_56
#print axioms Causal.Causality.curvesExtend_of_t1_secondCountable
#print axioms Causal.Causality.curvesExtendOn_of_t1_secondCountable
#print axioms Causal.Causality.exists_inextensible_of_t1_secondCountable

-- the fact's witness, as the rule will see it
#check @Causal.Causality.curvesExtend_of_t1_secondCountable
