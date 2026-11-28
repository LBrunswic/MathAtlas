# 0171 — For w closed in S(E), F(w) = A + A′ (ConeDec) is impossible: a ∈ A is a limit of a + t a′

*Found 2026-11-28 by T-bz-c3-boole-projectif-domaines; recorded by the master session.*

For w closed in S(E), F(w) = A + A′ (ConeDec) is impossible: a ∈ A is a limit of a + t a′ ∈ F(w), so mem_F_of_forall_add_smul (Chapter3/Sature.lean) puts a in A + A′ and forces 0 ∈ A′ (Sphere.not_coneDec_of_isClosed); the distinguished subvarieties of a closed w are ∅ and S(E).
