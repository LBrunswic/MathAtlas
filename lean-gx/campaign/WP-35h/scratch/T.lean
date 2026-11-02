import GXScaffold.Branched.GaloisExamples
open GX
#check @GX.absGalIdx
#check @GX.absGalIdx_spec
#check @GX.absGal_h𝓤
#check @GX.absGalW
#check @GX.absP_absGalW
#check @JoinedIn.somePath
#check @JoinedIn.somePath_mem
#check @IsPathConnected.joinedIn
#check @Path.Homotopic.Quotient.symm_trans
#check @Path.Homotopic.Quotient.trans_refl
#check @Path.Homotopic.Quotient.ind
#check @eventually_lt_nhds
#check @IsCompact.exists_isMinOn
#check @isQuotientMap_quotient_mk'
#check @GX.univCoverProj
example : LocallyConnectedSpace ℂ := inferInstance
example : CompactSpace (ℕ → Bool) := inferInstance
