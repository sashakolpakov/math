import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels

/-! # Active Splitting Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport.Construction

noncomputable section

/-! Pulling active ordinary coordinates through an ambient isomorphism
retains the plane and each line with the same labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (q : ℕ)
variable {G G' : Grp (Over (Spec (.of k)))}
variable (b : G ≅ G') (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q G')

theorem chosenActiveEtalePlane_sourceTransport :
    ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (b ≪≫ e) ≫ b.hom = ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e := by
  change ((AnnihilatorSheaf.Construction.splitSecondInclusion _ _ ≫ (e.inv ≫ b.inv)) ≫ b.hom) = AnnihilatorSheaf.Construction.splitSecondInclusion _ _ ≫ e.inv
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem chosenActiveEtaleLine_sourceTransport [Fact q.Prime] (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (b ≪≫ e) L ≫ b.hom = ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L := by
  change (EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q L ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (b ≪≫ e)) ≫ b.hom =
    EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q L ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ z)
      (chosenActiveEtalePlane_sourceTransport k q b e))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport.Construction
