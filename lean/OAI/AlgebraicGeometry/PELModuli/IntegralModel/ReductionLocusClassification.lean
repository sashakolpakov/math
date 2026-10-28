import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

/-! # Reduction Locus Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionLocusClassification

noncomputable section

/-! Reducing a constructed parameter locus preserves its unique
factorization criterion on every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem existsUnique_lift_reduction_iff {S : Scheme.{0}} {Z M T : Over S}
    [IsReduced T.left] (j : Z ⟶ M) (x : T ⟶ M) :
    (∃! f : T ⟶ Reduction.reduction Z, f ≫ (Reduction.reductionι Z ≫ j) = x) ↔
      ∃! f : T ⟶ Z, f ≫ j = x := by
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨u ≫ Reduction.reductionι Z, (Category.assoc _ _ _).trans hu, ?_⟩
    intro v hv
    have hl : Reduction.factorToReduction v ≫ (Reduction.reductionι Z ≫ j) = x := by
      rw [← Category.assoc, Reduction.factorToReduction_ι, hv]
    exact (Reduction.factorToReduction_ι v).symm.trans (congrArg (fun q => q ≫ Reduction.reductionι Z) (huniq _ hl))
  · rintro ⟨u, hu, huniq⟩
    refine ⟨Reduction.factorToReduction u, ?_, ?_⟩
    · change Reduction.factorToReduction u ≫ (Reduction.reductionι Z ≫ j) = x
      rw [← Category.assoc, Reduction.factorToReduction_ι, hu]
    · intro v hv
      apply (cancel_mono (Reduction.reductionι Z)).mp
      rw [Reduction.factorToReduction_ι]
      exact huniq _ ((Category.assoc _ _ _).trans hv)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionLocusClassification
