import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares

/-! # Reduced Fiber Projections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedFiberProjections.IsogenyQuotient

noncomputable section

/-! The retained branch equivalence preserves the actual map into the
original cover, and the corresponding original source point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B B' : Scheme} (p : B' ⟶ B) (M : Over B)
  {X : Over B'} [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M)) (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M)
  {T : Over B'} (x : T ⟶ X)

omit [IsReduced X.left] [IsLocallyNoetherian X.left] in
theorem originalModelPoint_left :
    (ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x).left = x.left ≫ ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e := by
  change (x.left ≫ (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e).left) ≫ _ = _
  exact Category.assoc _ _ _

theorem modelFiberEquiv_left (z : (ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :
    (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x z).val.left = z.val.left ≫ ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C := by
  change (z.val.left ≫ (pullback.fst (C.baseChange p).source (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)).left) ≫ _ = _
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedFiberProjections.IsogenyQuotient
