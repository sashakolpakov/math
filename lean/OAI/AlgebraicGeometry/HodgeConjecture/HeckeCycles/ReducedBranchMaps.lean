import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares

/-! # Reduced Branch Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedBranchMaps.CM

noncomputable section

/-! The branch equivalence through reduction and field extension has the
literal original scheme maps used to transport the PEL family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B) {X : Over B'}
  [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M))
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M) {T : Over B'} (x : T ⟶ X)

omit [IsReduced X.left] [IsLocallyNoetherian X.left] in
theorem point_left :
    (CMExtraction.ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x).left = x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e := by
  rw [AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv_left]
  exact Category.assoc _ _ _

theorem branch_left (z : (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :
    (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x z).val.left = z.val.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C := by
  change (AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl C.cover
    (z.val ≫ pullback.fst (C.baseChange p).source (CMExtraction.ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e))).left = _
  rw [AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv_left]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedBranchMaps.CM
