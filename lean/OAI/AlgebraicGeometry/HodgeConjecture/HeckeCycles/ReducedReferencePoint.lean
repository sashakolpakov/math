import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedBranchMaps

/-! # Reduced Reference Point -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedReferencePoint.CM.Reference

noncomputable section

/-! Choose the original point with its literal composite scheme map.
The proved reduction and base-change equivalence retains every branch. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B) {X : Over B'}
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M))
  {T : Over B'} (x : T ⟶ X)

def point : Over.mk (T.hom ≫ p) ⟶ M :=
  Over.homMk (x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e)
    ((congrArg (fun f => f ≫ M.hom) (ReducedBranchMaps.CM.point_left p M e x)).symm.trans
      (CMExtraction.ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x).w)

theorem point_eq : point p M e x = CMExtraction.ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x :=
  Over.OverMorphism.ext (ReducedBranchMaps.CM.point_left p M e x).symm

theorem point_left : (point p M e x).left = x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e := rfl

def retarget {S : Scheme.{u}} {Y V : Over S} (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Y)
    {a b : V ⟶ Y} (h : a = b) : C.Fiber a ≃ C.Fiber b where
  toFun z := ⟨z.val, z.property.trans h⟩
  invFun z := ⟨z.val, z.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [IsReduced X.left] [IsLocallyNoetherian X.left] (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M)

def branchEquiv : (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x ≃ C.Fiber (point p M e x) :=
  (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).trans (retarget C (point_eq p M e x).symm)

theorem branch_left (z : (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :
    (branchEquiv p M e x C z).val.left = z.val.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C :=
  ReducedBranchMaps.CM.branch_left p M e C x z

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedReferencePoint.CM.Reference
