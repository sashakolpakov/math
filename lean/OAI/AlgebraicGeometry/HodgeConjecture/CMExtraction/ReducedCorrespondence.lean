import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CorrespondenceRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedModelComparison

/-! # Reduced Correspondence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondence.IsogenyQuotient

noncomputable section

/-! Base change followed by restriction transports IsogenyQuotient's original fine-model
correspondence to the retained reduced generic model. Its target factors
through the reduction because the finite étale source cover is reduced. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B)
  {X : Over B'} [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M)) (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M)

abbrev modelCover := CorrespondenceRestriction.IsogenyQuotient.restrictedCover (C.baseChange p) (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)

instance modelCover_reduced : IsReduced (modelCover p M e C).left :=
  CorrespondenceRestriction.IsogenyQuotient.restrictedCover_reduced (C.baseChange p) (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)

def modelTarget : modelCover p M e C ⟶ X :=
  (ReducedModelComparison.IsogenyQuotient.reducedModelHomEquiv p M e (modelCover p M e C)).symm
    (pullback.fst (C.baseChange p).source (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e) ≫ (C.baseChange p).target)

theorem modelTarget_comp :
    modelTarget p M e C ≫ ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e =
      pullback.fst (C.baseChange p).source (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e) ≫ (C.baseChange p).target := by
  rw [← ReducedModelComparison.IsogenyQuotient.reducedModelHomEquiv_apply]
  exact (ReducedModelComparison.IsogenyQuotient.reducedModelHomEquiv p M e (modelCover p M e C)).apply_symm_apply _

abbrev modelCorrespondence : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X :=
  CorrespondenceRestriction.IsogenyQuotient.restrictCorrespondence (C.baseChange p) (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e) (modelTarget p M e C)

variable {T : Over B'} (x : T ⟶ X)

abbrev originalModelPoint : Over.mk (T.hom ≫ p) ⟶ M :=
  AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl M (x ≫ ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)

def modelFiberEquiv :
    (modelCorrespondence p M e C).Fiber x ≃ C.Fiber (originalModelPoint p M e x) :=
  (CorrespondenceRestriction.IsogenyQuotient.restrictionFiberEquiv (C.baseChange p) (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)
    (modelTarget p M e C) x).trans
      (C.baseChangeFiberEquiv p T.hom (x ≫ ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e))

theorem modelFiberEquiv_endpoint (z : (modelCorrespondence p M e C).Fiber x) :
    originalModelPoint p M e ((modelCorrespondence p M e C).endpoint z) =
      C.endpoint (modelFiberEquiv p M e C x z) := by
  have hr := CorrespondenceRestriction.IsogenyQuotient.restrictionFiberEquiv_endpoint (C.baseChange p) (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)
    (modelTarget p M e C) (modelTarget_comp p M e C) x z
  change AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv p T.hom (T.hom ≫ p) rfl M
    ((modelCorrespondence p M e C).endpoint z ≫ ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e) = _
  rw [hr]
  exact C.baseChangeFiberEquiv_endpoint p T.hom (x ≫ ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e) _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondence.IsogenyQuotient
