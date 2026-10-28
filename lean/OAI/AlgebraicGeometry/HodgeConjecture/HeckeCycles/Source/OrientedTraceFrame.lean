import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OppositeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceFrame

/-! # Oriented Trace Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedTraceFrame.CM

noncomputable section

/-! Use the opposite multiplicity line and momentum/position order to
obtain exactly the original source trace form in rational coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem swap_pairing {I : Type*} [Fintype I]
    (x y : (I → ℚ) × (I → ℚ)) :
    (∑ i, (x.2 i * y.1 i - y.2 i * x.1 i)) =
      -(∑ i, (x.1 i * y.2 i - y.1 i * x.2 i)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def frame : GeometricSource.CM.Vec E ≃ₗ[ℚ] ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  ((TraceFrame.CM.reindexed E (OppositeCoordinates.CM.coordinates E C)).trans
    (LinearEquiv.prodComm ℚ _ _)).trans
      (LinearEquiv.sumArrowLequivProdArrow (GeometricSource.CM.Positions E places) (GeometricSource.CM.Positions E places) ℚ ℚ).symm

theorem frame_pairing (x y : GeometricSource.CM.Vec E) :
    ComplexAction.CM.Symplectic.pairing (frame E C x) (frame E C y) =
      Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by
  change (∑ i, (
    ((TraceFrame.CM.reindexed E (OppositeCoordinates.CM.coordinates E C)) x).2 i *
      ((TraceFrame.CM.reindexed E (OppositeCoordinates.CM.coordinates E C)) y).1 i -
    ((TraceFrame.CM.reindexed E (OppositeCoordinates.CM.coordinates E C)) y).2 i *
      ((TraceFrame.CM.reindexed E (OppositeCoordinates.CM.coordinates E C)) x).1 i)) = _
  rw [swap_pairing, TraceFrame.CM.reindexed_pairing]
  change -Algebra.trace ℚ E (C.delta * -C.a * GeometricSource.CM.hermitian E B.b x y) = _
  have he : C.delta * -C.a * GeometricSource.CM.hermitian E B.b x y = -(C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by ring
  rw [he, map_neg, neg_neg]

def changeOfFrame : ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) ≃ₗ[ℚ]
    ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  (ComplexAction.CM.Symplectic.frame E C).symm.trans (frame E C)

theorem change_pairing (x y : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :
    ComplexAction.CM.Symplectic.pairing (changeOfFrame E C x) (changeOfFrame E C y) =
      ComplexAction.CM.Symplectic.pairing x y := by
  change ComplexAction.CM.Symplectic.pairing
    (frame E C ((ComplexAction.CM.Symplectic.frame E C).symm x))
    (frame E C ((ComplexAction.CM.Symplectic.frame E C).symm y)) = _
  rw [frame_pairing, ← ComplexAction.CM.Symplectic.frame_pairing,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def matrix : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ :=
  ⟨LinearMap.toMatrix' (changeOfFrame E C).toLinearMap,
    ComplexAction.CM.Symplectic.matrix_symplectic _ (by
      intro x y
      simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using change_pairing E C x y)⟩

theorem matrix_source (x : GeometricSource.CM.Vec E) :
    (matrix E C).val *ᵥ ComplexAction.CM.Symplectic.frame E C x = frame E C x := by
  change (LinearMap.toMatrix' (changeOfFrame E C).toLinearMap) *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  exact congrArg (frame E C) ((ComplexAction.CM.Symplectic.frame E C).symm_apply_apply x)

theorem conjugated_source_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    ((matrix E C * ComplexAction.CM.Symplectic.symplectic E C g * (matrix E C)⁻¹).val) *ᵥ
        frame E C x = frame E C (ComplexAction.CM.Symplectic.rationalAction E g x) := by
  rw [← matrix_source E C x]
  change ((matrix E C).val * (ComplexAction.CM.Symplectic.symplectic E C g).val *
    ((matrix E C)⁻¹).val) *ᵥ
    ((matrix E C).val *ᵥ ComplexAction.CM.Symplectic.frame E C x) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  have h : ((matrix E C)⁻¹).val * (matrix E C).val = 1 :=
    congrArg Subtype.val (inv_mul_cancel (matrix E C))
  rw [h, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    ComplexAction.CM.Symplectic.symplectic_apply, matrix_source]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedTraceFrame.CM
