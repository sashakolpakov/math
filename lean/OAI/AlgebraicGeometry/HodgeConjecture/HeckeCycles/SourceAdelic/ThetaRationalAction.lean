import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PhaseMatrixReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FieldAction

/-! # Theta Rational Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalAction.CM

noncomputable section

/-! AdelicTheta's characterized rational symplectic matrices are exactly the
original source matrices conjugated by the derived change of frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))

def nativeMatrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    Matrix (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) ℚ :=
  (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (T.rationalSymplectic (Source.UnitaryMatrix.CM.hom E
    (OppositeCoordinates.CM.coordinates E L.coordinates) g))).submatrix
      ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L)) ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L))

include hT in
theorem native_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (T.rationalSymplectic (Source.UnitaryMatrix.CM.hom E
      (OppositeCoordinates.CM.coordinates E L.coordinates) g))) *ᵥ RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (ThetaRationalFrame.CM.native E L T x) =
        RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (ThetaRationalFrame.CM.native E L T (Source.ComplexAction.CM.Symplectic.rationalAction E g x)) := by
  have h := hT.2.2.2.2.2.2.2.2.1
    (Source.UnitaryMatrix.CM.hom E (OppositeCoordinates.CM.coordinates E L.coordinates) g)
    ((Source.GlobalFrames.CM.rational E (OppositeCoordinates.CM.coordinates E L.coordinates)).coordinates
      (Source.TensorPairing.CM.tensorVector E (OppositeCoordinates.CM.coordinates E L.coordinates) x))
  change _ = RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (T.rationalPhase
    ((SourceFinite.FieldAction.CM.rational E (OppositeCoordinates.CM.coordinates E L.coordinates) g).val *ᵥ
      (Source.GlobalFrames.CM.rational E (OppositeCoordinates.CM.coordinates E L.coordinates)).coordinates
        (Source.TensorPairing.CM.tensorVector E
          (OppositeCoordinates.CM.coordinates E L.coordinates) x))) at h
  rw [SourceFinite.FieldAction.CM.rational_action] at h
  exact h

include hT in
theorem frame_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    nativeMatrix E L T g *ᵥ ThetaRationalFrame.CM.frame E L T x =
      ThetaRationalFrame.CM.frame E L T (Source.ComplexAction.CM.Symplectic.rationalAction E g x) := by
  change (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix _).submatrix ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L))
    ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L)) *ᵥ
      PhaseMatrixReindex.CM.swap (ThetaRationalFrame.CM.index E L) (ThetaRationalFrame.CM.native E L T x) = _
  rw [PhaseMatrixReindex.CM.action, native_action E L T hT]
  funext i
  cases i <;> rfl

theorem conjugated_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    ((ThetaRationalFrame.CM.matrix E L T hT * Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g *
      (ThetaRationalFrame.CM.matrix E L T hT)⁻¹).val) *ᵥ ThetaRationalFrame.CM.frame E L T x =
        ThetaRationalFrame.CM.frame E L T (Source.ComplexAction.CM.Symplectic.rationalAction E g x) := by
  rw [← ThetaRationalFrame.CM.matrix_source E L T hT x]
  change ((ThetaRationalFrame.CM.matrix E L T hT).val * (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g).val *
    ((ThetaRationalFrame.CM.matrix E L T hT)⁻¹).val) *ᵥ
      ((ThetaRationalFrame.CM.matrix E L T hT).val *ᵥ Source.ComplexAction.CM.Symplectic.frame E L.coordinates x) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  have h : ((ThetaRationalFrame.CM.matrix E L T hT)⁻¹).val * (ThetaRationalFrame.CM.matrix E L T hT).val = 1 :=
    congrArg Subtype.val (inv_mul_cancel (ThetaRationalFrame.CM.matrix E L T hT))
  rw [h, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    Source.ComplexAction.CM.Symplectic.symplectic_apply, ThetaRationalFrame.CM.matrix_source]

theorem matrix_eq (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    nativeMatrix E L T g =
      (ThetaRationalFrame.CM.matrix E L T hT * Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g *
        (ThetaRationalFrame.CM.matrix E L T hT)⁻¹).val := by
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨x, rfl⟩ := (ThetaRationalFrame.CM.frame E L T).surjective v
  rw [frame_action E L T hT, conjugated_action E L T hT]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalAction.CM
