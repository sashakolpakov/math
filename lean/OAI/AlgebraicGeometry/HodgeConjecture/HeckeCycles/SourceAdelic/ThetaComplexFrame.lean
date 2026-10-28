import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaRationalComplexComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameComplexChange
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt

/-! # Theta Complex Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexFrame.CM

noncomputable section

/-! The original complex source space is identified with AdelicTheta's actual
CM tensor components by the complexification of the derived rational
symplectic matrix. No complex or theta matching hypothesis is added. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))

def nativeFrame : GeometricSource.CM.Ambient E ≃ₗ[ℂ]
    ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L)) → ℂ) :=
  Rational.FrameComplexChange.CM.frame (ThetaRationalFrame.CM.index E L) (Source.ComplexAction.CM.complexFrame E L.coordinates) (ThetaRationalFrame.CM.matrix E L T hT)

theorem native_rational (x : GeometricSource.CM.Vec E) :
    nativeFrame E L T hT (GeometricSource.CM.embeddingCoordinates E x) = fun i => (ThetaRationalFrame.CM.native E L T x i : ℂ) :=
  Rational.FrameComplexChange.CM.rational (ThetaRationalFrame.CM.index E L)
    (Source.ComplexAction.CM.Symplectic.frame E L.coordinates) (Source.ComplexAction.CM.complexFrame E L.coordinates)
    (GeometricSource.CM.embeddingCoordinates E) (Source.ComplexAction.CM.complexFrame_rational E L.coordinates) (ThetaRationalFrame.CM.matrix E L T hT)
    (ThetaRationalFrame.CM.native E L T) (ThetaRationalFrame.CM.matrix_source E L T hT) x

def equiv : GeometricSource.CM.Ambient E ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (Source.BallArithmetic.CM.data E L) :=
  (nativeFrame E L T hT).trans T.complexPhase.toLinearEquiv

theorem rational (x : GeometricSource.CM.Vec E) :
    equiv E L T hT (GeometricSource.CM.embeddingCoordinates E x) =
      ThetaComplexComponents.CM.components E L (GeometricSource.CM.embeddingCoordinates E x) := by
  change T.complexPhase (nativeFrame E L T hT (GeometricSource.CM.embeddingCoordinates E x)) = _
  rw [native_rational, ThetaComplexComponents.CM.rational]
  exact Adelic.ThetaRationalComplexComparison.CM.rational (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
    (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.BallArithmetic.CM.data E L) T hT
    (Source.TensorPairing.CM.tensorVector E (OppositeCoordinates.CM.coordinates E L.coordinates) x)

theorem comparison : (equiv E L T hT).toLinearMap =
    ThetaComplexComponents.CM.components E L := by
  apply Rational.FrameBilinearExt.CM.Linear.ext (Source.ComplexAction.CM.Symplectic.frame E L.coordinates)
    (Source.ComplexAction.CM.complexFrame E L.coordinates) (GeometricSource.CM.embeddingCoordinates E) (Source.ComplexAction.CM.complexFrame_rational E L.coordinates)
  exact rational E L T hT

theorem apply (w : GeometricSource.CM.Ambient E) :
    equiv E L T hT w = ThetaComplexComponents.CM.components E L w :=
  LinearMap.congr_fun (comparison E L T hT) w

include hT in
theorem components_bijective : Function.Bijective (ThetaComplexComponents.CM.components E L) := by
  have he : (ThetaComplexComponents.CM.components E L : GeometricSource.CM.Ambient E →
      RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (Source.BallArithmetic.CM.data E L)) = equiv E L T hT :=
    funext (fun w => (CM.apply E L T hT w).symm)
  rw [he]
  exact (equiv E L T hT).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexFrame.CM
