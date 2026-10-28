import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix

/-! # Theta Archimedean Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaArchimedeanAction.CM

noncomputable section

/-! The actual rational source group at infinity, in the AdelicTheta
orthonormal bases. Each local matrix is the original CM embedding of
the source matrix, conjugated by the explicitly constructed basis. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def rational : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) :=
  (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))).comp
      (Source.UnitaryMatrix.CM.hom E (OppositeCoordinates.CM.coordinates E L.coordinates))

theorem local_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin places.count) :
    ((rational E L g ((Source.BallArithmetic.CM.data E L).enumerate v)).val.val).map
      ((Source.BallArithmetic.CM.data E L).complex v) =
        g.val.val.map (ReferenceDatum.CM.embeddings E places v) := by
  ext i j
  change Source.ArchimedeanCoordinates.CM.complexCoordinate E
    (OppositeCoordinates.CM.coordinates E L.coordinates) v
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (.inl (Source.ArchimedeanPlaces.CM.enumeration E places v))
      ((Source.QuadraticConjugation.CM.Field.fieldEquiv E (OppositeCoordinates.CM.coordinates E L.coordinates)).symm (g.val.val i j))) = _
  rw [Source.ArchimedeanCoordinates.CM.rational_compatibility, AlgEquiv.apply_symm_apply]
  rfl

theorem standard_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin places.count) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (Source.BallArithmetic.CM.data E L) (rational E L g) v =
      (Source.ArchimedeanBases.CM.hermitian E (B := B) v).inv *
        g.val.val.map (ReferenceDatum.CM.embeddings E places v) *
          (Source.ArchimedeanBases.CM.hermitian E (B := B) v).val := by
  unfold RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix
  rw [local_matrix]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaArchimedeanAction.CM
