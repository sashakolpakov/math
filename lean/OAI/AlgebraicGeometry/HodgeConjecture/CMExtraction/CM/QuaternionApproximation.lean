import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.StrongApproximation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionSubgroup
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionRealPlace

/-! # Quaternion Approximation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionApproximation

noncomputable section

/-! Strong approximation for the actual quaternion algebra underlying
each binary subgroup of the CM Hermitian space. Its active real factor
is noncompact because the retained Hermitian coefficient is negative. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  (places : HeckeCycles.GeometricSource.CM.Places E) (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

include hb0 hδ0 in
theorem cmQuaternion_finite_strongApproximation
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0) :
    DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup
      (QuadraticCoordinates.squareParameter E δ hδ) (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb))) :=
  Quaternion.StrongApproximation.quaternion_finite_strongApproximation_positive _ _
    (QuadraticCoordinates.squareParameter_ne_zero E δ hδ hδ0)
    (QuaternionRealPlace.cmQuaternion_second_coefficient_ne_zero E b hb hb0)
    (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places places.distinguished)
    (ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places places.distinguished)
    (ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_continuous E places places.distinguished)
    (QuaternionRealPlace.cmQuaternion_active_real_positive E places b hb hball)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionApproximation
