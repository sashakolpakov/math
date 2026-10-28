import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealPlace
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.StrongApproximation

/-! # Quaternion Approximation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionApproximation.CM

noncomputable section

/-! Strong approximation for the actual quaternion norm-one group
underlying the source's binary Hermitian plane. Its real noncompactness
comes from the original ball coefficient's strict negativity. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem positive_real_coefficient :
    0 < RealPlace.CM.coordinate E
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl (RealPlace.CM.place E))
        (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2)) := by
  have h := congrArg Complex.re (RealPlace.CM.rational E (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2))
  change RealPlace.CM.coordinate E
    (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl (RealPlace.CM.place E)) (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2)) =
      (-B.b : ℂ).re at h
  rw [h, Complex.neg_re]
  exact neg_pos.mpr B.negative

theorem strong_approximation :
    DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic
      (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup (QuadraticConjugation.CM.Field.discriminant E C) (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2))) :=
  CMExtraction.Quaternion.StrongApproximation.quaternion_finite_strongApproximation_positive
    (QuadraticConjugation.CM.Field.discriminant E C) (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
    (neg_ne_zero.mpr (RealCoefficients.CM.hermitianCoefficient_ne_zero E (B := B) 2))
    (RealPlace.CM.place E) (RealPlace.CM.coordinate E)
    (RealPlace.CM.coordinate_continuous E) (positive_real_coefficient E (B := B))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionApproximation.CM
