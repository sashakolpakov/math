import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanBases
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanSignMatrices
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Ball Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic.CM

noncomputable section

/-! Construct the complete archimedean ball arithmetic datum from the
original source period, using its derived signs and actual local forms. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

include B in
omit [IsGalois ℚ E] in
theorem other_place : ∃ v : Fin places.count, v ≠ places.distinguished := by
  obtain ⟨τ, hτ1, hτc⟩ := B.other_place
  obtain ⟨⟨v, b⟩, hv⟩ := places.complete.2 τ
  refine ⟨v, ?_⟩
  intro he
  subst v
  cases b
  · exact hτ1 (by simpa only [Bool.false_eq_true, ite_false, places.identity] using hv.symm)
  · exact hτc (by simpa only [ite_true, places.identity, mul_one] using hv.symm)

def data : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (QuadraticConjugation.CM.Field.RealField E)
    (QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
    (QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) where
  places := places.count
  enumerate := ArchimedeanPlaces.CM.enumeration E places
  distinguished := places.distinguished
  other_place := CM.other_place E (B := B) (places := places)
  real := ArchimedeanPlaces.CM.realCoordinate E places
  real_continuous := ArchimedeanPlaces.CM.real_continuous E places
  real_inverse_continuous := ArchimedeanPlaces.CM.real_inverse_continuous E places
  complex := ArchimedeanCoordinates.CM.complexCoordinate E (OppositeCoordinates.CM.coordinates E L.coordinates)
  complex_continuous := ArchimedeanCoordinates.CM.continuous E
    (OppositeCoordinates.CM.coordinates E L.coordinates)
  complex_inverse_continuous := ArchimedeanCoordinates.CM.inverse_continuous E
    (OppositeCoordinates.CM.coordinates E L.coordinates)
  complex_scalar := ArchimedeanCoordinates.CM.scalar E (OppositeCoordinates.CM.coordinates E L.coordinates)
  complex_star := ArchimedeanCoordinates.CM.star E (OppositeCoordinates.CM.coordinates E L.coordinates)
  basisV := ArchimedeanBases.CM.hermitian E (B := B)
  basisP := ArchimedeanBases.CM.skew E (OppositeCoordinates.CM.coordinates E L.coordinates)
  positive v _ := ArchimedeanSignMatrices.CM.positive E (d := d) v
  distinguished_sign _ := by simp [ArchimedeanSignMatrices.CM.positive]
  formV v :=
    (ArchimedeanBases.CM.hermitian_form E
      (OppositeCoordinates.CM.coordinates E L.coordinates) v).trans
      (congrArg Matrix.diagonal (funext (ArchimedeanSignMatrices.CM.hermitian_sign E v)))
  formP v :=
    (ArchimedeanBases.CM.skew_form E
      (OppositeCoordinates.CM.coordinates E L.coordinates) v).trans
      (congrArg Matrix.diagonal (funext fun _ => ArchimedeanSignMatrices.CM.skew_sign E L v))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic.CM
