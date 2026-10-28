import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization

/-! # Archimedean Bases -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanBases.CM

noncomputable section

/-! Construct the source's actual orthonormal archimedean bases. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def hermitian (v : Fin places.count) : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  DiagonalNormalization.CM.normalizer (ArchimedeanForms.CM.hermitianReal E (B := B) v) (ArchimedeanForms.CM.hermitian_ne_zero E v)

def skew (v : Fin places.count) : (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  DiagonalNormalization.CM.normalizer (fun _ : Fin 1 => ArchimedeanForms.CM.skewReal E C v) (fun _ => ArchimedeanForms.CM.skew_ne_zero E C v)

theorem hermitian_form (v : Fin places.count) :
    (hermitian E (B := B) v).val.conjTranspose *
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C).val (.inl (ArchimedeanPlaces.CM.enumeration E places v))).map
        (ArchimedeanCoordinates.CM.complexCoordinate E C v) * (hermitian E (B := B) v).val =
      Matrix.diagonal (fun i => if 0 < ArchimedeanForms.CM.hermitianReal E (B := B) v i then (1 : ℂ) else -1) := by
  rw [ArchimedeanForms.CM.hermitian_matrix]
  simpa only [hermitian, mul_one] using DiagonalNormalization.CM.form
    (ArchimedeanForms.CM.hermitianReal E (B := B) v) (ArchimedeanForms.CM.hermitian_ne_zero E v) 1

theorem skew_form (v : Fin places.count) :
    (skew E C v).val.conjTranspose *
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.skewForm E C).val (.inl (ArchimedeanPlaces.CM.enumeration E places v))).map
        (ArchimedeanCoordinates.CM.complexCoordinate E C v) * (skew E C v).val =
      Matrix.diagonal (fun _ : Fin 1 => (if 0 < ArchimedeanForms.CM.skewReal E C v then (1 : ℂ) else -1) * Complex.I) := by
  rw [ArchimedeanForms.CM.skew_matrix]
  exact DiagonalNormalization.CM.form _ _ Complex.I

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanBases.CM
