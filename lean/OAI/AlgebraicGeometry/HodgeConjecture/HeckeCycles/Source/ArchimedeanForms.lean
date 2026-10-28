import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms

/-! # Archimedean Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM

noncomputable section

/-! The actual source forms in their complex completion coordinates,
with nonzero real coefficients for orthonormalization. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem localized_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) (QuadraticForms.CM.Coefficients E C))
    (v : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) M (.inl (ArchimedeanPlaces.CM.enumeration E places v))).map (ArchimedeanCoordinates.CM.complexCoordinate E C v) =
      fun i j => ReferenceDatum.CM.embeddings E places v (QuadraticConjugation.CM.Field.fieldEquiv E C (M i j)) := by
  ext i j
  exact ArchimedeanCoordinates.CM.rational_compatibility E C v (M i j)

theorem real_element (x : E) (hx : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x = x) (v : Fin places.count) :
    (ReferenceDatum.CM.embeddings E places v x).im = 0 := by
  have h := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E (ReferenceDatum.CM.embeddings E places v).toRingHom x
  rw [hx] at h
  have hi := congrArg Complex.im h
  change (ReferenceDatum.CM.embeddings E places v x).im = -(ReferenceDatum.CM.embeddings E places v x).im at hi
  linarith

theorem imaginary_element (x : E) (hx : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x = -x) (v : Fin places.count) :
    (ReferenceDatum.CM.embeddings E places v x).re = 0 := by
  have h := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E (ReferenceDatum.CM.embeddings E places v).toRingHom x
  rw [hx, map_neg] at h
  have hi := congrArg Complex.re h
  change -(ReferenceDatum.CM.embeddings E places v x).re = (ReferenceDatum.CM.embeddings E places v x).re at hi
  linarith

def hermitianReal (v : Fin places.count) (i : Fin 3) : ℝ :=
  (ReferenceDatum.CM.embeddings E places v (QuadraticForms.CM.coefficient E (B := B) i)).re

def skewReal (v : Fin places.count) : ℝ := (ReferenceDatum.CM.embeddings E places v (QuadraticForms.CM.skewCoefficient E C)).im

theorem hermitian_ne_zero (v : Fin places.count) (i : Fin 3) :
    hermitianReal E (B := B) v i ≠ 0 := by
  intro h
  apply QuadraticForms.CM.coefficient_ne_zero E i
  apply (ReferenceDatum.CM.embeddings E places v).injective
  rw [map_zero]
  exact Complex.ext h (real_element E _ (QuadraticForms.CM.coefficient_real E i) v)

theorem skew_ne_zero (v : Fin places.count) : skewReal E C v ≠ 0 := by
  intro h
  apply QuadraticForms.CM.skewCoefficient_ne_zero E C
  apply (ReferenceDatum.CM.embeddings E places v).injective
  rw [map_zero]
  exact Complex.ext (imaginary_element E _ (QuadraticForms.CM.skewCoefficient_imaginary E C) v) h

theorem hermitian_matrix (v : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C).val (.inl (ArchimedeanPlaces.CM.enumeration E places v))).map
      (ArchimedeanCoordinates.CM.complexCoordinate E C v) = Matrix.diagonal (fun i => (hermitianReal E (B := B) v i : ℂ)) := by
  rw [localized_matrix, QuadraticForms.CM.hermitianForm_val]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    apply Complex.ext
    · rfl
    · exact real_element E _ (QuadraticForms.CM.coefficient_real E i) v
  · simp [hij]

theorem skew_matrix (v : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.skewForm E C).val (.inl (ArchimedeanPlaces.CM.enumeration E places v))).map
      (ArchimedeanCoordinates.CM.complexCoordinate E C v) = Matrix.diagonal (fun _ : Fin 1 => (skewReal E C v : ℂ) * Complex.I) := by
  rw [localized_matrix, QuadraticForms.CM.skewForm_val]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    apply Complex.ext
    · simpa using imaginary_element E _ (QuadraticForms.CM.skewCoefficient_imaginary E C) v
    · simp [skewReal]
  · simp [hij]

theorem skew_trace_coefficient (v : Fin places.count) :
    skewReal E C v = -2 * (ReferenceDatum.CM.embeddings E places v (C.delta * C.a)).im := by
  simp [skewReal, QuadraticForms.CM.skewCoefficient, map_ofNat, Complex.mul_im, Complex.mul_re]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM
