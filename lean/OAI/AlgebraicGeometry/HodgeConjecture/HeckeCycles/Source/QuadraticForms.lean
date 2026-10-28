import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticTrace
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Quadratic Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

noncomputable section

/-! The original Hermitian space and multiplicity line as actual invertible
quadratic-algebra forms. The skew coefficient is -2 delta a: conjugating
the source's linear-first convention changes the sign, and AdelicSplitting divides its
quadratic trace by two. -/

open scoped Classical _root_.Matrix Kronecker
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

abbrev Coefficients := QuadraticAlgebra (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) 0

theorem b_ne_zero : B.b ≠ 0 := by
  intro hb
  have h := B.negative
  rw [hb] at h
  simp at h

def coefficient (j : Fin 3) : E := if j = 2 then B.b else 1

theorem coefficient_ne_zero (j : Fin 3) : coefficient E (B := B) j ≠ 0 := by
  by_cases hj : j = 2
  · simpa only [coefficient, hj, ite_true] using b_ne_zero E (B := B)
  · simp only [coefficient, hj, ite_false, ne_eq, one_ne_zero, not_false_eq_true]

def skewCoefficient : E := -2 * C.delta * C.a

theorem skewCoefficient_ne_zero : skewCoefficient E C ≠ 0 :=
  mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by norm_num)) C.delta_ne_zero) C.a_ne_zero

def diagonalUnit {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R] (u : I → Rˣ) :
    (Matrix I I R)ˣ where
  val := Matrix.diagonal (fun i => (u i).val)
  inv := Matrix.diagonal (fun i => ((u i)⁻¹).val)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have hm : (fun i => (u i).val * ((u i)⁻¹).val) = fun _ => 1 :=
      funext (fun i => (u i).val_inv)
    rw [hm, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have hm : (fun i => ((u i)⁻¹).val * (u i).val) = fun _ => 1 :=
      funext (fun i => (u i).inv_val)
    rw [hm, Matrix.diagonal_one]

def hermitianForm : (Matrix (Fin 3) (Fin 3) (Coefficients E C))ˣ :=
  diagonalUnit (fun j => Units.map (QuadraticConjugation.CM.Field.fieldEquiv E C).symm.toMonoidHom
    (Units.mk0 (coefficient E (B := B) j) (coefficient_ne_zero E j)))

def skewForm : (Matrix (Fin 1) (Fin 1) (Coefficients E C))ˣ :=
  diagonalUnit (fun _ => Units.map (QuadraticConjugation.CM.Field.fieldEquiv E C).symm.toMonoidHom
    (Units.mk0 (skewCoefficient E C) (skewCoefficient_ne_zero E C)))

theorem hermitianForm_val : (hermitianForm E C).val =
    Matrix.diagonal (fun j => (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (coefficient E (B := B) j)) := rfl

theorem skewForm_val : (skewForm E C).val =
    Matrix.diagonal (fun _ => (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (skewCoefficient E C)) := rfl

theorem coefficient_real (j : Fin 3) : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (coefficient E (B := B) j) = coefficient E (B := B) j := by
  by_cases hj : j = 2
  · simpa only [coefficient, hj, ite_true] using B.conjugate_b
  · simp only [coefficient, hj, ite_false, map_one]

theorem skewCoefficient_imaginary : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (skewCoefficient E C) = -skewCoefficient E C := by
  simp only [skewCoefficient, map_mul, map_neg, map_ofNat, C.delta_imaginary, C.a_real]
  ring

theorem hermitianForm_hermitian : (hermitianForm E C).val.conjTranspose = (hermitianForm E C).val := by
  rw [hermitianForm_val, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  change star ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm (coefficient E (B := B) j)) = _
  rw [← QuadraticConjugation.CM.fieldEquiv_symm_conjugation, coefficient_real]

theorem skewForm_skewHermitian : (skewForm E C).val.conjTranspose = -(skewForm E C).val := by
  rw [skewForm_val, Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext j
  change star ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm (skewCoefficient E C)) = -((QuadraticConjugation.CM.Field.fieldEquiv E C).symm (skewCoefficient E C))
  rw [← QuadraticConjugation.CM.fieldEquiv_symm_conjugation, skewCoefficient_imaginary, map_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
