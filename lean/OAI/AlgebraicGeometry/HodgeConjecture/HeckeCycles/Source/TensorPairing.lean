import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms

/-! # Tensor Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorPairing.CM

noncomputable section

/-! The AdelicSplitting trace tensor pairing is exactly the alternating form supplied
by the original ball-theta source, after rational trace to Q. -/

open scoped Classical _root_.Matrix Kronecker
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def tensorVector (x : GeometricSource.CM.Vec E) : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticConjugation.CM.Field.discriminant E C) 3 1 :=
  fun ij => (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (x ij.1)

theorem tensor_form (x y : GeometricSource.CM.Vec E) :
    QuadraticConjugation.CM.Field.fieldEquiv E C (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue ((QuadraticForms.CM.hermitianForm E C).val ⊗ₖ (QuadraticForms.CM.skewForm E C).val)
      (tensorVector E C x) (tensorVector E C y)) =
        QuadraticForms.CM.skewCoefficient E C * GeometricSource.CM.hermitian E B.b y x := by
  rw [QuadraticForms.CM.hermitianForm_val, QuadraticForms.CM.skewForm_val, Matrix.diagonal_kronecker_diagonal]
  unfold RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue
  simp only [dotProduct, Matrix.mulVec_diagonal, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum, map_mul,
    tensorVector, QuadraticConjugation.CM.fieldEquiv_star, AlgEquiv.apply_symm_apply]
  rw [GeometricSource.CM.hermitian, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (x i) * ((if i = 2 then B.b else 1) * QuadraticForms.CM.skewCoefficient E C * y i) =
    QuadraticForms.CM.skewCoefficient E C * ((if i = 2 then B.b else 1) * y i * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (x i))
  ring

theorem trace_half (z : QuadraticForms.CM.Coefficients E C) :
    Algebra.trace ℚ (QuadraticConjugation.CM.Field.RealField E) (QuadraticAlgebra.trace z / 2) =
      Algebra.trace ℚ E (QuadraticConjugation.CM.Field.fieldEquiv E C z) / 2 := by
  have h := QuadraticTrace.CM.rational_trace E C z
  have hs : QuadraticAlgebra.trace z / 2 = (1 / 2 : ℚ) • QuadraticAlgebra.trace z := by
    simp only [Algebra.smul_def, map_div₀, map_one, map_ofNat]
    ring
  rw [hs, map_smul, h]
  change (1 / 2 : ℚ) * Algebra.trace ℚ E (QuadraticConjugation.CM.Field.fieldEquiv E C z) = _
  ring

theorem source_pairing (x y : GeometricSource.CM.Vec E) :
    Algebra.trace ℚ (QuadraticConjugation.CM.Field.RealField E)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticConjugation.CM.Field.discriminant E C) 3 1 (QuadraticForms.CM.hermitianForm E C).val (QuadraticForms.CM.skewForm E C).val
        (tensorVector E C x) (tensorVector E C y)) =
      Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by
  unfold RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing
  rw [trace_half, tensor_form, QuadraticTrace.CM.source_trace_as_conjugate_first E C x y]
  have hs : QuadraticForms.CM.skewCoefficient E C * GeometricSource.CM.hermitian E B.b y x =
      (2 : ℚ) • (-C.delta * C.a * GeometricSource.CM.hermitian E B.b y x) := by
    simp only [QuadraticForms.CM.skewCoefficient, Algebra.smul_def, map_ofNat]
    ring
  rw [hs, map_smul]
  change (2 * Algebra.trace ℚ E (-C.delta * C.a * GeometricSource.CM.hermitian E B.b y x)) / 2 = _
  ring

theorem coordinate_pairing (x y : GeometricSource.CM.Vec E) :
    Algebra.trace ℚ (QuadraticConjugation.CM.Field.RealField E)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticConjugation.CM.Field.discriminant E C) 3 1 (QuadraticForms.CM.hermitianForm E C).val (QuadraticForms.CM.skewForm E C).val
        (tensorVector E C x) (tensorVector E C y)) =
      ∑ j, ((C.rational x).1 j * (C.rational y).2 j - (C.rational y).1 j * (C.rational x).2 j) := by
  rw [source_pairing, C.symplectic]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorPairing.CM
