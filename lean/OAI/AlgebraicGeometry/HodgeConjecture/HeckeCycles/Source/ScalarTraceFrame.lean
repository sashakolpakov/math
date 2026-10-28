import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis

/-! # Scalar Trace Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTraceFrame.CM

noncomputable section

/-! The literal source symplectic frame is a frame for RadialDilation's rational
trace form, with the original Hermitian matrix and multiplicity scalar. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (B : GeometricSource.CM.BallDatum E)

def matrix : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, B.b]

theorem matrix_hermitian (i j : Fin 3) :
    matrix E B i j = NumberField.IsCMField.complexConj E (matrix E B j i) := by
  have hb : NumberField.IsCMField.complexConj E B.b = B.b := B.conjugate_b
  fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.diagonal, hb]

theorem matrix_det_ne_zero : (matrix E B).det ≠ 0 := by
  have hb : B.b ≠ 0 := by
    intro h
    have hn := B.negative
    rw [h] at hn
    norm_num at hn
  simpa [matrix, Matrix.det_diagonal, Fin.prod_univ_three] using hb

theorem trace (θ : E) (x y : GeometricSource.CM.Vec E) :
    RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E θ (matrix E B) x y = Algebra.trace ℚ E (θ * GeometricSource.CM.hermitian E B.b x y) := by
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply]
  apply congrArg (fun t : E => Algebra.trace ℚ E (θ * t))
  simp [matrix, GeometricSource.CM.hermitian, Fin.sum_univ_succ, Matrix.diagonal, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation,
    mul_comm, mul_left_comm, mul_assoc]

variable {B} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem coordinates (x y : GeometricSource.CM.Vec E) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (ComplexAction.CM.Symplectic.frame E C x) (ComplexAction.CM.Symplectic.frame E C y) =
      RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (C.delta * C.a) (matrix E B) x y := by
  rw [CM.trace]
  calc
    _ = ComplexAction.CM.Symplectic.pairing (ComplexAction.CM.Symplectic.frame E C x) (ComplexAction.CM.Symplectic.frame E C y) := by
      unfold RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing ComplexAction.CM.Symplectic.pairing
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := ComplexAction.CM.Symplectic.frame_pairing E C x y

theorem coefficient_ne_zero : C.delta * C.a ≠ 0 := mul_ne_zero C.delta_ne_zero C.a_ne_zero

theorem coefficient_imaginary :
    NumberField.IsCMField.complexConj E (C.delta * C.a) = -(C.delta * C.a) := by
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (C.delta * C.a) = _
  rw [map_mul, C.delta_imaginary, C.a_real, neg_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTraceFrame.CM
