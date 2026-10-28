import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame

/-! # Real Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM

noncomputable section

/-! The source forms have explicit real diagonal coefficients and a purely
imaginary multiplicity coefficient in the quadratic presentation. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def hermitianCoefficient (i : Fin 3) : QuadraticConjugation.CM.Field.RealField E :=
  ⟨QuadraticForms.CM.coefficient E (B := B) i, (NumberField.IsCMField.complexConj_eq_self_iff E _).mp
    (QuadraticForms.CM.coefficient_real E i)⟩

def multiplicityCoefficient : QuadraticConjugation.CM.Field.RealField E :=
  ⟨C.a, (NumberField.IsCMField.complexConj_eq_self_iff E _).mp C.a_real⟩

def skewCoefficient : QuadraticConjugation.CM.Field.RealField E := -2 * multiplicityCoefficient E C

theorem hermitianCoefficient_ne_zero (i : Fin 3) : hermitianCoefficient E (B := B) i ≠ 0 := by
  intro hi
  exact QuadraticForms.CM.coefficient_ne_zero E i (congrArg (fun r : QuadraticConjugation.CM.Field.RealField E => (r : E)) hi)

theorem multiplicityCoefficient_ne_zero : multiplicityCoefficient E C ≠ 0 := by
  intro hi
  exact C.a_ne_zero (congrArg (fun r : QuadraticConjugation.CM.Field.RealField E => (r : E)) hi)

theorem skewCoefficient_ne_zero : skewCoefficient E C ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (multiplicityCoefficient_ne_zero E C)

theorem hermitian_coefficient (i : Fin 3) :
    (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (QuadraticForms.CM.coefficient E (B := B) i) =
      algebraMap (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.Coefficients E C) (hermitianCoefficient E (B := B) i) := by
  apply (QuadraticConjugation.CM.Field.fieldEquiv E C).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

theorem skew_coefficient :
    (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (QuadraticForms.CM.skewCoefficient E C) =
      (⟨0, skewCoefficient E C⟩ : QuadraticForms.CM.Coefficients E C) := by
  apply (QuadraticConjugation.CM.Field.fieldEquiv E C).injective
  rw [AlgEquiv.apply_symm_apply]
  change QuadraticForms.CM.skewCoefficient E C = QuadraticConjugation.CM.Field.toOriginal E C ⟨0, skewCoefficient E C⟩
  rw [QuadraticConjugation.CM.Field.toOriginal_apply]
  change -2 * C.delta * C.a = 0 + (-2 * C.a) * C.delta
  ring

theorem hermitian_form : (QuadraticForms.CM.hermitianForm E C).val =
    DiagonalFrame.CM.Symplectic.hermitian (QuadraticConjugation.CM.Field.discriminant E C) (hermitianCoefficient E (B := B)) := by
  rw [QuadraticForms.CM.hermitianForm_val]
  congr 1
  funext i
  exact hermitian_coefficient E C i

theorem skew_form : (QuadraticForms.CM.skewForm E C).val =
    DiagonalFrame.CM.Symplectic.skew (QuadraticConjugation.CM.Field.discriminant E C) (skewCoefficient E C) := by
  rw [QuadraticForms.CM.skewForm_val]
  congr 1
  funext i
  exact skew_coefficient E C

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM
