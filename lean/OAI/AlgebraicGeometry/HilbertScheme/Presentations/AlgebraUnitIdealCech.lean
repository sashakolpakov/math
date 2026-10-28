import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EvaluatedCoefficientModule
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.UnitIdealExactness

/-! # Algebra Unit Ideal Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AlgebraUnitIdealCech.ProjectiveCech

noncomputable section

/-! Actual Čech exactness when coordinate images generate the unit ideal in an acting algebra. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.EvaluatedCoefficientModule.GradedModules

universe u v w t

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
variable [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module S M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M] [IsScalarTower (MvPolynomial σ R) S M]

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem moduleCech_boundary_of_algebra_unit_ideal
    (hunit : Ideal.span (Set.range (fun i : σ => algebraMap (MvPolynomial σ R) S (X i))) = ⊤)
    (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) :
    f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R M q := by
  let := EvaluatedCoefficientModule.GradedModules.evaluatedCoefficientModule (σ := σ) R S M
  let := EvaluatedCoefficientModule.GradedModules.evaluatedCoefficient_tower_scalar (σ := σ) R S M
  let := EvaluatedCoefficientModule.GradedModules.evaluatedCoefficient_tower_base (σ := σ) R S M
  let := EvaluatedCoefficientModule.GradedModules.evaluatedCoefficient_tower_polynomial (σ := σ) R S M
  let E := CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv (σ := σ) R S M
  apply (CoefficientModuleCech.ProjectiveCech.coefficient_moduleCech_boundary_iff R S M q f).mpr
  apply (Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule S M q (E f)).mpr
  apply Cech.UnitIdealExactness.ProjectiveCech.moduleCech_exact_of_scalar_unit_ideal S M
    (fun i : σ => algebraMap (MvPolynomial σ R) S (X i))
    (EvaluatedCoefficientModule.GradedModules.evaluatedCoefficient_variable_scalar R S M) hunit q (E f)
  · exact (CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv_card R S M q f).mpr hf
  · change ModuleCech.Card.ProjectiveCech.moduleCechDifferential S M (CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv R S M f) = 0
    rw [← CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv_differential, hcycle, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AlgebraUnitIdealCech.ProjectiveCech
