import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts

/-! # Evaluated Coefficient Module -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EvaluatedCoefficientModule.GradedModules

noncomputable section

/-! A polynomial module over an algebra acquires the compatible larger-coefficient action by evaluation. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u}
variable (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
variable [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

def evaluatedCoefficientHom : MvPolynomial σ S →ₐ[S] S :=
  MvPolynomial.aeval (fun i => algebraMap (MvPolynomial σ R) S (X i))

theorem evaluatedCoefficientHom_coefficientMap (p : MvPolynomial σ R) :
    evaluatedCoefficientHom R S (algebraMap (MvPolynomial σ R) (MvPolynomial σ S) p) =
      algebraMap (MvPolynomial σ R) S p := by
  rw [MvPolynomial.algebraMap_def]
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.map_C]
    change MvPolynomial.aeval _ (C (algebraMap R S r)) = _
    rw [MvPolynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply R (MvPolynomial σ R) S r
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.map_X]
    change _ * MvPolynomial.aeval _ (X i) = _
    rw [MvPolynomial.aeval_X]

variable (M : Type t) [AddCommGroup M] [Module R M] [Module S M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial σ R) S M]

@[instance_reducible]
def evaluatedCoefficientModule : Module (MvPolynomial σ S) M :=
  Module.compHom M (evaluatedCoefficientHom (σ := σ) R S).toRingHom

omit [Algebra R S] [IsScalarTower R (MvPolynomial σ R) S] [Module R M]
  [Module (MvPolynomial σ R) M] [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial σ R) S M] in
theorem evaluatedCoefficient_tower_scalar :
    let := evaluatedCoefficientModule (σ := σ) R S M
    IsScalarTower S (MvPolynomial σ S) M := by
  let := evaluatedCoefficientModule (σ := σ) R S M
  apply IsScalarTower.of_algebraMap_smul
  intro s m
  change evaluatedCoefficientHom R S (C s) • m = s • m
  rw [show evaluatedCoefficientHom R S (C s) = s from MvPolynomial.aeval_C _ s]

omit [IsScalarTower R (MvPolynomial σ R) S] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M] [IsScalarTower (MvPolynomial σ R) S M] in
theorem evaluatedCoefficient_tower_base :
    let := evaluatedCoefficientModule (σ := σ) R S M
    IsScalarTower R (MvPolynomial σ S) M := by
  let := evaluatedCoefficientModule (σ := σ) R S M
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change evaluatedCoefficientHom R S (C (algebraMap R S r)) • m = r • m
  rw [show evaluatedCoefficientHom R S (C (algebraMap R S r)) = algebraMap R S r from
    MvPolynomial.aeval_C _ _, algebraMap_smul S]

omit [Module R M] [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M] in
theorem evaluatedCoefficient_tower_polynomial :
    let := evaluatedCoefficientModule (σ := σ) R S M
    IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M := by
  let := evaluatedCoefficientModule (σ := σ) R S M
  apply IsScalarTower.of_algebraMap_smul
  intro p m
  change evaluatedCoefficientHom R S (algebraMap (MvPolynomial σ R) (MvPolynomial σ S) p) • m = p • m
  rw [evaluatedCoefficientHom_coefficientMap, algebraMap_smul S]

omit [Algebra R S] [IsScalarTower R (MvPolynomial σ R) S] [Module R M]
  [Module (MvPolynomial σ R) M] [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial σ R) S M] in
theorem evaluatedCoefficient_variable_scalar (i : σ) (m : M) :
    let := evaluatedCoefficientModule (σ := σ) R S M
    X (R := S) i • m = algebraMap (MvPolynomial σ R) S (X i) • m := by
  let := evaluatedCoefficientModule (σ := σ) R S M
  change evaluatedCoefficientHom R S (X i) • m = _
  rw [show evaluatedCoefficientHom R S (X i) = algebraMap (MvPolynomial σ R) S (X i) from
    MvPolynomial.aeval_X _ i]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EvaluatedCoefficientModule.GradedModules
