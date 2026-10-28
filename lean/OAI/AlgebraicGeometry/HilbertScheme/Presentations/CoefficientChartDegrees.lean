import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeScalarRestriction

/-! # Coefficient Chart Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientChartDegrees.ProjectiveCech

noncomputable section

/-! Compatible coefficient enlargement identifies the actual homogeneous chart modules over the original scalar ring. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeScalarRestriction.GradedModules

universe u v w t

variable {σ : Type u} (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (M : Type t) [AddCommGroup M] [Module R M] [Module S M]
  [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ S) M]
  [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ S) M] [IsScalarTower S (MvPolynomial σ S) M]
  [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M]
variable (ℳ : ℤ → Submodule S M)

theorem coefficientModuleChartEquiv_degree (s : Finset σ) (d : ℤ) :
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M (fun i => (ℳ i).restrictScalars R) s d).map
      (CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s).toLinearMap =
        (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree S M ℳ s d).restrictScalars R := by
  rw [CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv, Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree, LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_degree]
  exact Localized.DegreeScalarRestriction.GradedModules.localizedDegreePiece_restrictScalars ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial S s) (s.card : ℤ) d

def coefficientModuleChartDegreeEquiv (s : Finset σ) (d : ℤ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M (fun i => (ℳ i).restrictScalars R) s d ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree S M ℳ s d :=
  (CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s).ofSubmodules _ _ (coefficientModuleChartEquiv_degree R S M ℳ s d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientChartDegrees.ProjectiveCech
