import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AlgebraUnitIdealCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizationCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedAction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CechBoundaries
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading

/-! # Form Localized Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizedCech.ProjectiveCech

noncomputable section

/-! Localization at a homogeneous linear form makes the actual augmented projective Čech complex exact in every degree. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem linearFormLocalized_cech_boundary (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1)
    (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M))
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (Presentations.Module.Fractions.GradedModules.AwayModule l M) q f)
    (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (Presentations.Module.Fractions.GradedModules.AwayModule l M) f = 0) :
    f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R (Presentations.Module.Fractions.GradedModules.AwayModule l M) q := by
  let : Module (Localization.Away l) (Presentations.Module.Fractions.GradedModules.AwayModule l M) := inferInstance
  let : IsScalarTower (MvPolynomial σ R) (Localization.Away l) (Presentations.Module.Fractions.GradedModules.AwayModule l M) := inferInstance
  let : IsScalarTower R (Localization.Away l) (Presentations.Module.Fractions.GradedModules.AwayModule l M) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (Localization.Away l)]
    exact (algebraMap_smul (Localization.Away l) (algebraMap R (MvPolynomial σ R) r) x).trans
      (algebraMap_smul (MvPolynomial σ R) r x)
  exact AlgebraUnitIdealCech.ProjectiveCech.moduleCech_boundary_of_algebra_unit_ideal R (Localization.Away l) (Presentations.Module.Fractions.GradedModules.AwayModule l M)
    (FormLocalizationCover.ProjectiveCech.linearFormLocalization_coordinates_span_top R l hl) q f hf hcycle

theorem linearFormLocalized_moduleCechExactAt
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d q := by
  have hl' : l ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (1 : ℤ) := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
    exact hl
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ l 1 hl'
  let := Localized.GradedAction.GradedModules.localizedDegree_gradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ l 1 hl'
  intro f hf hfc hcycle
  exact Homogeneous.CechBoundaries.ProjectiveCech.homogeneous_moduleCech_boundary R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d q f hf
    (linearFormLocalized_cech_boundary R M l hl q f hfc hcycle)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizedCech.ProjectiveCech
