import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionExact
import OAI.AlgebraicGeometry.SheafCohomology.CechFinrankComparison

/-! # Complex Minimal Resolution -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolution

noncomputable section

/-! The minimal homogeneous resolution realized by actual twist sheaves over the complex numbers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts
local instance complexResolutionField : Field Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) := CechFinrankComparison.Projective.complexBaseSectionsField

def freeSheaf (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) :
    (Proj (MvPolynomial.homogeneousSubmodule σ ℂ)).Modules :=
  ∐ fun i : Fin (GradedMinimalFiniteCover.augmentationRank D) =>
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D i)

def term (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) :
    ℕ → (Proj (MvPolynomial.homogeneousSubmodule σ ℂ)).Modules
  | 0 => freeSheaf j D
  | n + 1 => term j (GradedMinimalSyzygy.minimalGradedSyzygy D) n

def differential (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : ∀ n : ℕ, ComplexResolution.term j D (n + 1) ⟶ ComplexResolution.term j D n
  | 0 => GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap (R := ℂ) j
      (GradedMinimalFiniteCover.augmentationFinWeight D) (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
      (GradedMinimalResolutionStep.minimalGradedResolutionStep D) (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD)
  | n + 1 => differential j (GradedMinimalSyzygy.minimalGradedSyzygy D) (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD) n

theorem differential_comp (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (n : ℕ) :
    ComplexResolution.differential j D hD (n + 1) ≫ ComplexResolution.differential j D hD n = 0 := by
  induction n generalizing D with
  | zero =>
      exact GradedPolynomialComplex.MvPolynomial.coordinateGradedPolynomialSheafMap_comp_zero (R := ℂ) j
        (GradedMinimalFiniteCover.augmentationFinWeight D) (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
        (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy (GradedMinimalSyzygy.minimalGradedSyzygy D)))
        (GradedMinimalResolutionStep.minimalGradedResolutionStep D) (GradedMinimalResolutionStep.minimalGradedResolutionStep (GradedMinimalSyzygy.minimalGradedSyzygy D))
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD)
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous (GradedMinimalSyzygy.minimalGradedSyzygy D)
          (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD)) (GradedMinimalResolutionStep.minimalGradedResolutionStep_comp D)
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D) (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD)

theorem differential_exact (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (n : ℕ) :
    (ShortComplex.mk (ComplexResolution.differential j D hD (n + 1)) (ComplexResolution.differential j D hD n)
      (differential_comp j D hD n)).Exact := by
  induction n generalizing D with
  | zero =>
      exact GradedPolynomialExact.MvPolynomial.coordinateGradedPolynomialShortComplex_exact (R := ℂ) j
        (GradedMinimalFiniteCover.augmentationFinWeight D) (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
        (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy (GradedMinimalSyzygy.minimalGradedSyzygy D)))
        (GradedMinimalResolutionStep.minimalGradedResolutionStep D) (GradedMinimalResolutionStep.minimalGradedResolutionStep (GradedMinimalSyzygy.minimalGradedSyzygy D))
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD)
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous (GradedMinimalSyzygy.minimalGradedSyzygy D)
          (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD)) (GradedMinimalResolutionStep.minimalGradedResolutionStep_comp D)
        (GradedMinimalResolutionExact.minimalGradedResolutionStep_exact D)
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D) (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD)

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolution
