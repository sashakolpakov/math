import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionCokernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedResolutionTermination
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialZero

/-! # Complex Resolution Terminal -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionTerminal

noncomputable section

/-! At the projective terminal stage, the actual cokernel sheaf is a finite sum of twists. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField

theorem differential_zero_of_projective
    (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) [Projective (GradedSyzygyDimension.gradedModuleObject D)] :
    ComplexMinimalResolution.ComplexResolution.differential j D hD 0 = 0 :=
  GradedPolynomialZero.MvPolynomial.coordinateGradedPolynomialSheafMap_zero (R := ℂ) j
    (GradedMinimalFiniteCover.augmentationFinWeight D) (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
    (GradedMinimalResolutionStep.minimalGradedResolutionStep D) (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD)
    (GradedResolutionTermination.minimalGradedResolutionStep_zero_of_projective D)

def cokernelSheafIsoFreeOfProjective
    (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) [Projective (GradedSyzygyDimension.gradedModuleObject D)] :
    ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D hD ≅ ComplexMinimalResolution.ComplexResolution.freeSheaf j D :=
  cokernelIsoOfEq (differential_zero_of_projective j D hD) ≪≫ cokernelZeroIsoTarget

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionTerminal
