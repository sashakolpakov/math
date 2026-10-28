import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionStep

/-! # Graded Resolution Termination -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedResolutionTermination

noncomputable section

/-! A projective graded module has zero minimal syzygy. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

theorem minimalGradedSyzygy_subsingleton_of_projective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    [Projective (GradedSyzygyDimension.gradedModuleObject D)] : Subsingleton (GradedMinimalSyzygy.minimalGradedSyzygy D).Carrier := by
  have hk := LinearMap.ker_eq_bot.mpr (GradedFree.augmentationFreeProjection_injective_of_projective D)
  change Subsingleton (GradedMinimalFreeCover.augmentationFreeProjection D).ker
  rw [hk]
  infer_instance

theorem minimalGradedResolutionStep_zero_of_projective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    [Projective (GradedSyzygyDimension.gradedModuleObject D)] : GradedMinimalResolutionStep.minimalGradedResolutionStep D = 0 := by
  have := minimalGradedSyzygy_subsingleton_of_projective D
  ext x
  change (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm
    (GradedMinimalSyzygy.minimalGradedKernelInclusion D (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D) x)) = 0
  rw [Subsingleton.elim (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D) x) 0, map_zero, map_zero]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedResolutionTermination
