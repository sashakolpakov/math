import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionStep
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness

/-! # Graded Minimal Cover Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverDegree

noncomputable section

/-! The minimal graded cover and its relations in every homogeneous degree. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]
variable (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D)

def augmentationFinProjectionDegree (d : ℤ) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) K (fun i => (GradedMinimalFiniteCover.augmentationFinWeight D i : ℤ)) d →ₗ[K]
      D.grading d :=
  HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap _ _ ((GradedMinimalFiniteCover.augmentationFinProjection D).restrictScalars K)
    (GradedMinimalFiniteCover.augmentationFinProjection_homogeneous D hD) d

theorem augmentationFinProjectionDegree_surjective (d : ℤ) :
    Function.Surjective (augmentationFinProjectionDegree D hD d) :=
  HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap_surjective _ _ ((GradedMinimalFiniteCover.augmentationFinProjection D).restrictScalars K)
    (GradedMinimalFiniteCover.augmentationFinProjection_homogeneous D hD) (GradedMinimalFiniteCover.augmentationFinProjection_surjective D) d

def minimalGradedResolutionStepDegree (d : ℤ) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) K
      (fun i => (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D) i : ℤ)) d →ₗ[K]
      HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) K (fun i => (GradedMinimalFiniteCover.augmentationFinWeight D i : ℤ)) d :=
  HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap _ _ ((GradedMinimalResolutionStep.minimalGradedResolutionStep D).restrictScalars K)
    (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD) d

theorem minimalGradedResolutionStepDegree_exact (d : ℤ) :
    Function.Exact (minimalGradedResolutionStepDegree D hD d)
      (augmentationFinProjectionDegree D hD d) :=
  HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap_exact _ _ _ ((GradedMinimalResolutionStep.minimalGradedResolutionStep D).restrictScalars K)
    ((GradedMinimalFiniteCover.augmentationFinProjection D).restrictScalars K)
    (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD) (GradedMinimalFiniteCover.augmentationFinProjection_homogeneous D hD)
    (GradedMinimalResolutionStep.minimalGradedResolutionStep_exact_projection D) d

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverDegree
