import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFiniteCover

/-! # Graded Minimal Resolution Step -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionStep

noncomputable section

/-! Exact homogeneous maps between successive finite free terms of the minimal resolution. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

def minimalGradedResolutionStep (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (GradedMinimalFiniteCover.augmentationFinFreeModule (GradedMinimalSyzygy.minimalGradedSyzygy D)).Carrier →ₗ[MvPolynomial σ K]
      (GradedMinimalFiniteCover.augmentationFinFreeModule D).Carrier :=
  (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm.toLinearMap.comp
    ((GradedMinimalSyzygy.minimalGradedKernelInclusion D).comp (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D)))

theorem augmentationFinProjection_resolutionStep (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (x : (GradedMinimalFiniteCover.augmentationFinFreeModule (GradedMinimalSyzygy.minimalGradedSyzygy D)).Carrier) :
    GradedMinimalFiniteCover.augmentationFinProjection D (minimalGradedResolutionStep D x) = 0 := by
  change GradedMinimalFreeCover.augmentationFreeProjection D
    (GradedMinimalFiniteCover.augmentationFinFreeEquiv D ((GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm
      (GradedMinimalSyzygy.minimalGradedKernelInclusion D (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D) x)))) = 0
  rw [LinearEquiv.apply_symm_apply]
  exact (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D) x).property

theorem minimalGradedResolutionStep_exact_projection (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Function.Exact (minimalGradedResolutionStep D) (GradedMinimalFiniteCover.augmentationFinProjection D) := by
  intro x
  constructor
  · intro hx
    let y : (GradedMinimalSyzygy.minimalGradedSyzygy D).Carrier := ⟨GradedMinimalFiniteCover.augmentationFinFreeEquiv D x, hx⟩
    obtain ⟨z, hz⟩ := GradedMinimalFiniteCover.augmentationFinProjection_surjective (GradedMinimalSyzygy.minimalGradedSyzygy D) y
    refine ⟨z, ?_⟩
    change (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm
      (GradedMinimalSyzygy.minimalGradedKernelInclusion D (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D) z)) = x
    rw [hz]
    exact (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm_apply_apply x
  · rintro ⟨y, rfl⟩
    exact augmentationFinProjection_resolutionStep D y

theorem minimalGradedResolutionStep_comp (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (minimalGradedResolutionStep D).comp (minimalGradedResolutionStep (GradedMinimalSyzygy.minimalGradedSyzygy D)) = 0 := by
  ext x
  change (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm
    (GradedMinimalSyzygy.minimalGradedKernelInclusion D (GradedMinimalFiniteCover.augmentationFinProjection (GradedMinimalSyzygy.minimalGradedSyzygy D)
      (minimalGradedResolutionStep (GradedMinimalSyzygy.minimalGradedSyzygy D) x))) = 0
  rw [augmentationFinProjection_resolutionStep, map_zero, map_zero]

theorem minimalGradedResolutionStep_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (d : ℤ)
    (x : (GradedMinimalFiniteCover.augmentationFinFreeModule (GradedMinimalSyzygy.minimalGradedSyzygy D)).Carrier)
    (hx : x ∈ (GradedMinimalFiniteCover.augmentationFinFreeModule (GradedMinimalSyzygy.minimalGradedSyzygy D)).grading d) :
    minimalGradedResolutionStep D x ∈ (GradedMinimalFiniteCover.augmentationFinFreeModule D).grading d :=
  GradedMinimalFiniteCover.augmentationFinFreeEquiv_symm_homogeneous D hD d _
    (GradedMinimalSyzygy.minimalGradedKernelInclusion_homogeneous D d _
      (GradedMinimalFiniteCover.augmentationFinProjection_homogeneous (GradedMinimalSyzygy.minimalGradedSyzygy D)
        (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD) d x hx))

theorem minimalGradedResolutionStep_injective_of_projective_syzygy
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    [Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.minimalGradedSyzygy D))] :
    Function.Injective (minimalGradedResolutionStep D) :=
  (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm.injective.comp
    (Subtype.val_injective.comp
      ((GradedFree.augmentationFreeProjection_injective_of_projective (GradedMinimalSyzygy.minimalGradedSyzygy D)).comp
        (GradedMinimalFiniteCover.augmentationFinFreeEquiv (GradedMinimalSyzygy.minimalGradedSyzygy D)).injective))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionStep
