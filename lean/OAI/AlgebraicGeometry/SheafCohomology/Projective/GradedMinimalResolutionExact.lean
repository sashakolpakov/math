import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionStep

/-! # Graded Minimal Resolution Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionExact

noncomputable section

/-! Consecutive free resolution maps are exact, and the final free map is injective. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

theorem minimalGradedResolutionStep_exact (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Function.Exact (GradedMinimalResolutionStep.minimalGradedResolutionStep (GradedMinimalSyzygy.minimalGradedSyzygy D)) (GradedMinimalResolutionStep.minimalGradedResolutionStep D) := by
  intro x
  constructor
  · intro hx
    apply (GradedMinimalResolutionStep.minimalGradedResolutionStep_exact_projection (GradedMinimalSyzygy.minimalGradedSyzygy D) x).mp
    have hinj : Function.Injective (fun y : (GradedMinimalSyzygy.minimalGradedSyzygy D).Carrier =>
        (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm (GradedMinimalSyzygy.minimalGradedKernelInclusion D y)) :=
      (GradedMinimalFiniteCover.augmentationFinFreeEquiv D).symm.injective.comp Subtype.val_injective
    apply hinj
    simpa only [GradedMinimalResolutionStep.minimalGradedResolutionStep, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hx
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (GradedMinimalResolutionStep.minimalGradedResolutionStep_comp D) y

theorem iteratedMinimalGradedSyzygy_succ (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) (n : ℕ) :
    GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D (n + 1) = GradedMinimalSyzygy.minimalGradedSyzygy (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D n) := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D)

theorem minimalGradedResolution_lastStep_injective {r : ℕ}
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (r + 1)) K) :
    Function.Injective (GradedMinimalResolutionStep.minimalGradedResolutionStep (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D r)) := by
  have : Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.minimalGradedSyzygy (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D r))) := by
    rw [← iteratedMinimalGradedSyzygy_succ]
    exact GradedMinimalSyzygy.iteratedMinimalGradedSyzygy_projective (r + 1) D
  exact GradedMinimalResolutionStep.minimalGradedResolutionStep_injective_of_projective_syzygy _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalResolutionExact
