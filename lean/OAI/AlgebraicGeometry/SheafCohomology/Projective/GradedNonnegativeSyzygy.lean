import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalSyzygy
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleLowerBound

/-! # Graded Nonnegative Syzygy -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNonnegativeSyzygy

noncomputable section

/-! Minimal homogeneous resolutions preserve nonnegative generator degrees. -/

set_option backward.isDefEq.respectTransparency false
open DirectSum
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

def HasNonnegativeGrading {R : Type u} [CommRing R]
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) : Prop :=
  ∀ d : ℤ, d < 0 → D.grading d = ⊥

theorem augmentationBasisDegree_nonnegative (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : HasNonnegativeGrading D) (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) : 0 ≤ i.1 := by
  by_contra hi
  have hz : GradedAugmentationBasisLift.augmentationBasisLift D i = 0 :=
    (hD i.1 (lt_of_not_ge hi)).le (GradedAugmentationBasisLift.augmentationBasisLift_homogeneous D i)
  have h := GradedAugmentationBasisLift.augmentationProjection_basisLift D i
  rw [hz, map_zero] at h
  exact (GradedAugmentationBasisLift.augmentationBasis D).ne_zero i h.symm

theorem augmentationFreeModule_nonnegative (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : HasNonnegativeGrading D) : HasNonnegativeGrading (GradedMinimalFreeCover.augmentationFreeModule D) := by
  intro d hd
  change HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading K (fun i : GradedAugmentationBasisLift.AugmentationBasisIndex D => i.1) d = ⊥
  apply GradedModuleLowerBound.weightedFreeGrading_eq_bot_of_lt
  intro i
  exact hd.trans_le (augmentationBasisDegree_nonnegative D hD i)

theorem minimalGradedSyzygy_nonnegative (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : HasNonnegativeGrading D) : HasNonnegativeGrading (GradedMinimalSyzygy.minimalGradedSyzygy D) := by
  intro d hd
  apply eq_bot_iff.mpr
  intro x hx
  have hx' := GradedMinimalSyzygy.minimalGradedKernelInclusion_homogeneous D d x hx
  have hz : GradedMinimalSyzygy.minimalGradedKernelInclusion D x = 0 :=
    (augmentationFreeModule_nonnegative D hD d hd).le hx'
  exact Subtype.ext hz

theorem iteratedMinimalGradedSyzygy_nonnegative (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : HasNonnegativeGrading D) (n : ℕ) :
    HasNonnegativeGrading (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D n) := by
  induction n generalizing D with
  | zero => exact hD
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D) (minimalGradedSyzygy_nonnegative D hD)

def augmentationNaturalWeight (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) : ℕ := i.1.toNat

theorem augmentationNaturalWeight_coe (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : HasNonnegativeGrading D) (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) :
    (augmentationNaturalWeight D i : ℤ) = i.1 := by
  exact Int.toNat_of_nonneg (augmentationBasisDegree_nonnegative D hD i)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNonnegativeSyzygy
