import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFreeCover

/-! # Graded Minimal Cover Residues -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverResidues

noncomputable section

/-! The minimal homogeneous cover induces the chosen basis on augmentation quotients. -/

set_option backward.isDefEq.respectTransparency false
open _root_.MvPolynomial
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

theorem augmentationBasis_repr_projection (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (x : GradedAugmentationBasisLift.AugmentationBasisIndex D →₀ MvPolynomial σ K) (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) :
    (GradedAugmentationBasisLift.augmentationBasis D).repr (GradedAugmentationBasisLift.augmentationProjection D (GradedMinimalFreeCover.augmentationFreeProjection D x)) i =
      constantCoeff (x i) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single j p =>
      erw [GradedMinimalFreeCover.augmentationFreeProjection, Finsupp.linearCombination_single,
        (GradedAugmentationBasisLift.augmentationProjection D).map_smul, GradedAugmentationFinite.gradedAugmentationQuotient_smul,
        GradedAugmentationBasisLift.augmentationProjection_basisLift, map_smul, Module.Basis.repr_self]
      by_cases h : j = i
      · subst j
        simp
      · simp [Ne.symm h]

theorem augmentationFreeProjection_kernel_constantCoeff_zero
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) (x : GradedAugmentationBasisLift.AugmentationBasisIndex D →₀ MvPolynomial σ K)
    (hx : GradedMinimalFreeCover.augmentationFreeProjection D x = 0) (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) :
    constantCoeff (x i) = 0 := by
  rw [← augmentationBasis_repr_projection D x i, hx, map_zero, map_zero, Finsupp.zero_apply]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverResidues
