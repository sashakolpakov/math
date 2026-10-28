import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousVectorSpaceBasis

/-! # Graded Augmentation Basis Lift -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationBasisLift

noncomputable section

/-! Homogeneous lifts of a basis of the augmentation quotient. -/

universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

abbrev AugmentationBasisIndex (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :=
  HomogeneousVectorSpaceBasis.HomogeneousBasisIndex (GradedAugmentation.gradedAugmentationQuotient D).grading

def augmentationBasis (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Module.Basis (AugmentationBasisIndex D) K (GradedAugmentation.gradedAugmentationQuotient D).Carrier :=
  HomogeneousVectorSpaceBasis.homogeneousVectorSpaceBasis (GradedAugmentation.gradedAugmentationQuotient D).grading

@[instance_reducible]
def augmentationBasisIndexFintype (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Fintype (AugmentationBasisIndex D) := by
  letI := GradedAugmentationFinite.gradedAugmentationQuotient_finite D
  exact HomogeneousVectorSpaceBasis.homogeneousBasisIndexFintype (GradedAugmentation.gradedAugmentationQuotient D).grading

def augmentationProjection (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    D.Carrier →ₗ[MvPolynomial σ K] (GradedAugmentation.gradedAugmentationQuotient D).Carrier :=
  (GradedNakayama.polynomialAugmentationIdeal (R := K) (σ := σ) •
    (⊤ : Submodule (MvPolynomial σ K) D.Carrier)).mkQ

theorem exists_augmentationBasisLift (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : AugmentationBasisIndex D) :
    ∃ x : D.Carrier, x ∈ D.grading i.1 ∧ augmentationProjection D x = augmentationBasis D i :=
  HomogeneousVectorSpaceBasis.homogeneousVectorSpaceBasis_mem (GradedAugmentation.gradedAugmentationQuotient D).grading i

def augmentationBasisLift (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : AugmentationBasisIndex D) : D.Carrier :=
  Classical.choose (exists_augmentationBasisLift D i)

theorem augmentationBasisLift_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : AugmentationBasisIndex D) : augmentationBasisLift D i ∈ D.grading i.1 :=
  (Classical.choose_spec (exists_augmentationBasisLift D i)).1

theorem augmentationProjection_basisLift (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : AugmentationBasisIndex D) :
    augmentationProjection D (augmentationBasisLift D i) = augmentationBasis D i :=
  (Classical.choose_spec (exists_augmentationBasisLift D i)).2

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationBasisLift
