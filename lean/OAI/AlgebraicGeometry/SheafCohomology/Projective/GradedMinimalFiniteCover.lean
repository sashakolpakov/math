import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNonnegativeSyzygy
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedLinearEquiv

/-! # Graded Minimal Finite Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFiniteCover

noncomputable section

/-! Natural-degree finite-index coordinates for the minimal homogeneous free cover. -/

set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

def augmentationRank (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) : ℕ := by
  letI := GradedAugmentationBasisLift.augmentationBasisIndexFintype D
  exact Fintype.card (GradedAugmentationBasisLift.AugmentationBasisIndex D)

def augmentationIndexFinEquiv (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Fin (augmentationRank D) ≃ GradedAugmentationBasisLift.AugmentationBasisIndex D := by
  letI := GradedAugmentationBasisLift.augmentationBasisIndexFintype D
  exact (Fintype.equivFin (GradedAugmentationBasisLift.AugmentationBasisIndex D)).symm

def augmentationFinWeight (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : Fin (augmentationRank D)) : ℕ :=
  GradedNonnegativeSyzygy.augmentationNaturalWeight D (augmentationIndexFinEquiv D i)

def augmentationFinFreeModule (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K :=
  HomogeneousPolynomialMatrix.weightedFreePolynomialModule (fun i => (augmentationFinWeight D i : ℤ))

def augmentationFinFreeEquiv (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (augmentationFinFreeModule D).Carrier ≃ₗ[MvPolynomial σ K] (GradedMinimalFreeCover.augmentationFreeModule D).Carrier :=
  Finsupp.domLCongr (augmentationIndexFinEquiv D)

theorem augmentationFinFreeEquiv_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (d : ℤ) (x : Fin (augmentationRank D) →₀ MvPolynomial σ K)
    (hx : x ∈ (augmentationFinFreeModule D).grading d) :
    augmentationFinFreeEquiv D x ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d := by
  apply (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading K (fun i : GradedAugmentationBasisLift.AugmentationBasisIndex D => i.1) d _).mpr
  intro i
  have h := (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading K (fun k => (augmentationFinWeight D k : ℤ)) d x).mp hx
    ((augmentationIndexFinEquiv D).symm i)
  have hw : (augmentationFinWeight D ((augmentationIndexFinEquiv D).symm i) : ℤ) = i.1 := by
    dsimp only [augmentationFinWeight]
    rw [Equiv.apply_symm_apply, GradedNonnegativeSyzygy.augmentationNaturalWeight_coe D hD i]
  rw [hw] at h
  change x ((augmentationIndexFinEquiv D).symm i) ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K (d - i.1)
  exact h

theorem augmentationFinFreeEquiv_symm_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (d : ℤ) (x : (GradedMinimalFreeCover.augmentationFreeModule D).Carrier)
    (hx : x ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d) :
    (augmentationFinFreeEquiv D).symm x ∈ (augmentationFinFreeModule D).grading d :=
  GradedLinearEquiv.gradedLinearEquiv_symm_homogeneous _ _ ((augmentationFinFreeEquiv D).restrictScalars K)
    (augmentationFinFreeEquiv_homogeneous D hD) d x hx

def augmentationFinProjection (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (augmentationFinFreeModule D).Carrier →ₗ[MvPolynomial σ K] D.Carrier :=
  (GradedMinimalFreeCover.augmentationFreeProjection D).comp (augmentationFinFreeEquiv D).toLinearMap

theorem augmentationFinProjection_surjective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Function.Surjective (augmentationFinProjection D) :=
  (GradedMinimalFreeCover.augmentationFreeProjection_surjective D).comp (augmentationFinFreeEquiv D).surjective

theorem augmentationFinProjection_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (d : ℤ) (x : (augmentationFinFreeModule D).Carrier)
    (hx : x ∈ (augmentationFinFreeModule D).grading d) :
    augmentationFinProjection D x ∈ D.grading d :=
  GradedMinimalFreeCover.augmentationFreeProjection_homogeneous D d _ (augmentationFinFreeEquiv_homogeneous D hD d x hx)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFiniteCover
