import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationBasisLift
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayamaGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix

/-! # Graded Minimal Free Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFreeCover

noncomputable section

/-! Lifts of the augmentation basis form a finite homogeneous free cover. -/

open DirectSum
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

def augmentationFreeModule (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K := by
  letI := GradedAugmentationBasisLift.augmentationBasisIndexFintype D
  exact { Carrier := GradedAugmentationBasisLift.AugmentationBasisIndex D →₀ MvPolynomial σ K
          grading := HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading K (fun i : GradedAugmentationBasisLift.AugmentationBasisIndex D => i.1) }

def augmentationFreeProjection (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (augmentationFreeModule D).Carrier →ₗ[MvPolynomial σ K] D.Carrier :=
  Finsupp.linearCombination (MvPolynomial σ K) (GradedAugmentationBasisLift.augmentationBasisLift D)

theorem augmentationFreeProjection_single (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (i : GradedAugmentationBasisLift.AugmentationBasisIndex D) :
    augmentationFreeProjection D (Finsupp.single i 1) = GradedAugmentationBasisLift.augmentationBasisLift D i := by
  erw [augmentationFreeProjection, Finsupp.linearCombination_single, one_smul]

theorem augmentationFreeProjection_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (d : ℤ) (x : (augmentationFreeModule D).Carrier)
    (hx : x ∈ (augmentationFreeModule D).grading d) :
    augmentationFreeProjection D x ∈ D.grading d :=
  HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFree_linearCombination_homogeneous K D.grading
    (fun i : GradedAugmentationBasisLift.AugmentationBasisIndex D => i.1) (GradedAugmentationBasisLift.augmentationBasisLift D)
    (GradedAugmentationBasisLift.augmentationBasisLift_homogeneous D) d x hx

theorem augmentationFreeProjection_range_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (augmentationFreeProjection D).range.IsHomogeneous D.grading := by
  intro d y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨(decompose (augmentationFreeModule D).grading x d).val, ?_⟩
  exact HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.map_homogeneous_component (augmentationFreeModule D).grading D.grading
    (augmentationFreeProjection D).toAddMonoidHom (augmentationFreeProjection_homogeneous D) d x

theorem augmentationFreeProjection_surjective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Function.Surjective (augmentationFreeProjection D) := by
  let P := (augmentationFreeProjection D).range
  let I := GradedNakayama.polynomialAugmentationIdeal (R := K) (σ := σ) •
    (⊤ : Submodule (MvPolynomial σ K) D.Carrier)
  have hmap : P.map (GradedAugmentationBasisLift.augmentationProjection D) = ⊤ := by
    have hb : Submodule.span K (Set.range (GradedAugmentationBasisLift.augmentationBasis D)) ≤
        (P.map (GradedAugmentationBasisLift.augmentationProjection D)).restrictScalars K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨GradedAugmentationBasisLift.augmentationBasisLift D i,
        ⟨Finsupp.single i 1, augmentationFreeProjection_single D i⟩,
        GradedAugmentationBasisLift.augmentationProjection_basisLift D i⟩
    rw [Module.Basis.span_eq] at hb
    exact top_unique hb
  have hsup : I ⊔ P = ⊤ := (I.map_mkQ_eq_top P).mp hmap
  have hP : P = ⊤ := GradedNakayamaGeneration.gradedPolynomial_eq_top_of_augmentation D P
    (augmentationFreeProjection_range_homogeneous D) (by rw [sup_comm]; exact hsup)
  exact LinearMap.range_eq_top.mp hP

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFreeCover
