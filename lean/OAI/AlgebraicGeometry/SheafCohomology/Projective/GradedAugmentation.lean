import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayama
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleMk

/-! # Graded Augmentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentation

noncomputable section

/-! The augmentation submodule is homogeneous, so its quotient inherits a grading. -/

open DirectSum _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

theorem polynomialAugmentationIdeal_homogeneous :
    (GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ)).IsHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) := by
  intro d p hp
  change constantCoeff (decompose (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) p d).val = 0
  by_cases hd : d = 0
  · subst d
    rw [GradedPolynomialConstantComponent.polynomialIntegerGrading_decompose_zero, constantCoeff_C]
    exact hp
  · change AddMonoidAlgebra.coeff (decompose (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) p d).val 0 = 0
    by_contra hn
    have hdegree := (decompose (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) p d).property hn
    have hzero : (0 : ℤ) = d := by simpa using hdegree
    exact hd hzero.symm

theorem polynomialAugmentation_smul_top_homogeneous
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ] :
    (GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) • (⊤ : Submodule (MvPolynomial σ R) M)).IsHomogeneous ℳ := by
  intro d x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro p hp x _
    induction x using Decomposition.inductionOn ℳ with
    | zero => simp
    | add x y hx hy =>
        rw [smul_add, decompose_add]
        exact Submodule.add_mem _ (hx (by trivial)) (hy (by trivial))
    | homogeneous x =>
        rw [GradedCyclicSubmodule.homogeneous_smul_component (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ x.property]
        exact Submodule.smul_mem_smul (polynomialAugmentationIdeal_homogeneous _ hp) (by trivial)
  · intro x y hx hy
    rw [decompose_add]
    exact Submodule.add_mem _ hx hy

def gradedAugmentationQuotient (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R := by
  let P := GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) •
    (⊤ : Submodule (MvPolynomial σ R) D.Carrier)
  let ℳ := GradedModuleMk.GradedModuleQuotient.grading D.grading P
  letI := GradedModuleMk.GradedModuleQuotient.quotientDecomposition D.grading P
    (polynomialAugmentation_smul_top_homogeneous D.grading)
  exact { Carrier := D.Carrier ⧸ P, grading := ℳ }

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentation
