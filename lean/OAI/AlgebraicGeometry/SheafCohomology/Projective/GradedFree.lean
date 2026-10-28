import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverResidues
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SplitKernelAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedSyzygyDimension

/-! # Graded Free -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedFree

noncomputable section

/-! A finite graded projective polynomial module is graded free. -/

set_option backward.isDefEq.respectTransparency false
open DirectSum _root_.CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

theorem augmentationFreeProjection_injective_of_projective
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) [Projective (GradedSyzygyDimension.gradedModuleObject D)] :
    Function.Injective (GradedMinimalFreeCover.augmentationFreeProjection D) := by
  let p := GradedMinimalFreeCover.augmentationFreeProjection D
  let ℳ := fun d => ((GradedMinimalFreeCover.augmentationFreeModule D).grading d).comap (p.ker.subtype.restrictScalars K)
  have hker : p.ker.IsHomogeneous (GradedMinimalFreeCover.augmentationFreeModule D).grading :=
    HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.homogeneous_kernel (GradedMinimalFreeCover.augmentationFreeModule D).grading D.grading p
      (GradedMinimalFreeCover.augmentationFreeProjection_homogeneous D)
  let : Decomposition ℳ := HilbertScheme.Presentations.Homogeneous.SubmoduleGrading.GradedModules.homogeneousSubmoduleDecomposition
    (GradedMinimalFreeCover.augmentationFreeModule D).grading (p.ker.restrictScalars K) hker
  let : SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) K) ℳ :=
    { smul_mem := by
        intro n d a x ha hx
        change x.val ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d at hx
        change a • x.val ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading (n + d)
        exact SetLike.GradedSMul.smul_mem ha hx }
  let : Module.Finite (MvPolynomial σ K) p.ker := inferInstance
  let q : GradedSyzygyDimension.gradedModuleObject (GradedMinimalFreeCover.augmentationFreeModule D) ⟶ GradedSyzygyDimension.gradedModuleObject D := ModuleCat.ofHom p
  have : Epi q := (ModuleCat.epi_iff_surjective q).mpr (GradedMinimalFreeCover.augmentationFreeProjection_surjective D)
  let s : D.Carrier →ₗ[MvPolynomial σ K] (GradedMinimalFreeCover.augmentationFreeModule D).Carrier :=
    (Projective.factorThru (𝟙 (GradedSyzygyDimension.gradedModuleObject D)) q).hom
  have hs : p.comp s = LinearMap.id :=
    ModuleCat.hom_ext_iff.mp (Projective.factorThru_comp (𝟙 (GradedSyzygyDimension.gradedModuleObject D)) q)
  have hsmall : p.ker ≤ GradedNakayama.polynomialAugmentationIdeal (R := K) (σ := σ) • ⊤ := by
    intro x hx
    apply SplitKernelAugmentation.finsupp_mem_ideal_smul_top
    intro i
    exact GradedMinimalCoverResidues.augmentationFreeProjection_kernel_constantCoeff_zero D x hx i
  have : Subsingleton p.ker := GradedNakayama.gradedPolynomial_nakayama ℳ
    (SplitKernelAugmentation.splitKernel_le_ideal_smul_top p s hs (GradedNakayama.polynomialAugmentationIdeal (R := K) (σ := σ)) hsmall)
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : p.ker) 0)

def gradedProjectiveFreeEquiv (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    [Projective (GradedSyzygyDimension.gradedModuleObject D)] :
    (GradedMinimalFreeCover.augmentationFreeModule D).Carrier ≃ₗ[MvPolynomial σ K] D.Carrier :=
  LinearEquiv.ofBijective (GradedMinimalFreeCover.augmentationFreeProjection D)
    ⟨augmentationFreeProjection_injective_of_projective D, GradedMinimalFreeCover.augmentationFreeProjection_surjective D⟩

theorem gradedProjectiveFreeEquiv_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    [Projective (GradedSyzygyDimension.gradedModuleObject D)] (d : ℤ) (x : (GradedMinimalFreeCover.augmentationFreeModule D).Carrier)
    (hx : x ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d) :
    gradedProjectiveFreeEquiv D x ∈ D.grading d :=
  GradedMinimalFreeCover.augmentationFreeProjection_homogeneous D d x hx

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedFree
