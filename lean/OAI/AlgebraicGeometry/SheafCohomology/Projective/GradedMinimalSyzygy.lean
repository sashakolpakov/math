import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedFree

/-! # Graded Minimal Syzygy -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalSyzygy

noncomputable section

/-! The syzygy of the homogeneous augmentation-basis cover. -/

set_option backward.isDefEq.respectTransparency false
open DirectSum _root_.CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]

def minimalGradedSyzygy (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K := by
  let p := GradedMinimalFreeCover.augmentationFreeProjection D
  let ℳ := fun d => ((GradedMinimalFreeCover.augmentationFreeModule D).grading d).comap (p.ker.subtype.restrictScalars K)
  have hker : p.ker.IsHomogeneous (GradedMinimalFreeCover.augmentationFreeModule D).grading :=
    HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.homogeneous_kernel (GradedMinimalFreeCover.augmentationFreeModule D).grading D.grading p
      (GradedMinimalFreeCover.augmentationFreeProjection_homogeneous D)
  letI : Decomposition ℳ := HilbertScheme.Presentations.Homogeneous.SubmoduleGrading.GradedModules.homogeneousSubmoduleDecomposition
    (GradedMinimalFreeCover.augmentationFreeModule D).grading (p.ker.restrictScalars K) hker
  letI : SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) K) ℳ :=
    { smul_mem := by
        intro n d a x ha hx
        change x.val ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d at hx
        change a • x.val ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading (n + d)
        exact SetLike.GradedSMul.smul_mem ha hx }
  exact { Carrier := p.ker, grading := ℳ }

def minimalGradedKernelInclusion (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (minimalGradedSyzygy D).Carrier →ₗ[MvPolynomial σ K] (GradedMinimalFreeCover.augmentationFreeModule D).Carrier :=
  (GradedMinimalFreeCover.augmentationFreeProjection D).ker.subtype

theorem minimalGradedKernelInclusion_homogeneous (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
    (d : ℤ) (x : (minimalGradedSyzygy D).Carrier)
    (hx : x ∈ (minimalGradedSyzygy D).grading d) :
    minimalGradedKernelInclusion D x ∈ (GradedMinimalFreeCover.augmentationFreeModule D).grading d := hx

def minimalGradedCoverShortComplex (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    ShortComplex (ModuleCat (MvPolynomial σ K)) :=
  ModuleCat.shortComplexOfCompEqZero (minimalGradedKernelInclusion D) (GradedMinimalFreeCover.augmentationFreeProjection D)
    (by ext x; exact x.property)

theorem minimalGradedCoverShortComplex_shortExact (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    (minimalGradedCoverShortComplex D).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_ker_map (GradedMinimalFreeCover.augmentationFreeProjection D))
    Subtype.val_injective (GradedMinimalFreeCover.augmentationFreeProjection_surjective D)

theorem augmentationFreeModule_projective (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalFreeCover.augmentationFreeModule D)) := by
  let : Module.Free (MvPolynomial σ K) (GradedMinimalFreeCover.augmentationFreeModule D).Carrier := by
    dsimp only [GradedMinimalFreeCover.augmentationFreeModule]
    infer_instance
  exact ModuleCat.projective_of_free
    (Module.Free.chooseBasis (MvPolynomial σ K) (GradedMinimalFreeCover.augmentationFreeModule D).Carrier)

theorem minimalGradedSyzygy_hasProjectiveDimensionLE (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) (n : ℕ)
    [HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject D) (n + 1)] :
    HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject (minimalGradedSyzygy D)) n := by
  have h := (inferInstance : HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject D) (n + 1))
  exact ((minimalGradedCoverShortComplex_shortExact D).hasProjectiveDimensionLT_X₃_iff n
    (augmentationFreeModule_projective D)).mp h

def iteratedMinimalGradedSyzygy (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) :
    ℕ → HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K
  | 0 => D
  | n + 1 => iteratedMinimalGradedSyzygy (minimalGradedSyzygy D) n

theorem iteratedMinimalGradedSyzygy_hasProjectiveDimensionLE
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K) (k n : ℕ)
    [HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject D) (n + k)] :
    HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D k)) n := by
  induction k generalizing D with
  | zero => simpa only [Nat.add_zero, GradedMinimalSyzygy.iteratedMinimalGradedSyzygy] using
      (inferInstance : HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject D) (n + 0))
  | succ k ih =>
      have : HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject (minimalGradedSyzygy D)) (n + k) :=
        minimalGradedSyzygy_hasProjectiveDimensionLE D (n + k)
      exact ih (minimalGradedSyzygy D)

theorem iteratedMinimalGradedSyzygy_projective (r : ℕ)
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin r) K) :
    Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D r)) := by
  have : HasProjectiveDimensionLE (GradedSyzygyDimension.gradedModuleObject D) (0 + r) := by
    simpa only [Nat.zero_add] using
      HilbertSyzygyM.HilbertSyzygy.hasProjectiveDimensionLE_of_field K r (GradedSyzygyDimension.gradedModuleObject D)
  have := iteratedMinimalGradedSyzygy_hasProjectiveDimensionLE D r 0
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr this

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalSyzygy
