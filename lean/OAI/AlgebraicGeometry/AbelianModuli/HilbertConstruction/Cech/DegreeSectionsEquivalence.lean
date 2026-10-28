import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatAugmentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ExactLeft
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech

/-! # Degree Sections Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DegreeSectionsEquivalence

noncomputable section

/-! Exactness of the augmented homogeneous Čech complex identifies the homogeneous degree piece with its global section kernel. -/

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleCechAugmentationSectionsMap (d : ℤ) :
    HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0 →ₗ[R] HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := σ) R M ℳ d :=
  (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0).codRestrict _
    (fun x => HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d 0 x)

omit [Fintype σ] in
theorem moduleCechAugmentationSectionsMap_bijective (d : ℤ)
    (h0 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 0) (h1 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 1) :
    Function.Bijective (moduleCechAugmentationSectionsMap (σ := σ) R M ℳ d) := by
  constructor
  · intro x y h
    exact HilbertScheme.Presentations.Cech.FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_injective R M ℳ d (HilbertScheme.Presentations.Cech.ExactLeft.ProjectiveCech.moduleCechExactAt_zero_vanish R M ℳ d h0)
      (congrArg Subtype.val h)
  · intro z
    obtain ⟨x, hx⟩ := (HilbertScheme.Presentations.Cech.FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact R M ℳ d 0 h1 z.val).mp z.property
    exact ⟨x, Subtype.ext hx⟩

def moduleCechDegreeSectionsEquiv (d : ℤ)
    (h0 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 0) (h1 : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 1) :
    ℳ d ≃ₗ[R] HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := σ) R M ℳ d :=
  (HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm.trans
    (LinearEquiv.ofBijective (moduleCechAugmentationSectionsMap (σ := σ) R M ℳ d)
      (moduleCechAugmentationSectionsMap_bijective (σ := σ) R M ℳ d h0 h1))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DegreeSectionsEquivalence
