import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.SheafForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SheafIntegration
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldDeRham
import OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedResolutionComparison

/-! # Manifold Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldIntegration

noncomputable section

/-! Original integration and locally constant coefficients in the abelian sheaf category. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def abelianManifoldDeRhamComplex := Complex.SheafForget.complexSheafForgetComplex (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M)

theorem abelianManifoldDeRhamComplex_d (n : ℕ) :
    (abelianManifoldDeRhamComplex E M).d n (n + 1) = ManifoldDeRham.abelianManifoldFormSheafD E M n := by
  change (Complex.SheafForget.complexSheafForget (TopCat.of M)).map
    ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).d n (n + 1)) = _
  rw [Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
  rfl

def abelianManifoldSmoothComplex :=
  Complex.SheafForget.complexSheafForgetComplex (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ))

def abelianManifoldIntegration : abelianManifoldDeRhamComplex E M ⟶ abelianManifoldSmoothComplex E M :=
  Complex.SheafForget.complexSheafForgetComplexMap (Manifold.SheafIntegration.manifoldSheafIntegration E M)

def abelianManifoldSmoothAugmentation :
    ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M) ⟶ (abelianManifoldSmoothComplex E M).X 0 :=
  (Complex.SheafForget.complexSheafForget (TopCat.of M)).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M)

theorem abelianManifoldIntegration_augmentation :
    ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M ≫ (abelianManifoldIntegration E M).f 0 =
      abelianManifoldSmoothAugmentation E M := by
  change (Complex.SheafForget.complexSheafForget (TopCat.of M)).map (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) ≫
    (Complex.SheafForget.complexSheafForget (TopCat.of M)).map ((Manifold.SheafIntegration.manifoldSheafIntegration E M).f 0) = _
  rw [← Functor.map_comp, Manifold.SheafIntegration.manifoldSheafIntegration_augmentation]
  rfl

theorem abelianManifoldDeRhamComplex_augmentation_d :
    ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M ≫ (abelianManifoldDeRhamComplex E M).d 0 1 = 0 := by
  rw [abelianManifoldDeRhamComplex_d]
  exact ManifoldDeRham.abelianManifoldLocallyConstantInclusion_d E M

theorem abelianManifoldDeRhamComplex_zeroSequence :
    AugmentedResolutionComparison.augmentedZeroSequence (abelianManifoldDeRhamComplex E M) (ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M)
      (abelianManifoldDeRhamComplex_augmentation_d E M) = ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M := by
  unfold AugmentedResolutionComparison.augmentedZeroSequence ManifoldDeRham.abelianManifoldDeRhamZeroSequence
  congr 1

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldIntegration
