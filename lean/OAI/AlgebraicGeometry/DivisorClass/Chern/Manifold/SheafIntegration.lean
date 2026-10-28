import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration

/-! # Sheaf Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SheafIntegration

noncomputable section

/-! The original integration map on actual manifold sheaves, with its original augmentation. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def manifoldSheafIntegrationDegree (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).X n ⟶
      (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).X n :=
  ObjectProperty.homMk ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n ≫
    CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n))

theorem manifoldSheafIntegrationDegree_comm (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).d n (n + 1) ≫
        manifoldSheafIntegrationDegree E M (n + 1) =
      manifoldSheafIntegrationDegree E M n ≫
        (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).d n (n + 1) := by
  apply CategoryTheory.Sheaf.hom_ext
  change ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).d n (n + 1)).hom ≫
      ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f (n + 1) ≫ _) =
    ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n ≫ _) ≫
      CategoryTheory.sheafifyMap (Opens.grothendieckTopology (TopCat.of M))
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).d n (n + 1))
  rw [← Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d_sheaf, ← Category.assoc,
    ← (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).comm n (n + 1),
    Category.assoc, Category.assoc, CategoryTheory.toSheafify_naturality]

def manifoldSheafIntegration :
    Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M ⟶
      AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ) where
  f := manifoldSheafIntegrationDegree E M
  comm' i j hij := by
    obtain rfl := (show i + 1 = j from hij)
    exact (manifoldSheafIntegrationDegree_comm E M i).symm

theorem manifoldSheafIntegration_f_hom (n : ℕ) :
    ((manifoldSheafIntegration E M).f n).hom =
      (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n) := rfl

theorem manifoldSheafIntegration_zero :
    (manifoldSheafIntegration E M).f 0 = AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap E M := by
  apply CategoryTheory.Sheaf.hom_ext
  change (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f 0 ≫ _ =
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroPresheafMap E M ≫ _
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap_zero]

theorem manifoldSheafIntegration_augmentation :
    Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M ≫ (manifoldSheafIntegration E M).f 0 =
      AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M := by
  rw [manifoldSheafIntegration_zero]
  exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap_augmentation E M

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SheafIntegration
