import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration
import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafCategory

/-! # Integration Sheaf Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegrationSheafMap

noncomputable section

/-! Actual integration of smooth forms defines a map to the genuine
smooth singular sheaf complex, preserving its original augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def integrationSheafMap : Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M ⟶
    AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ) where
  f n := ObjectProperty.homMk
    ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n ≫
      toSheafify (Opens.grothendieckTopology M)
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n))
  comm' i j hij := by
    obtain rfl := (show i + 1 = j from hij)
    apply Sheaf.hom_ext
    change (((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f i ≫ toSheafify _ _) ≫
      sheafifyMap (Opens.grothendieckTopology M)
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).d i (i + 1))) = _
    rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc,
      (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).comm]
    erw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d_sheaf, Category.assoc]
    rfl

theorem integrationSheafMap_zero : (integrationSheafMap E M).f 0 = AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap E M := by
  apply Sheaf.hom_ext
  change (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f 0 ≫ _ = _
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap_zero]
  rfl

theorem integrationSheafMap_augmentation :
    Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantDeRhamAugmentation E M ≫ integrationSheafMap E M =
      AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantDeRhamAugmentation E M).f 0 ≫ (integrationSheafMap E M).f 0 = _
    rw [integrationSheafMap_zero, AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap_f_zero]
    unfold Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldLocallyConstantDeRhamAugmentation
    erw [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation.smoothSimplexZeroSheafMap_augmentation E M
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)) (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegrationSheafMap
