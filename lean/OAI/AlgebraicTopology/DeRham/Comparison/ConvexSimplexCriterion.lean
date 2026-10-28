import OAI.AlgebraicTopology.DeRham.Comparison.ConvexManifoldResolution
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSmoothAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.SingleZeroNormalization

/-! # Convex Simplex Criterion -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexCriterion

noncomputable section

/-!
# A normalization criterion for the concrete local simplex comparison

Both complexes and both locally constant augmentations are the actual ones.
Their quasi-isomorphism on convex opens has already been proved. The only
remaining condition on a cochain map is its exact degree-zero integration
formula, which will be discharged for the Duffy integration morphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For the actual local de Rham and smooth-singular complexes, the genuine
degree-zero integral identifies any comparison map as a quasi-isomorphism
on a convex open set. -/
theorem convexSimplexComparison_quasiIso_of_zero (U : Opens E)
    (hU : Convex ℝ (U : Set E))
    (f : Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U ⟶ Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U)
    (hzero : (f.f 0).hom = SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E U) : QuasiIso f := by
  let := ConvexManifoldResolution.locallyConstantOpenManifoldDeRhamResolutionMap_quasiIso_convex U hU
  let := ManifoldSmoothAugmentation.locallyConstantManifoldSmoothResolutionMap_quasiIso_convexOpen E
    (ModuleCat.of ℂ ℂ) U hU
  apply SingleZeroNormalization.quasiIso_of_singleZero_normalization
    (ConvexManifoldResolution.locallyConstantOpenManifoldDeRhamResolutionMap U)
    (ManifoldSmoothAugmentation.locallyConstantManifoldSmoothResolutionMap E (ModuleCat.of ℂ ℂ) U) f
  rw [ConvexManifoldResolution.locallyConstantOpenManifoldDeRhamResolutionMap_f_zero,
    ManifoldSmoothAugmentation.locallyConstantManifoldSmoothResolutionMap_f_zero_eq_presheaf E E U]
  apply ModuleCat.hom_ext
  change (f.f 0).hom.comp (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) =
    ((Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E E).app (op U)).hom
  rw [hzero]
  exact SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration_augmentation U

end

end OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexCriterion
