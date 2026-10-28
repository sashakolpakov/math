import OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexCriterion
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration

/-! # Convex Simplex Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexIntegration

noncomputable section

/-!
# The actual simplex integration comparison on convex open domains

The map is the already constructed signed Duffy integral over actual smooth
singular simplices. Its degree-zero normalization makes the genuine locally
constant augmentation square commute. The independently proved de Rham and
smooth singular resolutions therefore make this specific map a
quasi-isomorphism on each convex open, including the empty open.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual simplex integration commutes with the two genuine locally constant augmentations. -/
theorem manifoldOpenIntegration_augmentation (U : Opens E) :
    ConvexManifoldResolution.locallyConstantOpenManifoldDeRhamResolutionMap U ≫ ManifoldOpenIntegration.manifoldOpenIntegration E U =
      ManifoldSmoothAugmentation.locallyConstantManifoldSmoothResolutionMap E (ModuleCat.of ℂ ℂ) U := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, ConvexManifoldResolution.locallyConstantOpenManifoldDeRhamResolutionMap_f_zero,
    ManifoldOpenIntegration.manifoldOpenIntegration_zero,
    ManifoldSmoothAugmentation.locallyConstantManifoldSmoothResolutionMap_f_zero_eq_presheaf E E U]
  apply ModuleCat.hom_ext
  exact SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration_augmentation U

variable [FiniteDimensional ℝ E]

/-- The actual Duffy integration map is a quasi-isomorphism on every convex open domain. -/
theorem manifoldOpenIntegration_quasiIso_convex (U : Opens E)
    (hU : Convex ℝ (U : Set E)) : QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E U) := by
  apply ConvexSimplexCriterion.convexSimplexComparison_quasiIso_of_zero E U hU (ManifoldOpenIntegration.manifoldOpenIntegration E U)
  rw [ManifoldOpenIntegration.manifoldOpenIntegration_zero]
  rfl

/-- The resulting genuine de Rham-to-smooth-singular cohomology isomorphism. -/
def convexSimplexIntegrationCohomologyIso (U : Opens E)
    (hU : Convex ℝ (U : Set E)) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomology E U n ≅
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).homology n := by
  let := manifoldOpenIntegration_quasiIso_convex E U hU
  exact isoOfQuasiIsoAt (ManifoldOpenIntegration.manifoldOpenIntegration E U) n

/-- This isomorphism is induced by the actual simplex integration cochain map. -/
@[simp]
theorem convexSimplexIntegrationCohomologyIso_hom (U : Opens E)
    (hU : Convex ℝ (U : Set E)) (n : ℕ) :
    (convexSimplexIntegrationCohomologyIso E U hU n).hom =
      ManifoldOpenIntegration.manifoldOpenIntegrationCohomology E U n := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ConvexSimplexIntegration
