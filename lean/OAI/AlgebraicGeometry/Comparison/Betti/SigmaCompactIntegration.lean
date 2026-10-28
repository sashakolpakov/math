import OAI.AlgebraicTopology.DeRham.Comparison.Manifold

/-! # Sigma Compact Integration -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactIntegration.Smooth

noncomputable section

/-!
# Genuine integration on sigma-compact manifolds

The existing chart-descent proof applies to the full cover by chart sources.
Compactness is unnecessary: the proved partition-of-unity augmentation
already covers sigma-compact Hausdorff manifolds. This includes the open
manifolds needed for the sheaf comparison.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.Manifold

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- The actual top-open integration map is a quasi-isomorphism by chart descent. -/
theorem manifoldOpenIntegration_quasiIso_top :
    QuasiIso (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration E (⊤ : Opens M)) := by
  let U : M → Opens M := AlgebraicTopology.DeRham.Comparison.Manifold.manifoldChartOpen E M
  have hcover : ∀ y : M, ∃ x, y ∈ U x := fun y => ⟨y, mem_chart_source E y⟩
  apply (AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation.manifoldOpenIntegrationPresheafMap_quasiIso_iff E M (⊤ : Opens M)).mp
  apply AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_quasiIso_descent U ⊤ (fun _ => le_top)
    (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M)
  · exact AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge.manifoldPresheafCechAugmentation_quasiIso E M U hcover
  · exact AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison.manifoldSmoothCechTopAugmentation_quasiIso E M U hcover
  · apply AlgebraicTopology.DeRham.Comparison.CechTotal.cechTotalMap_quasiIso_of_intersections
    intro p a
    apply (AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation.manifoldOpenIntegrationPresheafMap_quasiIso_iff E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).mpr
    exact AlgebraicTopology.DeRham.Comparison.Manifold.manifoldOpenIntegration_quasiIso_chartOpen E M (a 0) _ (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)

/-- Actual Duffy integration compares smooth forms and smooth singular cochains. -/
theorem smoothSimplexIntegration_quasiIso :
    QuasiIso (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) := by
  apply (AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph.quasiIso_smoothSimplexIntegration_diffeomorph_iff (AlgebraicTopology.DeRham.Comparison.Manifold.manifoldTopDiffeomorph E M)).mpr
  exact (AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph.quasiIso_manifoldOpenIntegration_iff E (⊤ : Opens M)).mp
    (manifoldOpenIntegration_quasiIso_top E M)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactIntegration.Smooth
