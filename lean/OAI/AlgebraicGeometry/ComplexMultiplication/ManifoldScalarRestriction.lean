import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts

/-! # Manifold Scalar Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldScalarRestriction

noncomputable section

/-! # Restricting scalars in actual complex manifold maps -/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]

/-- The same actual chart maps are differentiable over the smaller scalar field. -/
theorem contMDiff_complex_to_real {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  obtain ⟨hc, hd⟩ := contMDiff_iff.mp hf
  apply contMDiff_iff.mpr
  refine ⟨hc, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using (hd x y).restrict_scalars ℝ

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldScalarRestriction
