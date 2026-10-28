import OAI.Analysis.DifferentialForms.Manifold.ComplexAction

/-! # Chart Inverse Tangent -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ChartInverseTangent

noncomputable section

/-! # The actual complex tangent transition at an inverse-chart point -/

open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The real tangent transition is the scalar restriction of the complex derivative. -/
theorem chartTransition_tangent_eq_complex_at_inverse
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f (e.symm y)).comp (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e y) =
      (fderiv ℂ (f ∘ e.symm) y).restrictScalars ℝ := by
  have hd := Analysis.DifferentialForms.Manifold.ComplexAction.chartTransition_tangent_eq_complex e f he hf (e.symm y)
    (e.map_target hy) hfy
  rw [e.right_inv hy] at hd
  exact hd

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ChartInverseTangent
