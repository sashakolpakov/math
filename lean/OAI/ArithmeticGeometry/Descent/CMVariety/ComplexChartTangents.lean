import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Complex Chart Tangents -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ComplexChartTangents.Abelian

noncomputable section

/-!
The actual inverse-chart tangent map is complex linear when the native
chart is complex smooth. The real tangent coordinates already used by
the exponential and lattice constructions are its scalar restriction.
-/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
open scoped _root_.Manifold ContDiff

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]

/-- The already constructed real inverse-chart derivative comes from an
actual complex-linear isomorphism of native tangent spaces. -/
theorem exists_complex_chart_tangent_equiv
    (c : OpenPartialHomeomorph G V) (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (hc : ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, V)) 1 c c.source)
    (hi : ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, E)) 1 c.symm c.target) :
    ∃ T : V ≃L[ℂ] E,
      (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := E) c) = T.toContinuousLinearMap.restrictScalars ℝ := by
  have hmd : c.MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, V)) :=
    ⟨hc.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  let T : V ≃L[ℂ] E := hmd.symm.mfderiv hz
  refine ⟨T, ?_⟩
  exact AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_eq_complex_restrictScalars (hi.contMDiffAt (c.open_target.mem_nhds hz))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ComplexChartTangents.Abelian
