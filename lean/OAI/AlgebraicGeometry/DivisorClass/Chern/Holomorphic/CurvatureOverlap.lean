import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LocalCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogNormCurvatureVanishing

/-! # Curvature Overlap -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureOverlap

noncomputable section

/-! The actual local metric curvature forms agree on every original frame overlap. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

theorem holomorphicLineLocalCurvatureForm_eq_scalar (i : M) :
    HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i = ScalarOpenConnection.smoothScalarOpenCurvature (HolomorphicLine.LocalCurvature.holomorphicLineLogMetricFunction u i) := rfl

theorem holomorphicLineLocalCurvatureForm_overlap (i j : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u j) := by
  rw [holomorphicLineLocalCurvatureForm_eq_scalar, holomorphicLineLocalCurvatureForm_eq_scalar,
    ScalarOpenConnection.smoothScalarOpenCurvature_restrict, ScalarOpenConnection.smoothScalarOpenCurvature_restrict]
  apply LogNormCurvatureVanishing.smoothScalarOpenCurvature_eq_of_logNormSq_difference (CohomologyTransitions.holomorphicCohomologyTransition E M u i j)
  intro x
  change (HolomorphicLine.LogMetric.holomorphicLineLogMetric u i ⟨x.val, x.property.1⟩ : ℂ) -
    (HolomorphicLine.LogMetric.holomorphicLineLogMetric u j ⟨x.val, x.property.2⟩ : ℂ) = _
  rw [HolomorphicLine.LogMetric.holomorphicLineLogMetric_transition u i j x.val x.property.1 x.property.2,
    Complex.ofReal_add, add_sub_cancel_right]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureOverlap
