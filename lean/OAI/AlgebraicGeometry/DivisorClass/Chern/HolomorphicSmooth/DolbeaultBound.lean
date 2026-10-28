import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultSolve
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianPrimitiveBound

/-! # Dolbeault Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultBound

noncomputable section

/-! Constructed original smooth Dolbeault primitives with the actual metric L² estimate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetricSmoothDolbeault_solve_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (ha : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0, HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = a ∧
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 b.val‖ ≤ ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖ :=
  ⟨HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose.val),
    h.smoothAntiLaplacianOne_primitive_of_solution V a
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose ha
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose_spec.1,
    h.smoothAntiLaplacianOne_codifferential_bound V hc a
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose_spec.1⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultBound
