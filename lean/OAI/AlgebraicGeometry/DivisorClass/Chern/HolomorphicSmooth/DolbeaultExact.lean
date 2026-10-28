import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultSolve

/-! # Dolbeault Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultExact

noncomputable section

/-! Exactness of the original global smooth Dolbeault complex in degree one under native coercivity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetricSmoothDolbeault_one_exact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) :
    LinearMap.ker (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1) = LinearMap.range (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0) := by
  ext a
  constructor
  · exact DolbeaultSolve.holomorphicMetricSmoothDolbeault_solve V h hc a
  · rintro ⟨b, rfl⟩
    exact HolomorphicLine.Dolbeault.holomorphicLineDolbeault_squared u ⊤ 0 b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultExact
