import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.StrongLaplacian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianClosedForcing

/-! # Dolbeault Solve -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultSolve

noncomputable section

/-! Original smooth closed antiholomorphic one-forms have actual original smooth Dolbeault primitives under the proved native coercivity hypothesis. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothDolbeault_solve (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (ha : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0, HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = a :=
  ⟨HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose.val),
    h.smoothAntiLaplacianOne_primitive_of_solution V a
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose ha
      (HolomorphicGreen.StrongLaplacian.holomorphicMetricSmoothGreen_exists_strong_solution V h hc a).choose_spec.1⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultSolve
