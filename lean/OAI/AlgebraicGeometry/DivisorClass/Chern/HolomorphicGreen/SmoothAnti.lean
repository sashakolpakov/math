import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothRepresentative
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.AntiRepresentative

/-! # Smooth Anti -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothAnti

noncomputable section

/-! The original Green solution of original smooth forcing is an actual global smooth antiholomorphic bundle form. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_exists_smooth_anti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
      Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b = HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) :=
  HolomorphicSmooth.AntiRepresentative.holomorphicMetric_smooth_representative_anti V h
    (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))
    (SmoothRepresentative.holomorphicMetricSmoothGreen_exists_smooth_representative V h hc a).choose
    (SmoothRepresentative.holomorphicMetricSmoothGreen_exists_smooth_representative V h hc a).choose_spec

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothAnti
