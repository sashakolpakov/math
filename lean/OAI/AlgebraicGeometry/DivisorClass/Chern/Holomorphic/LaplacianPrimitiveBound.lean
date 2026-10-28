import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianHilbertPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity
import OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertCoerciveEnergyBound

/-! # Laplacian Primitive Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native codifferential of an original smooth Laplacian solution has L² norm at most that of its original forcing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_codifferential_bound
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hb : h.smoothAntiLaplacianOne V b = a) :
    ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b.val)‖ ≤
      ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖ :=
  HilbertCoerciveEnergyBound.hilbert_coercive_energy_component_bound (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b.val))
    (HolomorphicSmooth.EnergyCoercivity.holomorphicMetricOneEnergySmoothInclusion_coercive V h hc b)
    ((congrArg (fun c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 =>
      inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h c)) hb.symm).trans
        (h.smoothAntiLaplacianOne_hilbert_pair V b b))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
