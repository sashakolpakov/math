import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantAntiPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntegralPairZero

/-! # Projected Codifferential Closed -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! A closed projected native codifferential in degree one vanishes by its actual original adjoint pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projected_codifferential_closed_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2)
    (hc : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ (h.degreeCodifferential V 1 c)) = 0) :
    Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ (h.degreeCodifferential V 1 c) = 0 := by
  let q := Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ (h.degreeCodifferential V 1 c)
  have hp : h.formIntegralPair V 1 q.val q.val = h.formIntegralPair V 1 (h.degreeCodifferential V 1 c) q.val :=
    (h.onePart_integral_pair V (h.degreeCodifferential V 1 c) q.val).trans
      (congrArg (h.formIntegralPair V 1 (h.degreeCodifferential V 1 c))
        (Holomorphic.OneFormProjection.holomorphicLineOnePart_eq_of_anti u ⊤ q.val q.property))
  have hd := (h.degreeCodifferential_pair V 1 q c).symm
  have hz : (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 q).val = 0 :=
    congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2 => a.val) hc
  have hzero : h.formIntegralPair V 1 q.val q.val = 0 :=
    hp.trans (hd.trans ((congrArg (h.formIntegralPair V 2 c) hz).trans (h.formIntegralPair_zero_right V 2 c)))
  exact Subtype.ext (h.formIntegralPair_definite V 1 q.val (congrArg Complex.re hzero))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
