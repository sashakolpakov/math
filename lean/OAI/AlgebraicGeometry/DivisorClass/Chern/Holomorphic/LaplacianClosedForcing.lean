import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ProjectedCodifferentialClosed
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianHilbertPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.InnerLinearSeparation

/-! # Laplacian Closed Forcing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! For closed original forcing, the actual degree-zero codifferential of a smooth Laplacian solution is an original Dolbeault primitive. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_decomposition
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.smoothAntiLaplacianOne V b =
      HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val)) +
        Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ (h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val) := rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_closed_primitive
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hb : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (h.smoothAntiLaplacianOne V b) = 0) :
    HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val)) =
      h.smoothAntiLaplacianOne V b := by
  have hq := h.projected_codifferential_closed_zero V (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val
    (InnerLinearSeparation.linear_right_summand_zero (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1) (h.smoothAntiLaplacianOne V b)
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val)))
      (Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ (h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val))
      (h.smoothAntiLaplacianOne_decomposition V b)
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault_squared u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val))) hb)
  exact ((h.smoothAntiLaplacianOne_decomposition V b).trans
    ((congrArg (fun q : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 =>
      HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val)) + q) hq).trans
      (add_zero _))).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_primitive_of_solution
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (ha : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0)
    (hb : h.smoothAntiLaplacianOne V b = a) :
    HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 b.val)) = a :=
  (h.smoothAntiLaplacianOne_closed_primitive V b ((congrArg (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1) hb).trans ha)).trans hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
