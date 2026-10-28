import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Multiplication
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeAdjointIntegral

/-! # Variable Metric Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! An actual smooth Dolbeault codifferential and integration by parts for every constructed metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (q : ℕ)

def HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1) →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q :=
  ((HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).ratioFormMul V h q).comp
    ((Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q).comp
      (h.ratioFormMul V (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) (q + 1)))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_apply
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    h.degreeCodifferential V q b =
      (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).ratioFormMul V h q
        (Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q
          (h.ratioFormMul V (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) (q + 1) b)) := rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    h.formIntegralPair V (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val =
      h.formIntegralPair V q (h.degreeCodifferential V q b) a.val := by
  let k := HolomorphicMetric.Data.holomorphicLineCanonicalMetric u
  let rb := h.ratioFormMul V k (q + 1) b
  calc
    _ = k.formIntegralPair V (q + 1) rb (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val :=
      h.formIntegralPair_change_left V k (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val
    _ = Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u (q + 1) rb (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val :=
      Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_formIntegralPair V (q + 1) rb (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val
    _ = Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u q (Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q rb) a.val :=
      Holomorphic.DegreeAdjointIntegral.holomorphicLineDegreeCodifferential_pair V u q a rb
    _ = k.formIntegralPair V q (Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q rb) a.val :=
      (Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_formIntegralPair V q (Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q rb) a.val).symm
    _ = h.formIntegralPair V q (h.degreeCodifferential V q b) a.val := by
      rw [h.formIntegralPair_change_left V k q, h.degreeCodifferential_apply]
      rw [h.ratioFormMul_cancel]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_pair_right
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    h.formIntegralPair V (q + 1) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val b =
      h.formIntegralPair V q a.val (h.degreeCodifferential V q b) := by
  have hp := congrArg (starRingEnd ℂ) (h.degreeCodifferential_pair V q a b)
  rw [h.formIntegralPair_conj, h.formIntegralPair_conj] at hp
  exact hp

theorem Holomorphic.VariableMetricAdjoint.holomorphicLineCanonicalMetric_degreeCodifferential
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).degreeCodifferential V q b =
      Holomorphic.DegreeCodifferential.holomorphicLineDegreeCodifferential V u q b := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_apply,
    HolomorphicMetric.Data.HolomorphicLineMetricData.ratioFormMul_self, HolomorphicMetric.Data.HolomorphicLineMetricData.ratioFormMul_self]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
