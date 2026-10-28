import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.ClosedOne
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.ClosedDolbeault
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultSquare

/-! # Closed Square -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! The native closed Dolbeault operators form the original complex for every actual metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : Data.HolomorphicLineMetricData u)

def Data.HolomorphicLineMetricData.closedDolbeaultOriginalGraph :
    (h.closedDolbeault V).domain →ₗ[ℂ] Holomorphic.DolbeaultGraph.HolomorphicDolbeaultGraph V u :=
  (((Equivalence.holomorphicMetricOriginalL2Equiv V h 0).toLinearMap.comp (h.closedDolbeault V).domain.subtype).prod
    ((Equivalence.holomorphicMetricOriginalL2Equiv V h 1).toLinearMap.comp (h.closedDolbeault V).toFun)).codRestrict _
      (fun x => Eq.mp (congrArg (fun S : Submodule ℂ (Holomorphic.FormCompletion.HolomorphicFormL2 V u 0 × Holomorphic.FormCompletion.HolomorphicFormL2 V u 1) =>
        (Equivalence.holomorphicMetricOriginalL2Equiv V h 0 x.val,
          Equivalence.holomorphicMetricOriginalL2Equiv V h 1 (h.closedDolbeault V x)) ∈ S)
            (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault_graph V u))
        ((h.closedDolbeault_mem_graph V x.val (h.closedDolbeault V x)).mp ((h.closedDolbeault V).mem_graph x)))

def Data.HolomorphicLineMetricData.closedDolbeaultAntiValue :
    (h.closedDolbeault V).domain →ₗ[ℂ] Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).symm.toLinearMap.comp
    ((Holomorphic.DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u).toLinearMap.comp (h.closedDolbeaultOriginalGraph V))

theorem Data.HolomorphicLineMetricData.closedDolbeaultAntiValue_val (x : (h.closedDolbeault V).domain) :
    (h.closedDolbeaultAntiValue V x).val = h.closedDolbeault V x := by
  change (Equivalence.holomorphicMetricOriginalL2Equiv V h 1).symm
    (Equivalence.holomorphicMetricOriginalL2Equiv V h 1 (h.closedDolbeault V x)) = _
  exact (Equivalence.holomorphicMetricOriginalL2Equiv V h 1).symm_apply_apply (h.closedDolbeault V x)

theorem Data.HolomorphicLineMetricData.closedDolbeaultAntiValue_graph (x : (h.closedDolbeault V).domain) :
    (h.closedDolbeaultAntiValue V x, 0) ∈ (h.closedDolbeaultOne V).graph := by
  apply (h.closedDolbeaultOne_mem_graph V _ _).mpr
  have he : (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h (h.closedDolbeaultAntiValue V x),
      Equivalence.holomorphicMetricOriginalL2Equiv V h 2 0) =
        (Holomorphic.DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u (h.closedDolbeaultOriginalGraph V x), 0) :=
    Prod.ext ((Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).apply_symm_apply
      (Holomorphic.DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u (h.closedDolbeaultOriginalGraph V x)))
        (Equivalence.holomorphicMetricOriginalL2Equiv V h 2).map_zero
  exact Eq.mpr (congrArg (fun z : Holomorphic.AntiOneHilbert.HolomorphicAntiOneL2 V u × Holomorphic.FormCompletion.HolomorphicFormL2 V u 2 =>
    z ∈ (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).graph) he)
      (Holomorphic.ClosedDolbeaultSquare.holomorphicDolbeaultGraphAntiValue_closedOne_graph V u (h.closedDolbeaultOriginalGraph V x))

def Data.HolomorphicLineMetricData.closedDolbeaultAntiValueDomain :
    (h.closedDolbeault V).domain →ₗ[ℂ] (h.closedDolbeaultOne V).domain :=
  (h.closedDolbeaultAntiValue V).codRestrict _ (fun x =>
    LinearPMap.mem_domain_of_mem_graph (h.closedDolbeaultAntiValue_graph V x))

theorem Data.HolomorphicLineMetricData.closedDolbeault_square (x : (h.closedDolbeault V).domain) :
    h.closedDolbeaultOne V (h.closedDolbeaultAntiValueDomain V x) = 0 :=
  (h.closedDolbeaultOne V).mem_graph_snd_inj
    ((h.closedDolbeaultOne V).mem_graph (h.closedDolbeaultAntiValueDomain V x))
    (h.closedDolbeaultAntiValue_graph V x) rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
