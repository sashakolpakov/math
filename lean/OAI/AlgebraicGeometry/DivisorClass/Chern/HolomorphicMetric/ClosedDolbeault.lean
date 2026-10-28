import OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedOperatorCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOperator

/-! # Closed Dolbeault -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! The original closed Dolbeault operator realized in the native Hilbert spaces of any actual metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : Data.HolomorphicLineMetricData u)

def Data.HolomorphicLineMetricData.closedDolbeault :
    Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 →ₗ.[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 :=
  ClosedOperatorCoordinates.linearPMapInCoordinates (Equivalence.holomorphicMetricOriginalL2Equiv V h 0)
    (Equivalence.holomorphicMetricOriginalL2Equiv V h 1) (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault V u)

theorem Data.HolomorphicLineMetricData.closedDolbeault_isClosed : (h.closedDolbeault V).IsClosed :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_isClosed _ _ _ (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault_isClosed V u)

theorem Data.HolomorphicLineMetricData.closedDolbeault_mem_graph
    (x : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0) (y : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1) :
    (x, y) ∈ (h.closedDolbeault V).graph ↔
      (Equivalence.holomorphicMetricOriginalL2Equiv V h 0 x, Equivalence.holomorphicMetricOriginalL2Equiv V h 1 y) ∈
        (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault V u).graph :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_mem_graph _ _ _ x y

theorem Data.HolomorphicLineMetricData.closedDolbeault_domain_dense :
    Dense ((h.closedDolbeault V).domain : Set (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0)) :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_domain_dense _ _ _ (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault_domain_dense V u)

theorem Data.HolomorphicLineMetricData.closedDolbeault_smooth_graph (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 a,
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)) ∈
        (h.closedDolbeault V).graph := by
  apply (h.closedDolbeault_mem_graph V _ _).mpr
  exact Eq.mpr (congrArg (fun z : Holomorphic.FormCompletion.HolomorphicFormL2 V u 0 × Holomorphic.FormCompletion.HolomorphicFormL2 V u 1 =>
    z ∈ (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault V u).graph)
      (Prod.ext (Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 0 a)
        (Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a))))
    (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault_smooth_graph V u a)

theorem Data.HolomorphicLineMetricData.closedDolbeault_smooth_mem (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 a ∈ (h.closedDolbeault V).domain :=
  LinearPMap.mem_domain_of_mem_graph (h.closedDolbeault_smooth_graph V a)

def Data.HolomorphicLineMetricData.closedDolbeaultSmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ] (h.closedDolbeault V).domain :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0).codRestrict _ (h.closedDolbeault_smooth_mem V)

theorem Data.HolomorphicLineMetricData.closedDolbeault_smooth_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    h.closedDolbeault V (h.closedDolbeaultSmoothInclusion V a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) :=
  (h.closedDolbeault V).mem_graph_snd_inj
    ((h.closedDolbeault V).mem_graph (h.closedDolbeaultSmoothInclusion V a))
    (h.closedDolbeault_smooth_graph V a) rfl

def Data.HolomorphicLineMetricData.dolbeaultGraphMap : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ]
    Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 × Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0).prod
    ((Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1).comp (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤))

theorem Data.HolomorphicLineMetricData.closedDolbeault_graph_closure :
    (h.closedDolbeault V).graph = (LinearMap.range (h.dolbeaultGraphMap V)).topologicalClosure := by
  have he : ∀ a, ((Equivalence.holomorphicMetricOriginalL2Equiv V h 0).prodCongr
      (Equivalence.holomorphicMetricOriginalL2Equiv V h 1)) (h.dolbeaultGraphMap V a) = Holomorphic.DolbeaultGraph.holomorphicDolbeaultGraphMap V u a := by
    intro a
    apply Prod.ext
    · exact Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 0 a
    · exact Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)
  exact (ClosedOperatorCoordinates.linearPMapInCoordinates_graph (Equivalence.holomorphicMetricOriginalL2Equiv V h 0)
    (Equivalence.holomorphicMetricOriginalL2Equiv V h 1) (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault V u)).trans
      (ClosedOperatorCoordinates.linearPMapCoordinateGraph_closure_range _ _ _ (h.dolbeaultGraphMap V)
        (Holomorphic.DolbeaultGraph.holomorphicDolbeaultGraphMap V u) he (Holomorphic.ClosedDolbeaultOperator.holomorphicClosedDolbeault_graph V u))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
