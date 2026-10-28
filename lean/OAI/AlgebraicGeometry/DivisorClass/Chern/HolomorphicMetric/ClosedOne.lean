import OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedOperatorCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOne

/-! # Closed One -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! The actual closed first Dolbeault differential with every constructed Hermitian metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : Data.HolomorphicLineMetricData u)

def Data.HolomorphicLineMetricData.closedDolbeaultOne :
    Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h →ₗ.[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2 :=
  ClosedOperatorCoordinates.linearPMapInCoordinates (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h)
    (Equivalence.holomorphicMetricOriginalL2Equiv V h 2) (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u)

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_isClosed : (h.closedDolbeaultOne V).IsClosed :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_isClosed _ _ _ (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne_isClosed V u)

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_mem_graph
    (x : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) (y : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2) :
    (x, y) ∈ (h.closedDolbeaultOne V).graph ↔
      (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h x, Equivalence.holomorphicMetricOriginalL2Equiv V h 2 y) ∈
        (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).graph :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_mem_graph _ _ _ x y

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_domain_dense :
    Dense ((h.closedDolbeaultOne V).domain : Set (Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h)) :=
  ClosedOperatorCoordinates.linearPMapInCoordinates_domain_dense _ _ _ (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne_domain_dense V u)

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_smooth_graph (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a,
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val) ∈
        (h.closedDolbeaultOne V).graph := by
  apply (h.closedDolbeaultOne_mem_graph V _ _).mpr
  exact Eq.mpr (congrArg (fun z : Holomorphic.AntiOneHilbert.HolomorphicAntiOneL2 V u × Holomorphic.FormCompletion.HolomorphicFormL2 V u 2 =>
    z ∈ (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).graph)
      (Prod.ext (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv_inclusion V h a)
        (Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)))
    (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne_smooth_graph V u a)

def Data.HolomorphicLineMetricData.closedDolbeaultOneSmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] (h.closedDolbeaultOne V).domain :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h).codRestrict _
    (fun a => LinearPMap.mem_domain_of_mem_graph (h.closedDolbeaultOne_smooth_graph V a))

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_smooth_apply (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.closedDolbeaultOne V (h.closedDolbeaultOneSmoothInclusion V a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val :=
  (h.closedDolbeaultOne V).mem_graph_snd_inj
    ((h.closedDolbeaultOne V).mem_graph (h.closedDolbeaultOneSmoothInclusion V a))
    (h.closedDolbeaultOne_smooth_graph V a) rfl

def Data.HolomorphicLineMetricData.dolbeaultOneGraphMap : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ]
    Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h × Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2 :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h).prod
    ((Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2).comp
      ((HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 2).subtype.comp (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1)))

theorem Data.HolomorphicLineMetricData.closedDolbeaultOne_graph_closure :
    (h.closedDolbeaultOne V).graph = (LinearMap.range (h.dolbeaultOneGraphMap V)).topologicalClosure := by
  have he : ∀ a, ((Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).prodCongr
      (Equivalence.holomorphicMetricOriginalL2Equiv V h 2)) (h.dolbeaultOneGraphMap V a) = Holomorphic.ClosedDolbeaultOne.holomorphicDolbeaultOneGraphMap V u a := by
    intro a
    exact Prod.ext (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv_inclusion V h a)
      (Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)
  exact (ClosedOperatorCoordinates.linearPMapInCoordinates_graph (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h)
    (Equivalence.holomorphicMetricOriginalL2Equiv V h 2) (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u)).trans
      (ClosedOperatorCoordinates.linearPMapCoordinateGraph_closure_range _ _ _ (h.dolbeaultOneGraphMap V)
        (Holomorphic.ClosedDolbeaultOne.holomorphicDolbeaultOneGraphMap V u) he (Holomorphic.ClosedDolbeaultOne.holomorphicClosedDolbeaultOne_graph V u))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
