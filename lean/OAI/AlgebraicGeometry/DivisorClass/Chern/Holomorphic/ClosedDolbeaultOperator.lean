import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultClosable
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Closed Dolbeault Operator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOperator

noncomputable section

/-! A native densely defined closed operator whose graph is exactly the
closure of the actual smooth bundle Dolbeault graph. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicClosedDolbeault : FormCompletion.HolomorphicFormL2 V u 0 →ₗ.[ℂ] FormCompletion.HolomorphicFormL2 V u 1 :=
  (DolbeaultGraph.holomorphicDolbeaultGraphClosure V u).toLinearPMap

theorem holomorphicClosedDolbeault_graph :
    (holomorphicClosedDolbeault V u).graph = DolbeaultGraph.holomorphicDolbeaultGraphClosure V u := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hzero
  exact DolbeaultClosable.holomorphicDolbeaultGraphValue_zero_of_source V u ⟨z, hz⟩ hzero

theorem holomorphicClosedDolbeault_isClosed : (holomorphicClosedDolbeault V u).IsClosed := by
  change IsClosed ((holomorphicClosedDolbeault V u).graph : Set (FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1))
  rw [holomorphicClosedDolbeault_graph]
  exact DolbeaultGraph.holomorphicDolbeaultGraphClosure_isClosed V u

theorem holomorphicClosedDolbeault_smooth_graph (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    (FormCompletion.holomorphicFormL2Inclusion V u 0 a,
      FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)) ∈
        (holomorphicClosedDolbeault V u).graph := by
  rw [holomorphicClosedDolbeault_graph]
  exact (LinearMap.range (DolbeaultGraph.holomorphicDolbeaultGraphMap V u)).le_topologicalClosure ⟨a, rfl⟩

theorem holomorphicClosedDolbeault_smooth_mem (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    FormCompletion.holomorphicFormL2Inclusion V u 0 a ∈ (holomorphicClosedDolbeault V u).domain :=
  LinearPMap.mem_domain_of_mem_graph (holomorphicClosedDolbeault_smooth_graph V u a)

def holomorphicClosedDolbeaultSmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ] (holomorphicClosedDolbeault V u).domain :=
  (FormCompletion.holomorphicFormL2Inclusion V u 0).codRestrict _ (holomorphicClosedDolbeault_smooth_mem V u)

theorem holomorphicClosedDolbeault_smooth_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicClosedDolbeault V u (holomorphicClosedDolbeaultSmoothInclusion V u a) =
      FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) :=
  (holomorphicClosedDolbeault V u).mem_graph_snd_inj
    ((holomorphicClosedDolbeault V u).mem_graph (holomorphicClosedDolbeaultSmoothInclusion V u a))
    (holomorphicClosedDolbeault_smooth_graph V u a) rfl

theorem holomorphicClosedDolbeault_domain_dense :
    Dense ((holomorphicClosedDolbeault V u).domain : Set (FormCompletion.HolomorphicFormL2 V u 0)) := by
  apply (FormCompletion.holomorphicFormL2Inclusion_dense V u 0).mono
  rintro _ ⟨a, rfl⟩
  exact holomorphicClosedDolbeault_smooth_mem V u a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOperator
