import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOne
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraphType

/-! # Closed Dolbeault Square -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultSquare

noncomputable section

/-! The original degree-zero and degree-one Dolbeault graph closures form an actual complex. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineDolbeaultZeroAnti_squared (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (DolbeaultGraphType.holomorphicLineDolbeaultZeroAnti V u a) = 0 := by
  have he : DolbeaultGraphType.holomorphicLineDolbeaultZeroAnti V u a =
      HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ a) := Subtype.ext rfl
  rw [he]
  exact HolomorphicLine.Dolbeault.holomorphicLineDolbeault_squared u ⊤ 0 _

def holomorphicDolbeaultGraphSuccessor :
    FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1 →L[ℂ]
      AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2 :=
  ((AntiOneHilbert.holomorphicL2ToAntiOne V u).comp (ContinuousLinearMap.snd ℂ _ _)).prod 0

theorem holomorphicDolbeaultGraphSuccessor_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphSuccessor V u (DolbeaultGraph.holomorphicDolbeaultGraphMap V u a) =
      ClosedDolbeaultOne.holomorphicDolbeaultOneGraphMap V u (DolbeaultGraphType.holomorphicLineDolbeaultZeroAnti V u a) := by
  apply Prod.ext
  · apply Subtype.ext
    exact DolbeaultGraphType.holomorphicL2OnePart_dolbeault V u a
  · change 0 = FormCompletion.holomorphicFormL2Inclusion V u 2
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (DolbeaultGraphType.holomorphicLineDolbeaultZeroAnti V u a)).val
    rw [holomorphicLineDolbeaultZeroAnti_squared]
    exact (FormCompletion.holomorphicFormL2Inclusion V u 2).map_zero.symm

theorem holomorphicDolbeaultGraphSuccessor_smooth_mem (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphSuccessor V u (DolbeaultGraph.holomorphicDolbeaultGraphMap V u a) ∈
      ClosedDolbeaultOne.holomorphicDolbeaultOneGraphClosure V u :=
  Eq.mpr (congrArg (fun w : AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2 =>
    w ∈ ClosedDolbeaultOne.holomorphicDolbeaultOneGraphClosure V u) (holomorphicDolbeaultGraphSuccessor_smooth V u a))
      ((LinearMap.range (ClosedDolbeaultOne.holomorphicDolbeaultOneGraphMap V u)).le_topologicalClosure ⟨_, rfl⟩)

theorem holomorphicDolbeaultGraphSuccessor_closure :
    DolbeaultGraph.holomorphicDolbeaultGraphClosure V u ≤
      (ClosedDolbeaultOne.holomorphicDolbeaultOneGraphClosure V u).comap (holomorphicDolbeaultGraphSuccessor V u).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨a, rfl⟩
    exact holomorphicDolbeaultGraphSuccessor_smooth_mem V u a
  · exact (ClosedDolbeaultOne.holomorphicDolbeaultOneGraphClosure_isClosed V u).preimage
      (holomorphicDolbeaultGraphSuccessor V u).continuous

theorem holomorphicDolbeaultGraphSuccessor_on_graph (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u) :
    holomorphicDolbeaultGraphSuccessor V u z.val = (DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u z, 0) := by
  apply Prod.ext
  · apply Subtype.ext
    exact (AntiOneHilbert.holomorphicAntiOneL2_mem V u _).mp (DolbeaultGraphType.holomorphicDolbeaultGraphValue_mem_anti V u z)
  · rfl

theorem holomorphicDolbeaultGraphAntiValue_closedOne_graph (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u) :
    (DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u z, 0) ∈ (ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).graph :=
  ClosedDolbeaultOne.holomorphicClosedDolbeaultOne_mem_graph V u _
    (Eq.mp (congrArg (fun w : AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2 =>
      w ∈ ClosedDolbeaultOne.holomorphicDolbeaultOneGraphClosure V u) (holomorphicDolbeaultGraphSuccessor_on_graph V u z))
        (holomorphicDolbeaultGraphSuccessor_closure V u z.property))

def holomorphicDolbeaultGraphAntiValueDomain :
    DolbeaultGraph.HolomorphicDolbeaultGraph V u →ₗ[ℂ] (ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).domain :=
  (DolbeaultGraphType.holomorphicDolbeaultGraphAntiValue V u).toLinearMap.codRestrict _ fun z =>
    LinearPMap.mem_domain_of_mem_graph (holomorphicDolbeaultGraphAntiValue_closedOne_graph V u z)

theorem holomorphicClosedDolbeault_graph_square (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u) :
    ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u (holomorphicDolbeaultGraphAntiValueDomain V u z) = 0 :=
  (ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).mem_graph_snd_inj
    ((ClosedDolbeaultOne.holomorphicClosedDolbeaultOne V u).mem_graph (holomorphicDolbeaultGraphAntiValueDomain V u z))
    (holomorphicDolbeaultGraphAntiValue_closedOne_graph V u z) rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultSquare
