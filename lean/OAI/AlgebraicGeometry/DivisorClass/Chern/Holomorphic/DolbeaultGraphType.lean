import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneHilbert
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraph

/-! # Dolbeault Graph Type -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraphType

noncomputable section

/-! The closed relation of the actual Dolbeault operator takes values in the
constructed antiholomorphic Hilbert space. This does not assume closability. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicLineDolbeaultZeroAnti :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤).codRestrict _ fun a i =>
    HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_coordinate_type u ⊤ a i

theorem holomorphicL2OnePart_dolbeault (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    AntiOneHilbert.holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)) =
      FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) :=
  AntiOneHilbert.holomorphicL2OnePart_anti_inclusion V u (holomorphicLineDolbeaultZeroAnti V u a)

def holomorphicDolbeaultGraphTypeDefect :
    FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1 →L[ℂ] FormCompletion.HolomorphicFormL2 V u 1 :=
  (AntiOneHilbert.holomorphicL2OnePart V u - ContinuousLinearMap.id ℂ (FormCompletion.HolomorphicFormL2 V u 1)).comp
    (ContinuousLinearMap.snd ℂ _ _)

theorem holomorphicDolbeaultGraphTypeDefect_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphTypeDefect V u (DolbeaultGraph.holomorphicDolbeaultGraphMap V u a) = 0 := by
  change AntiOneHilbert.holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)) -
    FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) = 0
  exact sub_eq_zero.mpr (holomorphicL2OnePart_dolbeault V u a)

theorem holomorphicDolbeaultGraphTypeDefect_closure :
    DolbeaultGraph.holomorphicDolbeaultGraphClosure V u ≤ (holomorphicDolbeaultGraphTypeDefect V u).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨a, rfl⟩
    exact holomorphicDolbeaultGraphTypeDefect_smooth V u a
  · exact (holomorphicDolbeaultGraphTypeDefect V u).isClosed_ker

theorem holomorphicDolbeaultGraphValue_mem_anti (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u) :
    DolbeaultGraph.holomorphicDolbeaultGraphValue V u z ∈ AntiOneHilbert.holomorphicAntiOneL2Submodule V u :=
  holomorphicDolbeaultGraphTypeDefect_closure V u z.property

def holomorphicDolbeaultGraphAntiValue : DolbeaultGraph.HolomorphicDolbeaultGraph V u →L[ℂ] AntiOneHilbert.HolomorphicAntiOneL2 V u :=
  (DolbeaultGraph.holomorphicDolbeaultGraphValue V u).codRestrict _ (holomorphicDolbeaultGraphValue_mem_anti V u)

theorem holomorphicDolbeaultGraphAntiValue_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphAntiValue V u (DolbeaultGraph.holomorphicDolbeaultGraphInclusion V u a) =
      AntiOneHilbert.holomorphicAntiOneL2Inclusion V u (holomorphicLineDolbeaultZeroAnti V u a) := by
  apply Subtype.ext
  exact DolbeaultGraph.holomorphicDolbeaultGraphValue_inclusion V u a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraphType
