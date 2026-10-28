import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraph

/-! # Dolbeault Closable -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultClosable

noncomputable section

/-! Closability of the actual bundle Dolbeault operator follows from its
proved metric adjoint identity and the faithful dense smooth inclusions. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

theorem inner_zero_of_denseRange {A F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (f : A → F) (hf : DenseRange f) (x : F) (h : ∀ a, inner ℂ x (f a) = 0) : x = 0 := by
  have hx : inner ℂ x x = 0 := hf.induction_on (p := fun y => inner ℂ x y = 0) x
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) h
  exact inner_self_eq_zero.mp hx

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicDolbeaultGraphMap_pair (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ (DolbeaultGraph.holomorphicDolbeaultGraphMap V u a).2 (FormCompletion.holomorphicFormL2Inclusion V u 1 b) =
      inner ℂ (DolbeaultGraph.holomorphicDolbeaultGraphMap V u a).1
        (FormCompletion.holomorphicFormL2Inclusion V u 0 (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b)) := by
  calc
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) b :=
      FormCompletion.holomorphicFormL2Inclusion_inner V u 1 _ _
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 0 a (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b) :=
      AdjointIntegral.holomorphicLineMetricCodifferential_pair_right V u a b
    _ = _ := (FormCompletion.holomorphicFormL2Inclusion_inner V u 0 _ _).symm

theorem holomorphicDolbeaultGraph_pair (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u)
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ (DolbeaultGraph.holomorphicDolbeaultGraphValue V u z) (FormCompletion.holomorphicFormL2Inclusion V u 1 b) =
      inner ℂ (DolbeaultGraph.holomorphicDolbeaultGraphSource V u z)
        (FormCompletion.holomorphicFormL2Inclusion V u 0 (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b)) := by
  let S : Set (FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1) :=
    {w | inner ℂ w.2 (FormCompletion.holomorphicFormL2Inclusion V u 1 b) =
      inner ℂ w.1 (FormCompletion.holomorphicFormL2Inclusion V u 0 (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b))}
  have hS : IsClosed S :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hs : Set.range (DolbeaultGraph.holomorphicDolbeaultGraphMap V u) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact holomorphicDolbeaultGraphMap_pair V u a b
  exact closure_minimal hs hS z.property

theorem holomorphicDolbeaultGraphValue_zero_of_source (z : DolbeaultGraph.HolomorphicDolbeaultGraph V u)
    (hz : DolbeaultGraph.holomorphicDolbeaultGraphSource V u z = 0) : DolbeaultGraph.holomorphicDolbeaultGraphValue V u z = 0 := by
  apply inner_zero_of_denseRange (FormCompletion.holomorphicFormL2Inclusion V u 1) (FormCompletion.holomorphicFormL2Inclusion_dense V u 1)
  intro b
  rw [holomorphicDolbeaultGraph_pair, hz, inner_zero_left]

theorem holomorphicDolbeaultGraphSource_injective : Function.Injective (DolbeaultGraph.holomorphicDolbeaultGraphSource V u) := by
  intro z w h
  have hs : DolbeaultGraph.holomorphicDolbeaultGraphSource V u (z - w) = 0 :=
    ((DolbeaultGraph.holomorphicDolbeaultGraphSource V u).map_sub z w).trans (sub_eq_zero.mpr h)
  have hv : DolbeaultGraph.holomorphicDolbeaultGraphValue V u z - DolbeaultGraph.holomorphicDolbeaultGraphValue V u w = 0 :=
    ((DolbeaultGraph.holomorphicDolbeaultGraphValue V u).map_sub z w).symm.trans
      (holomorphicDolbeaultGraphValue_zero_of_source V u (z - w) hs)
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · exact sub_eq_zero.mp hv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultClosable
