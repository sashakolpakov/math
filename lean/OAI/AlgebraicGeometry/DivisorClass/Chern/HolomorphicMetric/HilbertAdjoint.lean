import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.ClosedDolbeault
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricAdjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Hilbert Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! The native Hilbert adjoint for any actual metric agrees with its constructed smooth codifferential. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : Data.HolomorphicLineMetricData u)

theorem Data.HolomorphicLineMetricData.dolbeaultGraphMap_pair (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ (h.dolbeaultGraphMap V a).2 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) =
      inner ℂ (h.dolbeaultGraphMap V a).1
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b)) := by
  change inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)) _ =
    inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 a) _
  rw [Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner, Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner]
  exact h.degreeCodifferential_pair_right V 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ a) b

theorem Data.HolomorphicLineMetricData.closedDolbeault_graph_pair
    (z : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 × Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1)
    (hz : z ∈ (h.closedDolbeault V).graph) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ z.2 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) =
      inner ℂ z.1 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b)) := by
  rw [h.closedDolbeault_graph_closure] at hz
  let S : Set (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 × Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1) :=
    {w | inner ℂ w.2 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) =
      inner ℂ w.1 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b))}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const)
  have hs : Set.range (h.dolbeaultGraphMap V) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact h.dolbeaultGraphMap_pair V a b
  exact closure_minimal hs hS hz

theorem Data.HolomorphicLineMetricData.closedDolbeault_domain_pair
    (x : (h.closedDolbeault V).domain) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ (h.closedDolbeault V x) (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) =
      inner ℂ x.val (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b)) :=
  h.closedDolbeault_graph_pair V (x.val, h.closedDolbeault V x) ((h.closedDolbeault V).mem_graph x) b

theorem Data.HolomorphicLineMetricData.closedDolbeault_domain_pair_left
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (x : (h.closedDolbeault V).domain) :
    inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b)) x.val =
      inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) (h.closedDolbeault V x) := by
  have hp := congrArg (starRingEnd ℂ) (h.closedDolbeault_domain_pair V x b)
  exact (inner_conj_symm (𝕜 := ℂ)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b)) x.val).symm.trans
      (hp.symm.trans (inner_conj_symm (𝕜 := ℂ)
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) (h.closedDolbeault V x)))

def Data.HolomorphicLineMetricData.dolbeaultHilbertAdjoint :
    Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 →ₗ.[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 := (h.closedDolbeault V).adjoint

theorem Data.HolomorphicLineMetricData.dolbeaultHilbertAdjoint_isClosed :
    (h.dolbeaultHilbertAdjoint V).IsClosed :=
  LinearPMap.adjoint_isClosed (h.closedDolbeault_domain_dense V)

theorem Data.HolomorphicLineMetricData.dolbeaultHilbertAdjoint_smooth_mem
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b ∈ (h.dolbeaultHilbertAdjoint V).domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b),
      h.closedDolbeault_domain_pair_left V b⟩

def Data.HolomorphicLineMetricData.dolbeaultHilbertAdjointSmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 →ₗ[ℂ] (h.dolbeaultHilbertAdjoint V).domain :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1).codRestrict _ (h.dolbeaultHilbertAdjoint_smooth_mem V)

theorem Data.HolomorphicLineMetricData.dolbeaultHilbertAdjoint_smooth_apply
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    h.dolbeaultHilbertAdjoint V (h.dolbeaultHilbertAdjointSmoothInclusion V b) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b) :=
  LinearPMap.adjoint_apply_eq (h.closedDolbeault_domain_dense V) _
    (h.closedDolbeault_domain_pair_left V b)

theorem Data.HolomorphicLineMetricData.dolbeaultHilbertAdjoint_domain_dense :
    Dense ((h.dolbeaultHilbertAdjoint V).domain : Set (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1)) := by
  apply (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h 1).mono
  rintro _ ⟨b, rfl⟩
  exact h.dolbeaultHilbertAdjoint_smooth_mem V b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
