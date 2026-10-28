import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs

/-! # Restricted Pair Zero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! An actual zero restriction gives zero original pointwise metric pairing on the restricting open. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_zero_of_restrict (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (U : Opens V.analyticSpace)
    (ha : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) a = 0)
    (x : V.analyticSpace) (hx : x ∈ U) : h.globalFormPair V n a a x = 0 := by
  have hi := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  have hv : a.val x ⟨x, trivial, hi⟩ = 0 :=
    congrArg (fun b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n => b.val x ⟨x, hx, hi⟩) ha
  rw [h.globalFormPair_inFrame V n a a x x hi, hv, Holomorphic.AdjointPointPairs.projectiveTangentCovectorPair_zero_left, mul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
