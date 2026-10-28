import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Closed Submodule Curve Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubmoduleCurveTangent.Construction

noncomputable section

/-! Tangent vectors to curves lying in an affine translate of a closed
linear subspace belong to that subspace. -/

open scoped _root_.Topology
open Filter

theorem closed_submodule_curve_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Submodule ℝ E) (hP : IsClosed (P : Set E))
    (f : ℝ → E) (v : E) (a : ℝ) (hf : HasDerivAt f v a)
    (hmem : ∀ t, f t - f a ∈ P) : v ∈ P := by
  apply hP.mem_of_tendsto hf.tendsto_slope_zero
  exact Eventually.of_forall (fun t => P.smul_mem t⁻¹ (hmem (a + t)))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubmoduleCurveTangent.Construction
