import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Log Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogNorm

noncomputable section

/-! Exact local holomorphic logarithms for the metric transition potentials. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem realLog_normSq_exp (z : ℂ) : Real.log (Complex.normSq (Complex.exp z)) = 2 * z.re := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, Real.log_pow, Real.log_exp]
  norm_num

theorem complexLog_normSq_exp (z : ℂ) :
    (Real.log (Complex.normSq (Complex.exp z)) : ℂ) = z + conj z := by
  rw [realLog_normSq_exp, Complex.add_conj]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicLocalLogarithm_logNormSq (g : Exponential.HolomorphicFunction (E := E) (M := M))
    (p : M) (hp : g p ≠ 0) (q : Exponential.holomorphicLogarithmOpen g p) :
    (Real.log (Complex.normSq (g q)) : ℂ) =
      Exponential.holomorphicLocalLogarithm g p q + conj (Exponential.holomorphicLocalLogarithm g p q) := by
  rw [← Exponential.exp_holomorphicLocalLogarithm g p hp q]
  exact complexLog_normSq_exp _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogNorm
