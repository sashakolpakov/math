import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricForms
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DescentChartFormula

/-! # Parametric Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParametricPullback.CM

noncomputable section

/-! ThetaCycle: local covector parameter formulas remain smooth under the
literal derivative pullback in a fixed covering section. -/

open scoped ContDiff

theorem parametric_covector_pullback_smoothAt
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (g : P → E → E [⋀^Fin n]→L[ℝ] ℂ) (h : F → E) (p₀ : P) (x : F)
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (p₀, h x))
    (hh : ContDiffAt ℝ ∞ h x) :
    ContDiffAt ℝ ∞
      (fun q : P × F => (g q.1 (h q.2)).compContinuousLinearMap (fderiv ℝ h q.2)) (p₀, x) := by
  have hc : ContDiffAt ℝ ∞ (fun q : P × F => g q.1 (h q.2)) (p₀, x) :=
    hg.comp (p₀, x) (contDiffAt_fst.prodMk (hh.comp (p₀, x) contDiffAt_snd))
  have hd : ContDiffAt ℝ ∞ (fun q : P × F => fderiv ℝ h q.2) (p₀, x) :=
    (hh.fderiv_right (by simp)).comp (p₀, x) contDiffAt_snd
  exact Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap hc hd

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParametricPullback.CM
