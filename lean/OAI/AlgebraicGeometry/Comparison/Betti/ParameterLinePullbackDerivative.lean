import OAI.AlgebraicGeometry.Comparison.Betti.VectorDbarHolomorphicPullback
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Parameter Line Pullback Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParameterLinePullbackDerivative.Dolbeault

noncomputable section

/-! Actual parameter derivatives under a change of the line variable
and multiplication by a scalar depending only on that line variable. -/

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem parameter_fderiv_line_weight {g : P × ℂ → F} {a φ : ℂ → ℂ} {q : P × ℂ}
    (hf : DifferentiableAt ℝ (fun y : P × ℂ => a y.2 • g (y.1, φ y.2)) q)
    (hg : DifferentiableAt ℝ g (q.1, φ q.2)) (v : P) :
    fderiv ℝ (fun y : P × ℂ => a y.2 • g (y.1, φ y.2)) q (v, 0) =
      a q.2 • fderiv ℝ g (q.1, φ q.2) (v, 0) := by
  have hfull := (hf.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)).fderiv
  have hs := ((hg.hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 (φ q.2))).const_smul (a q.2)).fderiv
  exact congrArg (fun D : P →L[ℝ] F => D v) (hfull.symm.trans hs)

variable [NormedSpace ℂ P]

theorem parameter_direction_line_weight {g : P × ℂ → F} {a φ : ℂ → ℂ} {q : P × ℂ}
    (hf : DifferentiableAt ℝ (fun y : P × ℂ => a y.2 • g (y.1, φ y.2)) q)
    (hg : DifferentiableAt ℝ g (q.1, φ q.2)) (v : P)
    (hv : fderiv ℝ g (q.1, φ q.2) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ g (q.1, φ q.2) (v, 0)) :
    fderiv ℝ (fun y : P × ℂ => a y.2 • g (y.1, φ y.2)) q (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (fun y : P × ℂ => a y.2 • g (y.1, φ y.2)) q (v, 0) := by
  rw [parameter_fderiv_line_weight hf hg, parameter_fderiv_line_weight hf hg, hv, smul_comm]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParameterLinePullbackDerivative.Dolbeault
