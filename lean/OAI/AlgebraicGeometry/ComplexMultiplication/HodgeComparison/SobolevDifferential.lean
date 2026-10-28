import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds

/-! # Sobolev Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction

noncomputable section

/-! Genuine weak derivatives as bounded operators on the completed Sobolev coordinates. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The directional derivative of the H¹ function represented by an L² Bessel coordinate. -/
def sobolevL2Derivative (m : E) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  (2 * Real.pi * Complex.I : ℂ) •
    SobolevIs.CM.Construction.l2FourierMultiplier (g := fun x : E =>
      Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m)

/-- The operator above agrees with the native distributional derivative. -/
theorem sobolevL2Derivative_distribution (m : E) (f : Lp F 2 (volume : Measure E)) :
    (sobolevL2Derivative m f : 𝓢'(E, F)) =
      ∂_{m} ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) f) : 𝓢'(E, F)) := by
  let g : E → ℂ := fun x =>
    Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))
  have hg : g.HasTemperateGrowth := by dsimp [g]; fun_prop
  change (((2 * Real.pi * Complex.I : ℂ) •
    SobolevIs.CM.Construction.l2FourierMultiplier hg (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) f :
      Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) = _
  rw [← Lp.toTemperedDistributionCLM_apply, map_smul, Lp.toTemperedDistributionCLM_apply,
    SobolevIs.CM.Construction.l2FourierMultiplier_distribution, SobolevIs.CM.Construction.sobolevL2Embedding_distribution,
    lineDeriv_eq_fourierMultiplierCLM, besselPotential,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  apply congrArg (fun symbol : E → ℂ =>
    (2 * Real.pi * Complex.I : ℂ) • fourierMultiplierCLM F symbol (f : 𝓢'(E, F)))
  ext x
  change Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) =
    (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * (inner ℝ x m : ℂ)
  rw [Complex.ofReal_mul, mul_comm]

theorem sobolevL2Derivative_norm_le (m : E) (f : Lp F 2 (volume : Measure E)) :
    ‖sobolevL2Derivative m f‖ ≤ (2 * Real.pi * ‖m‖) * ‖f‖ := by
  change ‖(2 * Real.pi * Complex.I : ℂ) •
    SobolevIs.CM.Construction.l2FourierMultiplierValue (g := fun x : E =>
      Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) f‖ ≤ _
  rw [norm_smul]
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc, mul_assoc (2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left
    (SobolevIs.CM.Construction.l2FourierMultiplierValue_norm_le (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) f)
    (by positivity)

omit [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- The completed-space derivative is the ordinary derivative on its original smooth functions. -/
theorem sobolevL2Derivative_schwartz (m : E) (f : 𝓢(E, ℂ)) :
    sobolevL2Derivative m (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f) =
      (∂_{m} f).toLp 2 (volume : Measure E) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change ((sobolevL2Derivative m (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)) : 𝓢'(E, ℂ)) =
    (((∂_{m} f).toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ))
  rw [sobolevL2Derivative_distribution, SobolevIs.CM.Construction.sobolevL2Embedding_schwartz,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact lineDerivOp_toTemperedDistributionCLM_eq f m

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction
