import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Translations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Difference Quotients -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction

noncomputable section

/-! Actual difference quotients, their Fourier symbols, and the uniform
first-derivative symbol bound used in local elliptic regularity. -/

open _root_.MeasureTheory FourierTransform Filter
open scoped _root_.Topology

def differenceQuotientSymbol (t a : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * ((Real.fourierChar (t * a) : ℂ) - 1)

theorem differenceQuotientSymbol_bound (t a : ℝ) :
    ‖differenceQuotientSymbol t a‖ ≤ 2 * Real.pi * |a| := by
  by_cases ht : t = 0
  · simp only [differenceQuotientSymbol, ht, Complex.ofReal_zero, inv_zero, zero_mul, norm_zero]
    positivity
  have hphase : ‖(Real.fourierChar (t * a) : ℂ) - 1‖ ≤ 2 * Real.pi * |t| * |a| := by
    calc
      _ = ‖Complex.exp (Complex.I * ((2 * Real.pi * (t * a) : ℝ) : ℂ)) - 1‖ := by
        rw [Real.fourierChar_apply, mul_comm _ Complex.I]
      _ ≤ ‖2 * Real.pi * (t * a)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = 2 * Real.pi * |t| * |a| := by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, Nat.abs_ofNat]
        ring
  rw [differenceQuotientSymbol, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |t|⁻¹ * (2 * Real.pi * |t| * |a|) := mul_le_mul_of_nonneg_left hphase (by positivity)
    _ = 2 * Real.pi * |a| := by field_simp [abs_ne_zero.mpr ht]

theorem differenceQuotientSymbol_tendsto (a : ℝ) :
    Tendsto (fun t : ℝ => differenceQuotientSymbol t a) (𝓝[≠] 0)
      (𝓝 ((2 * Real.pi * a : ℝ) * Complex.I : ℂ)) := by
  have hd : HasDerivAt (fun t : ℝ => (Real.fourierChar (t * a) : ℂ))
      (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) 0 := by
    simpa only [Real.fourierChar_apply, id_eq, one_mul, zero_mul, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero] using
      ((((hasDerivAt_id (0 : ℝ)).mul_const a).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  have hslope : (fun t : ℝ => differenceQuotientSymbol t a) =
      slope (fun t : ℝ => (Real.fourierChar (t * a) : ℂ)) 0 := by
    funext t
    rw [slope_def_module]
    simp only [differenceQuotientSymbol, sub_zero, zero_mul,
      AddChar.map_zero_eq_one, Circle.coe_one, Complex.real_smul, Complex.ofReal_inv]
  rw [hslope]
  exact hd.tendsto_slope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def l2DifferenceQuotient (m : E) (t : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (t : ℂ)⁻¹ • ((Translations.CM.Construction.l2Translation (t • m)).toContinuousLinearMap - ContinuousLinearMap.id ℂ _)

theorem l2DifferenceQuotient_coe (m : E) (t : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), l2DifferenceQuotient m t u x =
      (t : ℂ)⁻¹ * (u (x + t • m) - u x) := by
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (Translations.CM.Construction.l2Translation (t • m) u - u),
    Lp.coeFn_sub (Translations.CM.Construction.l2Translation (t • m) u) u, Translations.CM.Construction.l2Translation_coe (t • m) u] with x hs hd ht
  change ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u) : Lp ℂ 2 volume) x = _
  simp only [hs, hd, Pi.smul_apply, Pi.sub_apply, ht, smul_eq_mul]

theorem fourier_l2DifferenceQuotient_coe (m : E) (t : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (l2DifferenceQuotient m t u) : Lp ℂ 2 volume) x =
      differenceQuotientSymbol t (inner ℝ m x) * (𝓕 u : Lp ℂ 2 volume) x := by
  have heq : 𝓕 (l2DifferenceQuotient m t u) =
      (t : ℂ)⁻¹ • (Translations.CM.Construction.l2TranslationPhase (t • m) (𝓕 u) - 𝓕 u) := by
    change (Lp.fourierTransformₗᵢ E ℂ) ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u)) = _
    rw [map_smul, map_sub]
    change (t : ℂ)⁻¹ • (𝓕 (Translations.CM.Construction.l2Translation (t • m) u) - 𝓕 u) = _
    rw [Translations.CM.Construction.fourier_l2Translation]
  rw [heq]
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (Translations.CM.Construction.l2TranslationPhase (t • m) (𝓕 u) - 𝓕 u),
    Lp.coeFn_sub (Translations.CM.Construction.l2TranslationPhase (t • m) (𝓕 u)) (𝓕 u),
    Translations.CM.Construction.l2TranslationPhase_coe (t • m) (𝓕 u)] with x hs hd hp
  simp only [hs, hd, Pi.smul_apply, Pi.sub_apply, hp, smul_eq_mul,
    real_inner_smul_left, differenceQuotientSymbol]
  ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction
