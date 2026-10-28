import OAI.Analysis.Fourier.SquareFunction.GlobalSharp

/-! Comparison constants and norm forms of the checked sharp inequality. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral Filter
open scoped ENNReal Topology

theorem positiveSetMean_toReal_eq_setAverage {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hfn : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f Q μ) :
    (positiveSetMean μ f Q).toReal = ⨍ x in Q, f x ∂μ := by
  rw [positiveSetMean, ← ofReal_setAverage hf (Eventually.of_forall hfn),
    ENNReal.toReal_ofReal (average_nonneg hfn)]

theorem enorm_setAverage_le {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) (f : X → H) (Q : Set X) :
    ‖⨍ x in Q, f x ∂μ‖ₑ ≤ (∫⁻ x in Q, ‖f x‖ₑ ∂μ) / μ Q := by
  rw [← setLAverage_eq]
  exact enorm_integral_le_lintegral_enorm f

/-- Passing from any comparison constant to the actual mean costs at most
two. This is the factor used after the low/middle/high decomposition. -/
theorem setOscillation_le_twice_centered {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hfn : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f Q μ) (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) (c : ℝ) :
    setOscillation μ f Q ≤ 2 * ((∫⁻ x in Q, ‖f x - c‖ₑ ∂μ) / μ Q) := by
  let a : ℝ := ⨍ x in Q, f x ∂μ
  let E : ℝ≥0∞ := ∫⁻ x in Q, ‖f x - c‖ₑ ∂μ
  have hc : IntegrableOn (fun _ : X => c) Q μ := integrableOn_const hQtop
  have hgap : ‖a - c‖ₑ ≤ E / μ Q := by
    have he : (⨍ x in Q, f x - c ∂μ) = a - c := by
      rw [setAverage_fun_sub hf hc, setAverage_const hQ0 hQtop]
    rw [← he]
    exact enorm_setAverage_le μ (fun x => f x - c) Q
  rw [setOscillation, positiveSetMean_toReal_eq_setAverage μ f Q hfn hf]
  calc
    _ ≤ (E + ‖a - c‖ₑ * μ Q) / μ Q := by
      apply ENNReal.div_le_div_right
      calc
        _ ≤ ∫⁻ x in Q, ‖f x - c‖ₑ + ‖a - c‖ₑ ∂μ := by
          apply lintegral_mono
          intro x
          change ‖f x - a‖ₑ ≤ ‖f x - c‖ₑ + ‖a - c‖ₑ
          rw [show f x - a = (f x - c) - (a - c) by ring]
          exact enorm_sub_le
        _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ (E + (E / μ Q) * μ Q) / μ Q :=
      ENNReal.div_le_div_right (add_le_add le_rfl (mul_le_mul_left hgap (μ Q))) (μ Q)
    _ = _ := by
      rw [ENNReal.div_mul_cancel hQ0 hQtop, ← two_mul]
      simp only [E, div_eq_mul_inv, mul_assoc]

/-- Norm form of the global cube-oscillation estimate. -/
theorem eLpNorm_le_of_cube_oscillation {ι : Type*} [Fintype ι] [Nonempty ι]
    (f G : (ι → ℝ) → ℝ) (hfn : ∀ x, 0 ≤ f x) (hGn : ∀ x, 0 ≤ G x)
    (hfc : Continuous f) (hf : Integrable f) (hG : AEStronglyMeasurable G)
    {p γ : ℝ} (hp : 1 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p < 1)
    (hosc : ∀ Q : Box ι, IsCubeBox Q → ∀ x ∈ Q,
      setOscillation volume f Q ≤ ENNReal.ofReal (G x)) :
    eLpNorm f (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p))) ^ (1 / p) *
        ENNReal.ofReal (((2 : ℝ) ^ Fintype.card ι + 1) / γ) *
          eLpNorm G (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hfc.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hG]
  simp only [ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal (hfn _),
    Real.enorm_eq_ofReal (hGn _)]
  have h := ENNReal.rpow_le_rpow
    (global_oscillation_moment_bound f G hfn hGn hfc hf hp hγ hsmall hosc)
    (one_div_pos.mpr hp0).le
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le,
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  simpa only [mul_assoc] using h

end OAI.Analysis.Fourier.SquareFunction
