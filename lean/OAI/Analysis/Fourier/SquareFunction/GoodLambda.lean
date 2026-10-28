import OAI.Analysis.Fourier.SquareFunction.Maximal

/-! The layer-cake and absorption step of the dyadic sharp-function argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

/-- Distribution-function inequalities add with exactly the same constants
after taking positive moments. -/
theorem power_moment_le_of_superlevel_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u v w : X → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (hun : ∀ x, 0 ≤ u x) (hvn : ∀ x, 0 ≤ v x) (hwn : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞)
    (h : ∀ t > 0, μ {x | t < u x} ≤ μ {x | t < v x} + c * μ {x | t < w x}) :
    (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ) +
        c * ∫⁻ x, ENNReal.ofReal (w x) ^ p ∂μ := by
  have hm (f : X → ℝ) : Measurable (fun t : ℝ => μ {x | t < f x} *
      ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1)) := by
    have hmono : Antitone (fun t : ℝ => μ {x | t < f x}) :=
      fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx)
    exact (hmono.measurable.mul measurable_const).mul
      (measurable_id.ennreal_ofReal.pow_const _)
  rw [lintegral_power_layercake μ hu hun hp,
    lintegral_power_layercake μ hv hvn hp, lintegral_power_layercake μ hw hwn hp]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (μ {x | t < v x} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1)) + c *
        (μ {x | t < w x} * ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ (μ {x | t < v x} + c * μ {x | t < w x}) *
            ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
          gcongr
          exact h t ht
        _ = _ := by ring
    _ = _ := by rw [lintegral_add_left (hm v), lintegral_const_mul c (hm w)]

/-- The small same-side term in a good-lambda estimate can be absorbed when
the left moment is finite. This is why the source first works with finite
families whose square function already belongs to `Lᵖ`. -/
theorem ennreal_absorb {U V : ℝ≥0∞} {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hU : U < ∞)
    (h : U ≤ V + ENNReal.ofReal θ * U) :
    U ≤ ENNReal.ofReal (1 / (1 - θ)) * V := by
  have hs : 0 < 1 - θ := sub_pos.mpr hθ1
  have hc : 0 < (1 : ℝ) / (1 - θ) := div_pos zero_lt_one hs
  by_cases hV : V = ∞
  · rw [hV, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)]
    exact le_top
  have hmul : ENNReal.ofReal θ * U ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU.ne
  have hr := (ENNReal.toReal_le_toReal hU.ne (ENNReal.add_ne_top.mpr ⟨hV, hmul⟩)).mpr h
  rw [ENNReal.toReal_add hV hmul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ] at hr
  apply (ENNReal.toReal_le_toReal hU.ne
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  calc
    U.toReal ≤ V.toReal / (1 - θ) := (le_div_iff₀ hs).mpr (by nlinarith)
    _ = (1 / (1 - θ)) * V.toReal := by ring

/-- A good-lambda distribution inequality yields the corresponding strong
positive-moment estimate, with its explicit absorption constant. -/
theorem power_moment_le_of_good_lambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hun : ∀ x, 0 ≤ u x) (hvn : ∀ x, 0 ≤ v x)
    {p a η : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hsmall : η * a ^ p < 1)
    (hfin : (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ) < ∞)
    (hgood : ∀ t > 0, μ {x | t < u x} ≤ μ {x | t < v x} +
      ENNReal.ofReal η * μ {x | t < a * u x}) :
    (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ) ≤
      ENNReal.ofReal (1 / (1 - η * a ^ p)) *
        ∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ := by
  have hscale : (∫⁻ x, ENNReal.ofReal (a * u x) ^ p ∂μ) =
      ENNReal.ofReal (a ^ p) * ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ := by
    simp_rw [ENNReal.ofReal_mul ha, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      ENNReal.ofReal_rpow_of_nonneg ha hp.le]
    exact lintegral_const_mul _ (hu.ennreal_ofReal.pow_const p)
  have h := power_moment_le_of_superlevel_add μ hu hv (hu.const_mul a)
    hun hvn (fun x => mul_nonneg ha (hun x)) hp (ENNReal.ofReal η) hgood
  rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul hη] at h
  exact ennreal_absorb (mul_nonneg hη (Real.rpow_nonneg ha _)) hsmall hfin h

end OAI.Analysis.Fourier.SquareFunction
