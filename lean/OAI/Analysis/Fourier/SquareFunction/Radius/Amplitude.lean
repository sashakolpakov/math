import OAI.Analysis.Fourier.SquareFunction.Radius.Hilbert

/-! Bounded amplitudes and unitary modulations in the radius Hilbert space. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal NNReal

theorem enorm_radiusToL2_mul_le (a b : C(RadiusInterval, ℂ)) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ r, ‖a r‖ ≤ C) :
    ‖radiusToL2 (a * b)‖ₑ ≤ ENNReal.ofReal C * ‖radiusToL2 b‖ₑ := by
  rw [enorm_radiusToL2, enorm_radiusToL2]
  calc
    _ ≤ eLpNorm (C • (b : RadiusInterval → ℂ)) 2 radiusMeasure := by
      apply eLpNorm_mono (a * b).continuous.aestronglyMeasurable
      intro r
      change ‖a r * b r‖ ≤ ‖C • b r‖
      rw [norm_mul, norm_smul, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha r) (norm_nonneg _)
    _ = _ := by rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC]

noncomputable def radiusModulation (η : ℝ) : C(RadiusInterval, ℂ) :=
  ⟨fun r => Complex.exp ((2 * Real.pi * (r : ℝ) * η : ℝ) * Complex.I), by fun_prop⟩

theorem norm_radiusModulation (η : ℝ) (r : RadiusInterval) :
    ‖radiusModulation η r‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_radiusModulation : Continuous radiusModulation := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : ℝ × RadiusInterval =>
    Complex.exp ((2 * Real.pi * (z.2 : ℝ) * z.1 : ℝ) * Complex.I))
  fun_prop

theorem norm_radiusModulation_le (η : ℝ) : ‖radiusModulation η‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro r
  exact (norm_radiusModulation η r).le

theorem enorm_radiusToL2_modulation (η : ℝ) (b : C(RadiusInterval, ℂ)) :
    ‖radiusToL2 (radiusModulation η * b)‖ₑ = ‖radiusToL2 b‖ₑ := by
  rw [enorm_radiusToL2, enorm_radiusToL2]
  apply eLpNorm_congr_norm_ae (radiusModulation η * b).continuous.aestronglyMeasurable
    b.continuous.aestronglyMeasurable
  filter_upwards [] with r
  change ‖radiusModulation η r * b r‖ = ‖b r‖
  rw [norm_mul, norm_radiusModulation, one_mul]

end OAI.Analysis.Fourier.SquareFunction
