import OAI.Analysis.Fourier.Restriction.Polar

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The radial Jacobian gives the precise annular loss before taking an
`Lᵖ` root. The upper endpoint is arbitrary. -/
theorem lintegral_radial_annulus_le {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫⁻ ω, ∫⁻ t in Icc a b, F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (ENNReal.ofReal (a ^ (n - 1)))⁻¹ * ∫⁻ x, F x := by
  let c := ENNReal.ofReal (a ^ (n - 1))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos ha _))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let L := ∫⁻ ω, ∫⁻ t in Icc a b, F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n
  have hL : c * L ≤ ∫⁻ x, F x := by
    calc
      c * L = ∫⁻ ω, ∫⁻ t in Icc a b, c * F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
        dsimp [L]
        rw [← lintegral_const_mul'' c (by fun_prop)]
        apply lintegral_congr
        intro ω
        exact (lintegral_const_mul'' c (by fun_prop)).symm
      _ ≤ ∫⁻ ω, ∫⁻ t in Icc a b, ENNReal.ofReal (t ^ (n - 1)) * F (t • ω)
          ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
        apply lintegral_mono
        intro ω
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hpow : a ^ (n - 1) ≤ t ^ (n - 1) := pow_le_pow_left₀ ha.le ht.1 _
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl
      _ ≤ ∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (n - 1)) * F (t • ω)
          ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
        apply lintegral_mono
        intro ω
        apply lintegral_mono' (Measure.restrict_mono (fun t ht ↦ ha.trans_le ht.1) le_rfl)
        exact le_rfl
      _ = ∫⁻ x, F x := (lintegral_polar_sphereMeasure hn hF).symm
  calc
    L = c⁻¹ * (c * L) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc hct, one_mul]
    _ ≤ c⁻¹ * ∫⁻ x, F x := mul_le_mul' le_rfl hL

end OAI.Analysis.Fourier.Restriction
