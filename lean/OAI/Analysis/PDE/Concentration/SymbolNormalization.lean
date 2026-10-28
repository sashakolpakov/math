import OAI.Analysis.PDE.Concentration.InverseSymbol

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem gaussian_prefactor_normalization (d : ℕ) {k h L : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) (hL : 0 < L) :
    (k / (h * (h * L))) ^ ((d : ℝ) / 2) =
      (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2) * k ^ ((d : ℝ) / 2) := by
  have hhalf : h ^ ((d : ℝ) / 2) * h ^ ((d : ℝ) / 2) = h ^ d := by
    rw [← Real.rpow_add hh, show (d : ℝ) / 2 + d / 2 = d by ring, Real.rpow_natCast]
  rw [Real.div_rpow hk (by positivity), Real.mul_rpow hh.le (by positivity),
    Real.mul_rpow hh.le hL.le, ← mul_assoc, hhalf,
    show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hL.le]
  field_simp

theorem gaussian_forward_inverse_amplitude {d : ℕ} {W : TransverseSpace d}
    {η : OAI.Analysis.Calculus.Current.SpatialSpace d} (hk : 0 < gaussianFrequencyK η) (hb : gaussianB0 (W, η) ≠ 0) :
    gaussianForwardAmplitude 0 (W, η) * gaussianInverseAmplitude (W, η) = 1 := by
  have hp : gaussianFrequencyK η ^ ((d : ℝ) / 2) *
      gaussianFrequencyK η ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hk, show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  simp only [gaussianForwardAmplitude, gaussianInverseAmplitude, gaussianB, ↓reduceIte,
    ← Complex.ofReal_mul, ← Complex.ofReal_one]
  congr 1
  calc
    _ = (gaussianB0 (W, η) * (gaussianB0 (W, η))⁻¹) *
        (gaussianFrequencyK η ^ ((d : ℝ) / 2) * gaussianFrequencyK η ^ (-(d : ℝ) / 2)) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hb, hp, one_mul]

theorem gaussian_inverse_prefactor_normalization (d : ℕ) {k h L : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) (hL : 0 < L) :
    (k / (h * (h * L))) ^ (-(d : ℝ) / 2) =
      h ^ d * L ^ ((d : ℝ) / 2) * k ^ (-(d : ℝ) / 2) := by
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg (div_nonneg hk (by positivity)), gaussian_prefactor_normalization d hk hh hL]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg hL.le, Real.rpow_neg hk]
  simp only [mul_inv_rev, inv_inv]
  ring

/-- The normalized definition is exactly the source symbol at `y=hL`. -/
theorem gaussianForwardSymbol_eq_source {d : ℕ} (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) {h L : ℝ} (hh : 0 < h) (hL : 0 < L)
    (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (hk : 0 ≤ gaussianFrequencyK η) :
    gaussianForwardSymbol j ρ χ h L W η =
      radialAngularCutoff ρ χ (Real.sqrt L) η * (gaussianB j (W, η) : ℂ) *
        ((gaussianFrequencyK η / (h * (h * L))) ^ ((d : ℝ) / 2) : ℝ) *
        Complex.exp (-(L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) := by
  rw [gaussian_prefactor_normalization d hk hh hL]
  simp only [gaussianForwardSymbol, Pi.smul_apply, Complex.real_smul,
    gaussianForwardCore, gaussianForwardAmplitude]
  push_cast
  ring

theorem gaussianInverseSymbol_eq_source {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) {h L : ℝ} (hh : 0 < h) (hL : 0 < L)
    (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (hk : 0 ≤ gaussianFrequencyK η) :
    gaussianInverseSymbol ρ χ h L W η =
      radialAngularCutoff ρ χ (Real.sqrt L) η * ((gaussianB0 (W, η))⁻¹ : ℝ) *
        ((gaussianFrequencyK η / (h * (h * L))) ^ (-(d : ℝ) / 2) : ℝ) *
        Complex.exp ((L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) := by
  rw [gaussian_inverse_prefactor_normalization d hk hh hL]
  simp only [gaussianInverseSymbol, Pi.smul_apply, Complex.real_smul,
    gaussianInverseCore, gaussianInverseAmplitude]
  push_cast
  ring

theorem gaussian_normalization_cancel (d : ℕ) {h L : ℝ} (hh : 0 < h) (hL : 0 < L) :
    ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) * (h ^ d * L ^ ((d : ℝ) / 2)) = 1 := by
  have hp : L ^ (-(d : ℝ) / 2) * L ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hL, show -(d : ℝ) / 2 + d / 2 = 0 by ring, Real.rpow_zero]
  calc
    _ = ((h ^ d)⁻¹ * h ^ d) * (L ^ (-(d : ℝ) / 2) * L ^ ((d : ℝ) / 2)) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ (pow_ne_zero _ hh.ne'), hp, one_mul]

/-- Exact inverse-symbol recovery: on the positive-frequency region the
forward and inverse multipliers multiply to the square of the cutoff. -/
theorem gaussian_symbols_recover {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) {h L : ℝ} (hh : 0 < h) (hL : 0 < L)
    (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (hk : 0 < gaussianFrequencyK η) (hb : gaussianB0 (W, η) ≠ 0) :
    gaussianForwardSymbol 0 ρ χ h L W η * gaussianInverseSymbol ρ χ h L W η =
      (radialAngularCutoff ρ χ (Real.sqrt L) η) ^ 2 := by
  have he : Complex.exp (-(L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) *
      Complex.exp ((L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  simp only [gaussianForwardSymbol, gaussianInverseSymbol, Pi.smul_apply,
    Complex.real_smul, gaussianForwardCore, gaussianInverseCore]
  calc
    _ = (((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) * (h ^ d * L ^ ((d : ℝ) / 2)) : ℝ) *
        (radialAngularCutoff ρ χ (Real.sqrt L) η) ^ 2 *
        (gaussianForwardAmplitude 0 (W, η) * gaussianInverseAmplitude (W, η)) *
        (Complex.exp (-(L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) *
          Complex.exp ((L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ))) := by
      push_cast
      ring
    _ = _ := by rw [gaussian_normalization_cancel d hh hL,
      gaussian_forward_inverse_amplitude hk hb, he]; simp

end OAI.Analysis.PDE.Concentration
