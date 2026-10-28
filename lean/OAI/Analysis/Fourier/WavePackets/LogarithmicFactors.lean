import OAI.Analysis.Fourier.WavePackets.SectorScale

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open scoped ENNReal

theorem sector_root_log_factor {c k p α x : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hp : 2 ≤ p) (hx : 0 < x) :
    (ENNReal.ofReal (c * x ^ (p * α)) * ENNReal.ofReal k ^ p *
      (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) =
    ENNReal.ofReal ((c * k ^ p * (2 : ℝ) ^ (p - 2)) ^ (1 / p) * x ^ α) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hreal : ((c * x ^ (p * α)) * k ^ p * (2 : ℝ) ^ (p - 2)) ^ (1 / p) =
      (c * k ^ p * (2 : ℝ) ^ (p - 2)) ^ (1 / p) * x ^ α := by
    rw [show c * x ^ (p * α) * k ^ p * (2 : ℝ) ^ (p - 2) =
      (c * k ^ p * (2 : ℝ) ^ (p - 2)) * x ^ (p * α) by ring]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx.le]
    congr 1
    congr 1
    field_simp
  rw [ENNReal.ofReal_rpow_of_nonneg hk hp0.le,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp2,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_pos.mpr hp0).le,
    hreal]

/-- The sector-count, amplitude-count, and restricted estimate have
exactly the combined logarithmic exponent claimed in the manuscript. -/
theorem assembled_log_factor (d : ℕ) {a b c k B D γ₀ p x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k) (_ : 0 ≤ B)
    (hD : 0 < D) (hγ₀ : 0 < γ₀) (hp : 2 ≤ p) (hx : 0 < x) :
    ENNReal.ofReal (a * (logarithmicSectorWidth γ₀ (D * x))⁻¹ ^ d) *
      ENNReal.ofReal (b * x) *
      ((ENNReal.ofReal (c * x ^ (p * (3 * ((d : ℝ) + 4) / 2))) *
        ENNReal.ofReal k ^ p * (2 : ℝ≥0∞) ^ (p - 2)) ^ (1 / p) * ENNReal.ofReal B) =
      ENNReal.ofReal
        ((a * (γ₀⁻¹) ^ d * D ^ ((d : ℝ) / 2) * b *
          (c * k ^ p * (2 : ℝ) ^ (p - 2)) ^ (1 / p) * B) * x ^ (2 * d + 7)) := by
  rw [sector_root_log_factor hc hk hp hx, logarithmicSectorWidth_count d hγ₀ (mul_pos hD hx),
    Real.mul_rpow hD.le hx.le]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hexp : (d : ℝ) / 2 + 1 + 3 * ((d : ℝ) + 4) / 2 = (2 * d + 7 : ℕ) := by
    push_cast
    ring
  rw [← Real.rpow_natCast x (2 * d + 7), ← hexp, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
  ring

end OAI.Analysis.Fourier.WavePackets
