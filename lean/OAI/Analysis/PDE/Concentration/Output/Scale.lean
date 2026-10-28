import OAI.Analysis.PDE.Concentration.Output.Sector

noncomputable section
namespace OAI.Analysis.PDE.Concentration

theorem output_normalized_power (n : ℕ) {C h L w : ℝ}
    (hC : 0 < C) (hh : 0 < h) (hL : 0 < L) (hw : 0 ≤ w) :
    (w ^ 2 / (C * h ^ (2 * (n + 1)) *
      L ^ ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1)))) ^
        (((n : ℝ) + 2) / ((n : ℝ) + 1)) =
    (C ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)))⁻¹ * (h ^ (2 * (n + 2)))⁻¹ *
      L ^ (-(((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1))) *
      w ^ (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) := by
  let q : ℝ := ((n : ℝ) + 2) / ((n : ℝ) + 1)
  let M : ℝ := gaussianDerivativeOrder (n + 1)
  have hwq : (w ^ 2) ^ q = w ^ (2 * q) := by
    rw [← Real.rpow_natCast w 2, ← Real.rpow_mul hw]
    norm_num
  have hhq : (h ^ (2 * (n + 1))) ^ q = h ^ (2 * (n + 2)) := by
    rw [← Real.rpow_natCast h (2 * (n + 1)), ← Real.rpow_mul hh.le, ← Real.rpow_natCast h (2 * (n + 2))]
    congr 1
    dsimp [q]
    push_cast
    field_simp
  have hLq : (L ^ (M + (n + 1))) ^ q = L ^ ((M + (n + 1)) * q) :=
    (Real.rpow_mul hL.le _ _).symm
  change (w ^ 2 / (C * h ^ (2 * (n + 1)) * L ^ (M + (n + 1)))) ^ q =
    (C ^ q)⁻¹ * (h ^ (2 * (n + 2)))⁻¹ * L ^ (-q * (M + (n + 1))) * w ^ (2 * q)
  rw [Real.div_rpow (sq_nonneg _) (by positivity), hwq,
    Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC.le (by positivity), hhq, hLq]
  rw [show -q * (M + (n + 1)) = -((M + (n + 1)) * q) by ring, Real.rpow_neg hL.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem output_logarithmic_scale (n : ℕ) {L : ℝ} (hL : 0 < L) :
    L ^ (n + 3) *
      L ^ (-(((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1))) =
      L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) := by
  rw [← Real.rpow_natCast L (n + 3), ← Real.rpow_add hL]
  congr 1
  push_cast
  field_simp
  ring

theorem output_volume_weight_scale (n : ℕ) (c v C : ℝ) {h L : ℝ}
    (hh : 0 < h) (hL : 0 < L) :
    (c * h ^ 2) * (v * h ^ (2 * (n + 2)) * L ^ (n + 3)) *
      ((C ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)))⁻¹ * (h ^ (2 * (n + 2)))⁻¹ *
        L ^ (-(((n : ℝ) + 2) / ((n : ℝ) + 1)) *
          ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1)))) =
      (c * v / C ^ (((n : ℝ) + 2) / ((n : ℝ) + 1))) * h ^ 2 *
        L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
          (gaussianDerivativeOrder (n + 1) : ℝ)) := by
  calc
    _ = (c * v / C ^ (((n : ℝ) + 2) / ((n : ℝ) + 1))) * h ^ 2 *
      (L ^ (n + 3) * L ^ (-(((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1)))) := by
      field_simp
    _ = _ := by rw [output_logarithmic_scale n hL]

end OAI.Analysis.PDE.Concentration
