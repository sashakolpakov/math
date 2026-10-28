import OAI.MeasureTheory.Kakeya.DyadicCover

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def ballCoverCost (s : ℝ) (r : ℕ → ℝ) : ℝ≥0∞ := ∑' j, ENNReal.ofReal (r j) ^ s

theorem dyadic_ball_volume_scale {n : ℕ} {s δ r : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hr : δ / 2 < r) :
    (3 * δ) ^ n ≤ (3 ^ n * 2 ^ s * δ ^ ((n : ℝ) - s)) * r ^ s := by
  have hrpos : 0 < r := lt_trans (by positivity) hr
  have hsplit : δ ^ n = δ ^ ((n : ℝ) - s) * δ ^ s := by
    rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_natCast]
  have hpow : δ ^ s ≤ (2 * r) ^ s :=
    Real.rpow_le_rpow hδ.le (by linarith) hs.le
  calc
    (3 * δ) ^ n = 3 ^ n * (δ ^ ((n : ℝ) - s) * δ ^ s) := by rw [mul_pow, hsplit]
    _ ≤ 3 ^ n * (δ ^ ((n : ℝ) - s) * (2 * r) ^ s) := by gcongr
    _ = (3 ^ n * 2 ^ s * δ ^ ((n : ℝ) - s)) * r ^ s := by
      rw [Real.mul_rpow (by norm_num) hrpos.le]
      ring

theorem volume_dyadicExpandedSet_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    volume (dyadicExpandedSet x r k) ≤
      (ENNReal.ofReal (3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) *
        volume (Metric.ball (0 : Space n) 1)) * ballCoverCost s r := by
  have hd := dyadicRadius_pos k
  let B : ℝ≥0∞ := ENNReal.ofReal (3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) *
        volume (Metric.ball (0 : Space n) 1)
  have hterm (j : ℕ) : volume (⋃ _ : j ∈ dyadicIndices r k,
      Metric.ball (x j) (3 * dyadicRadius k)) ≤ B * ENNReal.ofReal (r j) ^ s := by
    by_cases hj : j ∈ dyadicIndices r k
    · have hjlo : dyadicRadius k / 2 < r j := by
        simpa only [dyadicRadius, pow_succ, mul_one_div] using hj.1
      have hjpos : 0 < r j := lt_trans (by exact div_pos (dyadicRadius_pos k) (by norm_num)) hjlo
      have hb : volume (Metric.ball (x j) (3 * dyadicRadius k)) ≤ B * ENNReal.ofReal (r j) ^ s := by
        rw [Measure.addHaar_ball_of_pos volume _ (by positivity : 0 < 3 * dyadicRadius k)]
        simp only [Space, finrank_euclideanSpace_fin]
        rw [ENNReal.ofReal_rpow_of_nonneg hjpos.le hs.le]
        calc
          _ ≤ ENNReal.ofReal ((3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) * r j ^ s) *
              volume (Metric.ball (0 : Space n) 1) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (dyadic_ball_volume_scale hs (dyadicRadius_pos k) hjlo)) le_rfl
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity)]
            dsimp only [B]
            ring
      simpa [hj] using hb
    · simp [hj]
  calc
    volume (dyadicExpandedSet x r k) ≤ ∑' j, volume (⋃ _ : j ∈ dyadicIndices r k,
        Metric.ball (x j) (3 * dyadicRadius k)) := measure_iUnion_le _
    _ ≤ ∑' j, B * ENNReal.ofReal (r j) ^ s := ENNReal.tsum_le_tsum hterm
    _ = B * ballCoverCost s r := ENNReal.tsum_mul_left

end OAI.MeasureTheory.Kakeya
