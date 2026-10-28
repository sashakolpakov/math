import Mathlib

open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def mixedThreshold (a t : ℝ) : ℝ := t ^ (-1 / (a - 1))

theorem mixedThreshold_pos {a t : ℝ} (ht : 0 < t) : 0 < mixedThreshold a t :=
  Real.rpow_pos_of_pos ht _

theorem mixedThreshold_power {a t : ℝ} (ha : 1 < a) (ht : 0 < t) :
    mixedThreshold a t ^ (1 - a) = t := by
  rw [mixedThreshold, ← Real.rpow_mul ht.le]
  have hne : a - 1 ≠ 0 := by linarith
  have he : (-1 / (a - 1)) * (1 - a) = 1 := by
    field_simp
    ring
  rw [he, Real.rpow_one]

theorem mixedThreshold_ratio {a s t : ℝ} (ha : 1 < a) (hs : 0 ≤ s) (ht : 0 < t) :
    ENNReal.ofReal (mixedThreshold a t ^ (s - a)) /
        ENNReal.ofReal (mixedThreshold a t ^ (1 - a)) ^ s =
      ENNReal.ofReal (t ^ (-(a * (s - 1) / (a - 1)))) := by
  rw [mixedThreshold_power ha ht, ENNReal.ofReal_rpow_of_nonneg ht.le hs,
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht s),
    mixedThreshold, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
  congr 2
  have hne : a - 1 ≠ 0 := by linarith
  field_simp
  ring

end OAI.Analysis.Fourier.Restriction
