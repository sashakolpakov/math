import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.MeasureTheory.Kakeya.Log.Restriction
import OAI.MeasureTheory.Kakeya.Log.TubeBound
import OAI.MeasureTheory.Kakeya.Log.VolumeLocalization

open OAI.Analysis.Fourier.Wave

/-!
# Logarithmic lower bounds for Kakeya tube unions

The tubes here have unit-length core segments and actual radius `δ`. Their
centers are arbitrary, and their unit directions must be `δ`-separated.
The estimates are unconditional consequences of the logarithmic local-smoothing
theorem, and are independent of the Comparator challenge.
-/

open _root_.MeasureTheory

noncomputable section
namespace OAI.MeasureTheory.Kakeya

private theorem half_scale_log_le {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    1 + Real.log (1 / (δ / 2)) ≤ (1 + Real.log 2) * (1 + Real.log (1 / δ)) := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ).mpr hδone)
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hid : Real.log (1 / (δ / 2)) = Real.log 2 + Real.log (1 / δ) := by
    rw [one_div_div, Real.log_div (by norm_num) hδ.ne',
      Real.log_div one_ne_zero hδ.ne', Real.log_one]
    ring
  rw [hid]
  nlinarith [mul_nonneg htwo hlog]

private theorem half_scale_volume_coefficient_le {a M δ : ℝ}
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hδ : 0 < δ) (hδone : δ ≤ 1) (k N : ℕ) :
    (a / ((2 : ℝ) ^ k * (1 + Real.log 2) ^ N)) * (M * δ ^ k) /
        (1 + Real.log (1 / δ)) ^ N ≤
      a * (M * (δ / 2) ^ k) / (1 + Real.log (1 / (δ / 2))) ^ N := by
  have hlog : 0 < 1 + Real.log (1 / δ) := by
    have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
    linarith
  have hhalf : 0 < 1 + Real.log (1 / (δ / 2)) := by
    have hh : 0 < δ / 2 := by positivity
    have hh1 : δ / 2 ≤ 1 := by linarith
    have := Real.log_nonneg ((one_le_div hh).mpr hh1)
    linarith
  have htwo : 0 < 1 + Real.log 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hpow : (1 + Real.log (1 / (δ / 2))) ^ N ≤
      (1 + Real.log 2) ^ N * (1 + Real.log (1 / δ)) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hhalf.le (half_scale_log_le hδ hδone) N
  calc
    _ = a * (M * (δ / 2) ^ k) /
        ((1 + Real.log 2) ^ N * (1 + Real.log (1 / δ)) ^ N) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hhalf N) hpow

/-- Uniform occupied-volume bound for finitely many unit-length, radius-`δ`
tubes in `ℝⁿ` with `δ`-separated unit directions. There is no restriction on the
tube centers. The constant depends only on the dimension, not on the number of
tubes, their locations, or their radius. -/
theorem tube_union_logarithmic (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v x : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      c * ((m : ℝ) * δ ^ (n - 1)) /
          (1 + Real.log (1 / δ)) ^ (2 * n * (2 * n + 5)) ≤
        volume.real (⋃ i, tube δ (v i) (x i)) := by
  obtain ⟨C, hC, hext⟩ := logarithmic_tube_extension_of_restriction hn
    (logarithmic_local_restriction OAI.Analysis.Fourier.LocalSmoothing.logarithmic_refinement hn)
  obtain ⟨a, ha, H⟩ := local_critical_extension_logarithmic_tube_volume_global
    hn C hC (2 * n + 5) hext
  have htwo : 0 < 1 + Real.log 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  refine ⟨a / ((2 : ℝ) ^ (n - 1) * (1 + Real.log 2) ^ (2 * n * (2 * n + 5))),
    div_pos ha (mul_pos (by positivity) (pow_pos htwo _)), ?_⟩
  intro m δ hδ hδone v x hv hsep
  have hh : 0 < δ / 2 := by positivity
  have hh1 : δ / 2 ≤ 1 := by linarith
  have hsep' : ∀ i j, i ≠ j → δ / 2 ≤ dist (v i) (v j) := by
    intro i j hij
    exact (show δ / 2 ≤ δ by linarith).trans (hsep i j hij)
  have hbound := H m (δ / 2) hh hh1 v x hv hsep'
  have he : tubeUnion (δ / 2) v x = ⋃ i, tube δ (v i) (x i) := by
    simp only [tubeUnion, show 2 * (δ / 2) = δ by ring]
  rw [he] at hbound
  exact (half_scale_volume_coefficient_le ha.le (Nat.cast_nonneg m) hδ hδone
    (n - 1) (2 * n * (2 * n + 5))).trans hbound

/-- In three dimensions, at least `δ⁻²` direction-separated unit tubes occupy
volume at least `c / (1 + log (1/δ))^66`. The bound is uniform over all tube
centers and all scales `0 < δ ≤ 1`. -/
theorem tube_union_logarithmic_three_dimensional :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v x : Fin m → Space 3, (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) → 1 ≤ (m : ℝ) * δ ^ 2 →
      c / (1 + Real.log (1 / δ)) ^ 66 ≤
        volume.real (⋃ i, tube δ (v i) (x i)) := by
  obtain ⟨c, hc, H⟩ := tube_union_logarithmic 3 (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro m δ hδ hδone v x hv hsep hdense
  have hbound := H m δ hδ hδone v x hv hsep
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at hbound
  apply le_trans ?_ hbound
  apply div_le_div_of_nonneg_right
  · exact le_mul_of_one_le_right hc.le hdense
  · positivity

end OAI.MeasureTheory.Kakeya
