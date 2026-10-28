import OAI.Analysis.Fourier.BochnerRiesz.Projection
import OAI.Analysis.Fourier.SquareFunction.KernelDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem schwartz_kernel_decay {n : ℕ} (K : SchwartzMap (Space n) ℂ) (q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      ‖K x‖ ≤ C * (‖x‖ + 1) ^ (-q) ∧
      ‖fderiv ℝ K x‖ ≤ C * (‖x‖ + 1) ^ (-q) := by
  obtain ⟨N, hN⟩ := exists_nat_gt q
  let B : ℝ := 2 ^ N * (Finset.Iic (N, 1)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) K
  have hB : 0 ≤ B := by positivity
  refine ⟨B + 1, by positivity, ?_⟩
  have hd (j : ℕ) (hj : j ≤ 1) (x : Space n) :
      ‖iteratedFDeriv ℝ j K x‖ ≤ (B + 1) * (‖x‖ + 1) ^ (-q) := by
    have hb : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j K x‖ ≤ B :=
      SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (N, 1)) (k := N) (n := j) le_rfl hj K x
    have ht : 0 < 1 + ‖x‖ := by positivity
    have hb' : ‖iteratedFDeriv ℝ j K x‖ ≤ (B + 1) * (1 + ‖x‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg ht.le, Real.rpow_natCast, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos ht N)).mpr
      nlinarith
    apply hb'.trans
    rw [add_comm ‖x‖ 1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (by linarith)
  intro x
  constructor
  · simpa using hd 0 (by omega) x
  · simpa only [norm_iteratedFDeriv_one] using hd 1 le_rfl x

end OAI.Analysis.Fourier.BochnerRiesz
