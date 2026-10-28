import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialUpper
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocusingLower

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- Uniform pointwise upper bound for the actual initial focusing packet. -/
theorem focusingWave_initial_sup {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 2 ≤ N → ∀ x : Space n,
      ‖focusingWave n N (-(3/2)) x‖ ≤ C * N^((n:ℝ)-radialOrder n) := by
  obtain ⟨C,hC,hb⟩ := radialWave_time_bound hn
  let a : ℝ := ((2*Real.pi)^n)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a*C*(3/4:ℝ)^(-radialOrder n),by positivity,fun N hN x => ?_⟩
  have hNp : 0 < N := by linarith
  have ht : |N*(-(3/2:ℝ))|/2 = (3/4:ℝ)*N := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have htime : 2 ≤ |N*(-(3/2:ℝ))| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hh := hb (N*(-(3/2))) htime (N•x)
  rw [ht,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3/4) hNp.le] at hh
  rw [focusingWave_scale hNp,focusingWave_one_eq hn,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (pow_pos hNp n),abs_of_pos ha]
  have he : N^n * N^(-radialOrder n) = N^((n:ℝ)-radialOrder n) := by
    simpa only [Real.rpow_natCast,sub_eq_add_neg] using
      (Real.rpow_add hNp (n:ℝ) (-radialOrder n)).symm
  have h := mul_le_mul_of_nonneg_left hh (mul_nonneg (pow_nonneg hNp.le n) ha.le)
  change N^n * (a * _) ≤ _
  rw [← he]
  convert h using 1 <;> ring

theorem focusing_packet_initial_sup {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 2 ≤ N → ∀ f : SchwartzMap (Space n) ℂ,
      (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N (3/2)) →
      ∀ x : Space n, ‖f x‖ ≤ C * N^((n:ℝ)-radialOrder n) := by
  obtain ⟨C,hC,hb⟩ := focusingWave_initial_sup hn
  refine ⟨C,hC,fun N hN f hf x => ?_⟩
  rw [focusing_packet_initial hf]
  exact hb N hN x

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
