import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialFormula
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocusingWave

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

theorem focusingWave_one_eq {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (x : Space n) :
    focusingWave n 1 t x = (((2*Real.pi)^n)⁻¹ : ℝ) • radialWave n t x := by
  simpa only [focusingWave,inv_one,one_smul] using angularInverse_radial_formula hn t x

/-- The actual frequency-N half-wave has the predicted lower amplitude on
outgoing shells of width N⁻¹. -/
theorem focusingWave_shell_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ η k R : ℝ, 0 < η ∧ 0 < k ∧ 1 ≤ R ∧ ∀ N : ℝ, 0 < N →
      ∀ t : ℝ, ∀ x : Space n, R ≤ N*‖x‖ → |N*(‖x‖-t)| ≤ η →
      k * N ^ ((n:ℝ)-radialOrder n) * ‖x‖ ^ (-radialOrder n) ≤ ‖focusingWave n N t x‖ := by
  obtain ⟨η,k,R,hη,hk,hR,h⟩ := radialWave_shell_lower hn
  let a : ℝ := ((2*Real.pi)^n)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨η,a*k,R,hη,mul_pos ha hk,hR,fun N hN t x hx ht => ?_⟩
  have hnorm : ‖N • x‖ = N*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hN]
  have hnx : 0 < N*‖x‖ := lt_of_lt_of_le zero_lt_one (hR.trans hx)
  have hr : 0 < ‖x‖ := (mul_pos_iff_of_pos_left hN).mp hnx
  have ht' : |‖N • x‖-N*t| ≤ η := by simpa only [hnorm,mul_sub] using ht
  have hl := h (N*t) (N • x) (by simpa only [hnorm] using hx) ht'
  rw [focusingWave_scale hN,focusingWave_one_eq hn,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (pow_pos hN _),abs_of_pos ha]
  have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg (pow_nonneg hN.le n) ha.le)
  rw [hnorm,Real.mul_rpow hN.le hr.le] at hh
  have he : N^n * N^(-radialOrder n) = N^((n:ℝ)-radialOrder n) := by
    simpa only [Real.rpow_natCast,sub_eq_add_neg] using
      (Real.rpow_add hN (n:ℝ) (-radialOrder n)).symm
  convert hh using 1 <;> try ring_nf
  calc
    a*k*N^((n:ℝ)-radialOrder n)*‖x‖^(-radialOrder n) =
      a*k*(N^n*N^(-radialOrder n))*‖x‖^(-radialOrder n) := by rw [he]
    _ = _ := by ring

/-- A one-sided annular shell is enough for all sharpness integrals. -/
theorem focusingWave_outgoing_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ η k A : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < k ∧ 1 ≤ A ∧ ∀ N : ℝ, 0 < N →
      ∀ t : ℝ, A/N ≤ t → ∀ x : Space n,
      t ≤ ‖x‖ → ‖x‖ ≤ t+η/N →
      k * N ^ ((n:ℝ)-radialOrder n) * t ^ (-radialOrder n) ≤ ‖focusingWave n N t x‖ := by
  obtain ⟨η,k,R,hη,hk,hR,h⟩ := focusingWave_shell_lower hn
  have hm : 0 ≤ radialOrder n := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [radialOrder]
    linarith
  refine ⟨min η 1,k*2^(-radialOrder n),R,lt_min hη zero_lt_one,min_le_right _ _,
    mul_pos hk (by positivity),hR,fun N hN t ht x hr hr' => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le (div_pos (lt_of_lt_of_le zero_lt_one hR) hN) ht
  have hNR : R ≤ N*t := by simpa only [mul_comm] using (div_le_iff₀ hN).mp ht
  have hNη : N*(‖x‖-t) ≤ η := by
    have hb := (le_div_iff₀ hN).mp (show ‖x‖-t ≤ min η 1/N by linarith)
    nlinarith [min_le_left η 1]
  have hl := h N hN t x (by nlinarith) (by rw [abs_of_nonneg (mul_nonneg hN.le (sub_nonneg.mpr hr))]; exact hNη)
  have hηt : min η 1/N ≤ t := by
    apply (div_le_iff₀ hN).2
    nlinarith [min_le_right η 1]
  have hr2 : ‖x‖ ≤ 2*t := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (htpos.trans_le hr) hr2 (neg_nonpos.mpr hm)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) htpos.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hk.le (Real.rpow_nonneg hN.le ((n:ℝ)-radialOrder n)))
  apply le_trans ?_ hl
  convert hh using 1 ; ring

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
