import OAI.Analysis.Fourier.BochnerRiesz.CompactInput
import OAI.Analysis.Fourier.BochnerRiesz.UniformConvergence

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


def brDilatedKernel {n : ℕ} (δ R : ℝ) (x : Space n) : ℂ :=
  (R ^ n : ℝ) • OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (R • x)

theorem continuous_brDilatedKernel {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    Continuous (brDilatedKernel (n := n) δ R) := by
  change Continuous (fun x : Space n => (R ^ n : ℝ) • OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (R • x))
  exact ((OAI.Analysis.Fourier.Radial.continuous_bochnerRieszKernel hδ).comp
    ((continuous_const : Continuous (fun _ : Space n => R)).smul continuous_id)).const_smul (R ^ n : ℝ)

theorem bddAbove_norm_brDilatedKernel {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (R : ℝ) : BddAbove (range fun x : Space n => ‖brDilatedKernel δ R x‖) := by
  obtain ⟨C, hC⟩ := bddAbove_norm_bochnerRieszKernel hn hδ
  refine ⟨‖R ^ n‖ * C, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖(R ^ n : ℝ) • OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (R • x)‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC (mem_range_self (R • x))) (norm_nonneg _)

theorem brDilatedKernel_eq_angularInverse {n : ℕ} (δ : ℝ) {R : ℝ} (hR : 0 < R) :
    brDilatedKernel (n := n) δ R =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 (R⁻¹ • ξ) : ℂ)) := by
  ext x
  simpa only [brDilatedKernel, OAI.Analysis.Fourier.Radial.bochnerRieszKernel, inv_pow, inv_inv] using
    (angularInverse_dilate (fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ))
      (inv_pos.mpr hR) x).symm

theorem bochnerRiesz_eq_convolve_brDilatedKernel {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {R : ℝ} (hR : 0 < R) {f : Space n → ℂ} (hf : Integrable f) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f = OAI.Analysis.Fourier.SquareFunction.convolveKernel (brDilatedKernel δ R) f := by
  rw [bochnerRiesz_eq_frequencyHalfWave δ hR f, brDilatedKernel_eq_angularInverse δ hR]
  ext x
  rw [frequencyHalfWave_zero_eq_convolution (φ := fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ))
    (Complex.continuous_ofReal.comp (continuous_bochnerRieszSymbol hδ.le 1))
    (OAI.Analysis.Fourier.Radial.hasCompactSupport_complex_bochnerRieszSymbol_unit hδ) (inv_pos.mpr hR) hf]
  rw [OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
  unfold OAI.Analysis.Fourier.WavePackets.complexConvolution
  congr 1
  ext y
  simp only [smul_eq_mul, mul_comm]

theorem scaled_decay_le {n : ℕ} {β R d b : ℝ} (hβ : (n : ℝ) ≤ β)
    (hR : 1 ≤ R) (hb : 0 < b) (hbd : b ≤ d) :
    R ^ n * (1 + R * d) ^ (-β) ≤ b ^ (-β) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hβ0 : 0 ≤ β := (Nat.cast_nonneg n).trans hβ
  have hRb : 0 < R * b := mul_pos hR0 hb
  have hbase : R * b ≤ 1 + R * d := by nlinarith
  have hpow : (1 + R * d) ^ (-β) ≤ (R * b) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hRb hbase (neg_nonpos.mpr hβ0)
  calc
    _ ≤ R ^ n * (R * b) ^ (-β) := mul_le_mul_of_nonneg_left hpow (pow_nonneg hR0.le _)
    _ = R ^ ((n : ℝ) - β) * b ^ (-β) := by
      rw [Real.mul_rpow hR0.le hb.le, ← Real.rpow_natCast,
        ← mul_assoc, ← Real.rpow_add hR0]
      congr 2
    _ ≤ 1 * b ^ (-β) := mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hR (sub_nonpos.mpr hβ)) (Real.rpow_nonneg hb.le _)
    _ = _ := one_mul _

theorem brDilatedKernel_compact_tail {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ S : ℝ, 0 ≤ S →
      ∀ x y : Space n, 2 * S + 2 < ‖x‖ → ‖y‖ ≤ S →
        ‖brDilatedKernel δ R (x - y)‖ ≤
          C * (1 + ‖x‖) ^ (-(((n : ℝ) + 2 * δ + 1) / 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  let β := ((n : ℝ) + 2 * δ + 1) / 2
  have hβ : (n : ℝ) ≤ β := by dsimp [β]; linarith
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.Radial.bochnerRieszKernel_polynomial_decay hn hd
  refine ⟨C * 3 ^ β, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro R hR S hS x y hx hy
  have hb0 : 0 < (1 + ‖x‖) / 3 := by positivity
  have hxy : (1 + ‖x‖) / 3 ≤ ‖x - y‖ := by
    have H := norm_le_norm_sub_add x y
    linarith
  have H := scaled_decay_le hβ hR hb0 hxy
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  calc
    ‖brDilatedKernel δ R (x - y)‖ = R ^ n * ‖OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (R • (x - y))‖ := by
      rw [brDilatedKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR0 _)]
    _ ≤ R ^ n * (C * (1 + R * ‖x - y‖) ^ (-β)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hR0.le _)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR0, β, neg_div] using hb (R • (x - y))
    _ = C * (R ^ n * (1 + R * ‖x - y‖) ^ (-β)) := by ring
    _ ≤ C * (((1 + ‖x‖) / 3) ^ (-β)) := mul_le_mul_of_nonneg_left H hC.le
    _ = (C * 3 ^ β) * (1 + ‖x‖) ^ (-β) := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      simp only [div_inv_eq_mul]
      ring

end OAI.Analysis.Fourier.BochnerRiesz
