import OAI.Analysis.Fourier.BochnerRiesz.PacketNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The local-smoothing proof bounds the smooth interior partial sums
uniformly, before taking their limit. -/
theorem localSmoothing_brInteriorCycles_uniform (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p) (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ J : ℕ, 2 ≤ J ∧ ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (brInteriorCycles δ (J + N) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (le_max_left _ _) hδ
  let ε : ℝ := (δ - OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε < δ := by dsimp [ε]; linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  obtain ⟨χ, hχ, hc, hzero, hone, _⟩ := exists_annular_cutoff (n := n)
    (a := 1 / 4) (b := 1 / 2) (c := 2) (d := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, L, hL, hmax⟩ := localSmoothing_maximalShellCycles hls hn
    (dyadicPowerProfile δ) (hasCompactSupport_dyadicPowerProfile δ) hp hε
  obtain ⟨J₀, hJ₀⟩ := pow_unbounded_of_one_lt L (by norm_num : (1 : ℝ) < 2)
  let J : ℕ := J₀ + 2
  have hJ : 2 ≤ J := by dsimp [J]; omega
  have hlarge (j : ℕ) : L ≤ (2 : ℝ) ^ (J + j) := by
    exact hJ₀.le.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [J]; omega))
  obtain ⟨K, hK, hkernel⟩ := exists_angularInverse_kernel_bound
    (contDiff_brExteriorSymbol δ hχ hzero) (hasCompactSupport_brExteriorSymbol δ hc)
  obtain ⟨B, hB, hinterior⟩ := exists_angularInverse_kernel_bound
    (contDiff_brInteriorSymbol hδ0 hJ) (hasCompactSupport_brInteriorSymbol hδ0 J)
  let G : ℝ := (1 - (2 : ℝ) ^ ((OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) - δ))⁻¹
  have hG : 0 < G := dyadic_rpow_sum_constant_pos hgap
  refine ⟨J, hJ, B + (K * C₀) * G, by positivity, ?_⟩
  intro N f
  rw [brInteriorCycles_finite_partition hδ0 hJ hχ hc hzero hone N f]
  apply finite_dyadic_eLpNorm_bound volume (brInteriorCycles δ J f)
    (fun j x ↦ Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) * brShellPacket δ χ (J + j) f x)
    hp1 (mul_nonneg hK.le hC₀.le) hB.le hgap J N (eLpNorm f (ENNReal.ofReal p) volume)
  · exact (eLpNorm_brInteriorCycles_le hδ0 hJ f hp1 ENNReal.ofReal_ne_top).trans
      (mul_le_mul' hinterior le_rfl)
  · intro j
    exact eLpNorm_weighted_brShellPacket_le hχ hc hzero hK.le hC₀.le hkernel
      (J + j) f hp1 ENNReal.ofReal_ne_top (hmax _ (hlarge j) f).2

end OAI.Analysis.Fourier.BochnerRiesz
