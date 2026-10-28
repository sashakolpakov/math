import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowFamily

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

def lowWaveAnnulus {n : ℕ} (b χ : Space n → ℂ) (r T : ℝ) (ξ : Space n) : ℂ :=
  b (r⁻¹ • ξ) * χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ)) - 1)

theorem lowWaveAnnulus_eq_dilate {n : ℕ} (b χ : Space n → ℂ)
    {r : ℝ} (hr : 0 < r) (T : ℝ) :
    lowWaveAnnulus b χ r T = fun ξ => r • lowWaveFamily b χ ((T,r),r⁻¹ • ξ) := by
  funext ξ
  rw [Complex.real_smul,lowWaveFamily_identity]
  simp only [smul_inv_smul₀ hr.ne',norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr),lowWaveAnnulus]
  congr 3
  field_simp

/-- The small-frequency phase remainder gains one complete dyadic scale. -/
theorem uniform_lowWaveAnnulus_kernel {n : ℕ} {b χ : Space n → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hz : 0 ∉ tsupport b)
    (hχ : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowWaveAnnulus b χ r T)) 1 volume ≤ ENNReal.ofReal (r*C) := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1
    (isCompact_Icc.prod isCompact_Icc) hc (contDiff_lowWaveFamily hb hχ hz)
    (lowWaveFamily_support b χ)
  refine ⟨C,hC,?_⟩
  intro r hr hr1 T hT
  have hi : Integrable (fun ξ => lowWaveFamily b χ ((T,r),ξ)) := by
    apply ((contDiff_lowWaveFamily hb hχ hz).continuous.comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact ((lowWaveFamily_support b χ) (tsupport_comp_subset_preimage _
      (continuous_const.prodMk continuous_id) hξ)).2
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowWaveAnnulus b χ r T) = fun x =>
      r • OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ)) x := by
    rw [lowWaveAnnulus_eq_dilate b χ hr T]
    exact funext (OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real r _)
  rw [he]
  change eLpNorm (r • (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ))))
    1 volume ≤ _
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hr.le,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one hi (inv_pos.mpr hr),
    ENNReal.ofReal_mul hr.le]
  exact mul_le_mul' le_rfl (hbound (T,r) ⟨hT,hr.le,hr1⟩).2

end OAI.Analysis.Fourier.WavePackets
