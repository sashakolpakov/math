import OAI.Analysis.Fourier.Dispersion.Symbol

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem sqrt_add_sq_sub (m r : ℝ) (hr : 0<r) :
    Real.sqrt (m^2+r^2)-r = m^2 / (Real.sqrt (m^2+r^2)+r) := by
  have hd : Real.sqrt (m^2+r^2)+r ≠ 0 := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ m^2+r^2 by positivity)
  field_simp
  nlinarith

theorem massiveAnnularDifference_scaling {n : ℕ} (m : ℝ) {h : ℝ} (hh : 0<h)
    {ξ : Space n} (hξ : 0<‖ξ‖) :
    h * massiveAnnularDifference m h (h•ξ) = Real.sqrt (m^2+‖ξ‖^2)-‖ξ‖ := by
  have hs : (m*h)^2+‖h•ξ‖^2 = h^2*(m^2+‖ξ‖^2) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
    ring
  have hsqrt : Real.sqrt ((m*h)^2+‖h•ξ‖^2) = h*Real.sqrt (m^2+‖ξ‖^2) := by
    rw [hs,Real.sqrt_mul (sq_nonneg h),Real.sqrt_sq hh.le]
  rw [massiveAnnularDifference,hsqrt,norm_smul,Real.norm_eq_abs,abs_of_pos hh,
    sqrt_add_sq_sub m ‖ξ‖ hξ]
  have hd : Real.sqrt (m^2+‖ξ‖^2)+‖ξ‖ ≠ 0 := by positivity
  field_simp


theorem massiveCorrectionAnnulus_scaling {n : ℕ} (m t : ℝ) {h : ℝ}
    (hh : 0<h) (hh1 : h≤1) (ξ : Space n) :
    (massiveCorrection m t ξ-1)*OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (h•ξ) =
      (h:ℂ)*massiveCorrectionAnnulus m ((t,h),h•ξ) := by
  rw [massiveCorrectionAnnulus_identity]
  by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (h•ξ) = 0
  · simp only [hz,mul_zero,zero_mul]
  have hnorm : 8<‖h•ξ‖ := by
    by_contra! hle
    exact hz (OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff_eq_zero_of_norm_le_eight hle)
  have hξ : 4<‖ξ‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh] at hnorm
    nlinarith [norm_nonneg ξ]
  have hd := massiveAnnularDifference_scaling m hh (show 0<‖ξ‖ by linarith)
  rw [massiveCorrection,regularizedRadius,OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_eq hξ.le,
    Real.sqrt_sq (norm_nonneg ξ),mul_assoc t h,hd]
  ring

theorem massiveCorrection_bound (n : ℕ) (m : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (1:ℝ) 2, ∀ f : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞, 1≤p → p≠⊤ →
      eLpNorm (complexAngularSchwartzMultiplier (massiveCorrection m t) f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  let l : ℝ × Space n → ℂ := fun z ↦ (massiveCorrection m z.1 z.2-1)*OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff z.2
  have hl : ContDiff ℝ ∞ l := ((contDiff_massiveCorrection n m).sub contDiff_const).mul
    ((OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n).comp contDiff_snd)
  have hs : tsupport l ⊆ univ ×ˢ tsupport (@OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff n) := by
    intro z hz
    exact ⟨trivial,tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩
  exact complex_multiplier_bound_of_dyadic_defect (temperate_massiveCorrection n m)
    (contDiff_massiveCorrectionAnnulus n m) hl (tsupport_massiveCorrectionAnnulus n m) hs
    (fun _ _ ↦ rfl) (fun t h hh hh1 ξ ↦ massiveCorrectionAnnulus_scaling m t hh hh1 ξ)

end OAI.Analysis.Fourier.Dispersion
