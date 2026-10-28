import OAI.Analysis.Fourier.BesselPotential.AnnularLogScaling

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace OAI.Analysis.Fourier.BesselPotential

theorem inverse_annular_log_bessel_symbol {n : ℕ} (χ : Space n → ℂ) (s B : ℝ)
    {h : ℝ} (hh : 0 < h) (hone : h ≤ 1) (ξ : Space n) :
    (h^s * annularLogScale h ^ (-B) : ℝ) •
      (annularLogSobolevSymbol χ s B (annularLogParameter h,h • ξ) *
        (((1+‖ξ‖^2)^(s/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B : ℝ) •
          (1 : ℂ))) = χ (h • ξ) := by
  have hr : 0 < 1+‖ξ‖^2 := by positivity
  have hl : 0 < Real.log (2+Real.sqrt (1+‖ξ‖^2)) :=
    Real.log_pos (by linarith [Real.sqrt_nonneg (1+‖ξ‖^2)])
  have hL : 0 < annularLogScale h :=
    lt_of_lt_of_le zero_lt_one (annularLogScale_one_le hh hone)
  have hpow : (h^2 : ℝ)^(-s/2) = h^(-s) := by
    rw [← Real.rpow_natCast_mul hh.le]
    congr 1
    ring
  have h₁ : (h^s : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hh s).ne'
  have h₂ : ((1+‖ξ‖^2)^(s/2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h₃ : (Real.log (2+Real.sqrt (1+‖ξ‖^2))^B : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hl B).ne'
  have h₄ : (annularLogScale h ^ B : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL B).ne'
  rw [annularLogSobolevSymbol,annularLogParameter_radial hh,
    annularLogBlend_scaling hh hone,Real.mul_rpow (sq_nonneg h) hr.le,hpow,
    Real.div_rpow hl.le hL.le,show -s/2 = -(s/2) by ring]
  simp only [Real.rpow_neg hh.le,Real.rpow_neg hr.le,Real.rpow_neg hl.le,
    Real.rpow_neg hL.le,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_inv,mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr h₁,Complex.ofReal_ne_zero.mpr h₂,
    Complex.ofReal_ne_zero.mpr h₃,Complex.ofReal_ne_zero.mpr h₄]

theorem frequencyHalfWave_eq_inverse_log_bessel {n : ℕ} (χ : Space n → ℂ) (s B : ℝ)
    {h : ℝ} (hh : 0 < h) (hone : h ≤ 1) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f x = (h^s * annularLogScale h^(-B)) •
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ => annularLogSobolevSymbol χ s B (annularLogParameter h,ξ))
        h 0 (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave,zero_mul,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_mul]
  rw [← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real]
  congr 1
  funext ξ
  rw [angularFourier_logBesselPotential]
  have hc := inverse_annular_log_bessel_symbol χ s B hh hone ξ
  simp only [Complex.real_smul,mul_one] at hc ⊢
  calc
    χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ =
      ((h^s * annularLogScale h^(-B) : ℝ) : ℂ) *
        (annularLogSobolevSymbol χ s B (annularLogParameter h,h • ξ) *
          (((1+‖ξ‖^2)^(s/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B : ℝ) : ℂ)) *
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by rw [hc]
    _ = _ := by ring

/-- Uniform inverse log-Bessel estimate on high-frequency annuli. -/
theorem annularProject_inverse_log_bessel_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (haway : ∀ ξ ∈ tsupport χ, 1 < ‖ξ‖) (s B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) p volume ≤
        ENNReal.ofReal (C*h^s*(1+Real.log (1/h))^(-B)) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume := by
  obtain ⟨C,hC,hbound⟩ := annularLogSobolevSymbol_uniform_bound hχ hc haway s B
  refine ⟨C,hC,?_⟩
  intro h hh hone f p hp hptop
  have hint : Integrable (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) := by
    rw [← logBesselPotentialSchwartz_eq]
    exact (logBesselPotentialSchwartz s B f).integrable
  have heq : (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f : Space n → ℂ) =
      (h^s * annularLogScale h^(-B)) •
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ => annularLogSobolevSymbol χ s B (annularLogParameter h,ξ))
          h 0 (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) := by
    funext x
    rw [OAI.Analysis.Fourier.BochnerRiesz.annularProject_eq_frequencyHalfWave hχ hc hh]
    exact frequencyHalfWave_eq_inverse_log_bessel χ s B hh hone f x
  have hn : 0 ≤ h^s * annularLogScale h^(-B) := mul_nonneg
    (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg (by linarith [annularLogScale_one_le hh hone]) _)
  rw [heq,eLpNorm_const_smul,Real.enorm_eq_ofReal hn]
  calc
    _ ≤ ENNReal.ofReal (h^s * annularLogScale h^(-B)) *
        (ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume) :=
      mul_le_mul' le_rfl (hbound _ (annularLogParameter_mem hh hone) h hh _ hint p hp hptop)
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hn]
      congr 2
      unfold annularLogScale
      ring

theorem norm_gt_one_of_mem_tsupport_vanishing_two {n : ℕ} {χ : Space n → ℂ}
    (hsmall : ∀ ξ, ‖ξ‖ ≤ 2 → χ ξ = 0) {ξ : Space n} (hξ : ξ ∈ tsupport χ) :
    1 < ‖ξ‖ := by
  by_contra! hn
  have hnear : ∀ᶠ η in 𝓝 ξ, ‖η‖ < 2 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖ξ‖ < 2 by linarith)
  have hzero : χ =ᶠ[𝓝 ξ] 0 := hnear.mono fun η hη => hsmall η hη.le
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hξ

theorem annularProject_inverse_log_bessel_bound_of_vanishing {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsmall : ∀ ξ, ‖ξ‖ ≤ 2 → χ ξ = 0) (s B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) p volume ≤
        ENNReal.ofReal (C*h^s*(1+Real.log (1/h))^(-B)) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume :=
  annularProject_inverse_log_bessel_bound hχ hc
    (fun _ hξ => norm_gt_one_of_mem_tsupport_vanishing_two hsmall hξ) s B

end OAI.Analysis.Fourier.BesselPotential
