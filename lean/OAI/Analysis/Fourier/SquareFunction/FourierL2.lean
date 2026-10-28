import OAI.Analysis.Fourier.Wave.Compatibility

open _root_.MeasureTheory FourierTransform
open scoped ContDiff ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

abbrev LineL2 := Lp (α := ℝ) ℂ 2

private theorem fourier_line_pairing (g : ℝ → ℂ) (hg : Integrable g)
    (φ : SchwartzMap ℝ ℂ) :
    (∫ ξ, (𝓕 φ) ξ * g ξ) = ∫ x, φ x * (𝓕 g) x := by
  have hL : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext
    simp []
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner φ.integrable hg
  rw [hL] at h
  have hφ (ξ : ℝ) : (𝓕 φ) ξ = (𝓕 (φ : ℝ → ℂ)) ξ :=
    congrFun (SchwartzMap.fourier_coe φ) ξ
  simp_rw [hφ]
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ ℝ) φ ξ * g ξ) =
    ∫ x, φ x * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x
  simpa only [smul_eq_mul] using h

private theorem fourier_lineL2_pairing (g : LineL2) (φ : SchwartzMap ℝ ℂ) :
    (∫ x, φ x * ((Lp.fourierTransformₗᵢ ℝ ℂ) g) x) = ∫ ξ, (𝓕 φ) ξ * g ξ := by
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq g)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at h
  exact h.symm

/-- On the radius line the ordinary Fourier integral agrees with the unitary
`L²` transform on their common domain. -/
theorem fourier_lineL2_coe (g : LineL2) (hg : Integrable (g : ℝ → ℂ)) :
    (fun x => ((Lp.fourierTransformₗᵢ ℝ ℂ) g) x) =ᵐ[volume] 𝓕 (g : ℝ → ℂ) := by
  have hc : Continuous (𝓕 (g : ℝ → ℂ)) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransform _).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ ℝ ℂ) g)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro ψ hψ hsψ
  have hsc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hsψ.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ := hsc.toSchwartzMap hdiff
  have h := (fourier_lineL2_pairing g φ).trans (fourier_line_pairing g hg φ)
  simpa [φ, Complex.real_smul] using h

/-- Classical one-dimensional Plancherel in extended-norm form. -/
theorem eLpNorm_fourier_line {g : ℝ → ℂ} (hg : Integrable g) (hg₂ : MemLp g 2) :
    eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume := by
  let g₂ : LineL2 := hg₂.toLp g
  have hcoe : (g₂ : ℝ → ℂ) =ᵐ[volume] g := hg₂.coeFn_toLp
  have hfg : (fun x => ((Lp.fourierTransformₗᵢ ℝ ℂ) g₂) x) =ᵐ[volume] 𝓕 g := by
    filter_upwards [fourier_lineL2_coe g₂ (hg.congr hcoe.symm)] with x hx
    exact hx.trans (Real.fourier_congr_ae hcoe x)
  rw [← eLpNorm_congr_ae hfg, ← Lp.enorm_def, ← ofReal_norm,
    LinearIsometryEquiv.norm_map, ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae hcoe]

end OAI.Analysis.Fourier.SquareFunction
