import OAI.Analysis.Fourier.Restriction.Amplitude
import OAI.Analysis.Fourier.Wave.AngularTransform

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter FourierTransform
open scoped ENNReal BigOperators Topology RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem angularFourier_const_mul {n : ℕ} (c : ℂ) (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ c * f x) ξ = c * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem angularFourier_congr_ae {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᵐ[volume] g) (ξ : Space n) : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [hx]

theorem angularFourier_integrand_integrable {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) (ξ : Space n) :
    Integrable (fun x ↦ Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f x) := by
  have hm : AEStronglyMeasurable
      (fun x : Space n ↦ Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) volume :=
    (show Continuous (fun x : Space n ↦
      Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) by fun_prop).aestronglyMeasurable
  apply hf.norm.mono' (hm.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp [Complex.norm_exp]

theorem angularFourier_add {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f x + g x) ξ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ + OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  simp_rw [mul_add]
  exact integral_add (angularFourier_integrand_integrable hf ξ)
    (angularFourier_integrand_integrable hg ξ)

theorem angularFourier_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Space n → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (f i) ξ := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun i hi ↦ angularFourier_integrand_integrable (hf i hi) ξ)

theorem angularFourier_eq_scaled {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = 𝓕 f ((2 * Real.pi)⁻¹ • ξ) := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simpa only [smul_smul, mul_inv_cancel₀ hπ, one_smul] using
    OAI.Analysis.Fourier.Wave.angularFourier_scaled f ((2 * Real.pi)⁻¹ • ξ)

theorem continuous_angularFourier {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) : Continuous (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) := by
  have hF : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  convert hF.comp (show Continuous (fun ξ : Space n ↦ (2 * Real.pi)⁻¹ • ξ) by fun_prop) using 1
  funext ξ
  exact angularFourier_eq_scaled f ξ

theorem tendsto_angularFourier_amplitudeBand {n : ℕ} {f : Space n → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (ξ : Space n) :
    Tendsto (fun N : ℕ ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier
      (amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N)) ξ)
      atTop (𝓝 (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
  · intro N
    exact (angularFourier_integrand_integrable
      (integrable_amplitudeBand hf hfi _ _) ξ).aestronglyMeasurable
  · exact hfi.norm
  · intro N
    filter_upwards [] with x
    simpa [norm_mul, Complex.norm_exp] using
      norm_amplitudeBand_le f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N) x
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul (tendsto_amplitudeBand f x)

end OAI.Analysis.Fourier.Restriction
