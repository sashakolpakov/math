import OAI.Analysis.Fourier.Restriction.TwoRadius
import OAI.Analysis.Fourier.Restriction.AnnularNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem measurable_sphericalKernelConvolution {n : ℕ} {K f : Space n → ℂ}
    (hK : Measurable K) (hf : Measurable f) : Measurable (sphericalKernelConvolution K f) := by
  have H : Measurable (fun z : Space n × Space n ↦ K (z.1 - z.2) * f z.2) := by fun_prop
  exact H.stronglyMeasurable.integral_prod_right'.measurable

theorem twoRadius_fourier_norm_bound {n : ℕ} (hn : 1 ≤ n) {K : Space n → ℂ}
    (hKm : Measurable K) {M : ℝ} (hKb : ∀ x, ‖K x‖ ≤ M)
    (β A B C : ℝ) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hK : ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖(‖x‖ ^ β : ℝ) * K x - (radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (f : Space n → ℂ), Measurable f → Integrable f →
      (∀ y, R < ‖y‖ → f y = 0) → ∀ (p T : ℝ), 1 ≤ p → 2 ≤ T → 2 * R ≤ T → Real.pi / 2 ≤ T →
      ENNReal.ofReal ‖(A : ℂ) - Complex.I * (B : ℂ)‖ *
        (eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) * ENNReal.ofReal T ^ (1 / p)) ≤
      ENNReal.ofReal ((3 * T) ^ β) * (2 * (((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p) *
        eLpNorm (sphericalKernelConvolution K f) (ENNReal.ofReal p) volume)) +
      ENNReal.ofReal (D * (1 + R ^ 2) / T * ∫ y, ‖f y‖) *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ * ENNReal.ofReal T) ^ (1 / p) := by
  obtain ⟨D, hD, hpoint⟩ := twoRadius_fourier_bound hKm hKb β A B C hC hK
  refine ⟨D, hD, ?_⟩
  intro R hR f hfm hfi hfs p T hp hT hRT hpi
  have hT0 : 0 < T := by linarith
  have H := annular_norm_pair_bound (c := ‖(A : ℂ) - Complex.I * (B : ℂ)‖)
    (W := (3 * T) ^ β) (E := D * (1 + R ^ 2) / T * ∫ y, ‖f y‖)
    hn (continuous_angularFourier hfi).measurable
    (measurable_sphericalKernelConvolution hKm hfm) hp (norm_nonneg _)
    (Real.rpow_nonneg (by positivity) β)
    (show 0 ≤ D * (1 + R ^ 2) / T * ∫ y, ‖f y‖ by positivity) hT0
    (show 0 ≤ Real.pi / 2 by positivity) (b := 2 * T) ?_
  · simpa only [show 2 * T - T = T by ring] using H
  intro ω hω t ht
  have ht0 : 0 < t := hT0.trans_le ht.1
  have H := hpoint R hR f hfi hfs ω t hω (hT.trans ht.1) (hRT.trans ht.1)
  apply H.trans
  have htl : t ≤ 3 * T := by linarith [ht.2]
  have htu : t + Real.pi / 2 ≤ 3 * T := by linarith [ht.2]
  have htp : 0 ≤ t + Real.pi / 2 := by positivity
  have h1 := Real.rpow_le_rpow ht0.le htl hβ
  have h2 := Real.rpow_le_rpow htp htu hβ
  have h3 : D * (1 + R ^ 2) / t ≤ D * (1 + R ^ 2) / T :=
    div_le_div_of_nonneg_left (by positivity) hT0 ht.1
  calc
    _ ≤ (3 * T) ^ β * ‖sphericalKernelConvolution K f (t • ω)‖ +
        (3 * T) ^ β * ‖sphericalKernelConvolution K f ((t + Real.pi / 2) • ω)‖ +
        D * (1 + R ^ 2) / T * ∫ y, ‖f y‖ := by gcongr
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
