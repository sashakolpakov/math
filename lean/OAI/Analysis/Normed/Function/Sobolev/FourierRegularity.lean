import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

/-- Fourier inversion almost everywhere for L¹ ∩ L² data whose classical
Fourier transform is integrable. No continuity of the input is assumed. -/
theorem ae_fourierInv_fourier {d : ℕ} {f : Space d → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (hF : Integrable (𝓕 f)) :
    f =ᵐ[volume] 𝓕⁻ (𝓕 f) := by
  let u : OAI.Analysis.Fourier.Wave.WaveL2 d := hf₂.toLp f
  let F : OAI.Analysis.Fourier.Wave.WaveL2 d := (Lp.fourierTransformₗᵢ (Space d) ℂ) u
  have hFAE : (F : Space d → ℂ) =ᵐ[volume] 𝓕 f :=
    OAI.Analysis.Fourier.BochnerRiesz.fourier_toLp_ae hf hf₂
  have hFi : Integrable (F : Space d → ℂ) := hF.congr hFAE.symm
  have hInv := OAI.Analysis.Fourier.Wave.inverseFourierL2_coe F hFi
  have hInv' : (u : Space d → ℂ) =ᵐ[volume] 𝓕⁻ (F : Space d → ℂ) := by
    simpa only [F, LinearIsometryEquiv.symm_apply_apply] using hInv
  exact hf₂.coeFn_toLp.symm.trans (hInv'.trans
    (Eventually.of_forall fun x ↦ Real.fourierInv_congr_ae hFAE x))

/-- Integrable Fourier moments produce an actual smooth representative
of L¹ ∩ L² data, not a regularity assumption on the chosen representative. -/
theorem exists_contDiff_representative_of_fourier_moments {d : ℕ} {N : ℕ∞}
    {f : Space d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    (hF : ∀ k : ℕ, k ≤ N → Integrable (fun ξ ↦ ‖ξ‖ ^ k * ‖𝓕 f ξ‖)) :
    ∃ g : Space d → ℂ, ContDiff ℝ N g ∧ f =ᵐ[volume] g := by
  refine ⟨𝓕⁻ (𝓕 f), ?_, ?_⟩
  · have hc : ContDiff ℝ N (𝓕 (𝓕 f)) := Real.contDiff_fourier hF
    have heq : 𝓕⁻ (𝓕 f) = fun x ↦ 𝓕 (𝓕 f) (-x) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ _
    rw [heq]
    exact hc.comp contDiff_neg
  · have hFi : Integrable (𝓕 f) := by
      apply (integrable_norm_iff (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).aestronglyMeasurable).mp
      simpa only [pow_zero, one_mul] using hF 0 (by simp)
    exact ae_fourierInv_fourier hf hf₂ hFi

end OAI.Analysis.Normed.Function.Sobolev
