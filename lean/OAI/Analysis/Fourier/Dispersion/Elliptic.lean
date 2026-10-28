import OAI.Analysis.Fourier.Dispersion.Synthesis
import OAI.Analysis.Fourier.Dispersion.Linear
import OAI.Analysis.Fourier.Dispersion.Quadratic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

def linearMassDispersion {n : ℕ} (R : Space n ≃L[ℝ] Space n) (m : ℝ) (ξ : Space n) : ℝ :=
  Real.sqrt (m^2+‖R ξ‖^2)

theorem continuous_linearMassDispersion {n : ℕ} (R : Space n ≃L[ℝ] Space n) (m : ℝ) :
    Continuous (linearMassDispersion R m) := by unfold linearMassDispersion; fun_prop

theorem compact_cutoff_comp_linearEquiv {n : ℕ} (R : Space n ≃L[ℝ] Space n)
    {χ : Space n → ℂ} (hc : HasCompactSupport χ) : HasCompactSupport (χ ∘ R.symm) := by
  apply (hc.image R.continuous).of_isClosed_subset (isClosed_tsupport _)
  intro ξ hξ
  exact ⟨R.symm ξ,tsupport_comp_subset_preimage χ R.symm.continuous hξ,R.apply_symm_apply ξ⟩

theorem linearMassDispersion_uniform_kernel {n : ℕ}
    (R : Space n ≃L[ℝ] Space n) (m : ℝ) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ,0<C ∧ ∀ t∈Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦
        Complex.exp (-Complex.I*(t*linearMassDispersion R m ξ:ℝ))*χ ξ)) 1 volume ≤ ENNReal.ofReal C := by
  by_cases hm : m=0
  · subst m
    let φ : Space n → ℂ := χ ∘ R.symm
    have hφ : ContDiff ℝ ∞ φ := hχ.comp R.symm.contDiff
    have hcφ : HasCompactSupport φ := compact_cutoff_comp_linearEquiv R hc
    obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_fixed_frequency_kernel_compact hφ hcφ
      (isCompact_Icc (a := (1:ℝ)) (b := 2))
    refine ⟨C,hC,fun t ht ↦ ?_⟩
    have he : (fun ξ ↦ Complex.exp (-Complex.I*(t*linearMassDispersion R 0 ξ:ℝ))*χ ξ) =
        OAI.Analysis.Fourier.WavePackets.waveAmplitude φ 1 t ∘ R := by
      funext ξ
      simp only [linearMassDispersion,zero_pow (by omega : 2≠0),zero_add,
        Real.sqrt_sq (norm_nonneg _),Function.comp_apply,OAI.Analysis.Fourier.WavePackets.waveAmplitude,div_one,
        φ,R.symm_apply_apply]
    rw [he,eLpNorm_angularInverse_comp_linearEquiv R _
      (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse (OAI.Analysis.Fourier.WavePackets.waveAmplitude_integrable
        hφ.continuous hcφ 1 t)).measurable]
    exact hb t ht
  · apply smoothDispersion_uniform_kernel ?_ hχ hc
    unfold linearMassDispersion
    exact (contDiff_const.add (ContDiff.norm_sq (𝕜 := ℝ) R.contDiff)).sqrt
      (fun ξ ↦ by positivity)

theorem linearMassDispersion_frequency_bound (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2≤n) (R : Space n ≃L[ℝ] Space n) (m : ℝ)
    {p : ℝ} (hp : 2≤p) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hz : 0∉tsupport χ) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyDispersion (linearMassDispersion R m) χ h z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5))*
        eLpNorm f (ENNReal.ofReal p) volume := by
  let φ : Space n → ℂ := χ ∘ R.symm
  have hφ : ContDiff ℝ ∞ φ := hχ.comp R.symm.contDiff
  have hcφ : HasCompactSupport φ := compact_cutoff_comp_linearEquiv R hc
  have hzφ : 0∉tsupport φ := by
    intro h
    have H := tsupport_comp_subset_preimage χ R.symm.continuous h
    exact hz (by simpa only [mem_preimage,map_zero] using H)
  obtain ⟨C,hC,hb⟩ := massive_frequency_bound_of_logarithmicRefinement hlog hn hp m hφ hcφ hzφ
  refine ⟨C,hC,fun h hh h1 f ↦ ?_⟩
  have H := frequencyDispersion_bound_comp_linearEquiv R
    (fun ξ ↦ Real.sqrt (m^2+‖ξ‖^2)) φ h (ENNReal.ofReal p)
      (ENNReal.ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5)))
        (hb h hh h1) f
  have he : φ ∘ R = χ := by funext ξ; simp [φ]
  have hd : (fun ξ : Space n ↦ Real.sqrt (m^2+‖ξ‖^2)) ∘ R =
      linearMassDispersion R m := rfl
  rw [he,hd] at H
  exact H

end OAI.Analysis.Fourier.Dispersion
