import OAI.Analysis.Fourier.Dispersion.Dyadic
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyWeights

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

open OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem frequencyDispersion_unweight {n : ℕ} (disp : Space n → ℝ)
    (χ : Space n → ℂ) {w : Space n → ℝ} (hw : w.HasTemperateGrowth)
    (hw0 : ∀ ξ,w ξ≠0) (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    frequencyDispersion disp χ 1 t f = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
      (fun ξ ↦ Complex.exp (-Complex.I*(t*disp ξ:ℝ))*OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w ξ)
      1 0 (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) := by
  funext x
  simp only [frequencyDispersion,OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave,one_smul,zero_mul,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  congr 1
  funext ξ
  simp only [OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hw,OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff,
    Complex.real_smul,Complex.ofReal_inv]
  have hne : (w ξ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw0 ξ)
  field_simp

theorem frequencyDispersion_weighted_bound_of_kernel {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) {p : ℝ} (hp : 1≤p) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {w : Space n → ℝ} (hw : w.HasTemperateGrowth) (hw0 : ∀ ξ,w ξ≠0)
    (hk : ∃ C : ℝ,0<C ∧ ∀ t∈Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦
        Complex.exp (-Complex.I*(t*disp ξ:ℝ))*OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w ξ)) 1 volume ≤ ENNReal.ofReal C) :
    ∃ C : ℝ,0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyDispersion disp χ 1 z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hk⟩ := hk
  refine ⟨C,hC,fun f ↦ ?_⟩
  apply OAI.Analysis.Fourier.LocalSmoothing.Interpolation.observation_norm_le_of_slices
    (continuous_frequencyDispersion hd hχ hc (by norm_num) f).measurable (by linarith)
  intro t ht
  change eLpNorm (frequencyDispersion disp χ 1 t f) _ _ ≤ _
  rw [frequencyDispersion_unweight disp χ hw hw0]
  have ha : Continuous (fun ξ ↦
      Complex.exp (-Complex.I*(t*disp ξ:ℝ))*OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w ξ) := by
    have huc := (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.contDiff_unweightedCutoff hχ hw hw0).continuous
    fun_prop
  have has : HasCompactSupport (fun ξ ↦
      Complex.exp (-Complex.I*(t*disp ξ:ℝ))*OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w ξ) :=
    (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.hasCompactSupport_unweightedCutoff w hc).mul_left
  exact (OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_frequencyHalfWave_zero_le ha has (by norm_num)
    (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f).integrable
    (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top).trans (mul_le_mul' (hk t ht) le_rfl)

theorem smoothDispersion_uniform_kernel {n : ℕ} {disp : Space n → ℝ}
    (hd : ContDiff ℝ ∞ disp) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ,0<C ∧ ∀ t∈Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦
        Complex.exp (-Complex.I*(t*disp ξ:ℝ))*χ ξ)) 1 volume ≤ ENNReal.ofReal C := by
  let a : ℝ × Space n → ℂ := fun z ↦ Complex.exp (-Complex.I*(z.1*disp z.2:ℝ))*χ z.2
  have ha : ContDiff ℝ ∞ a :=
    (Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (hd.comp contDiff_snd))))).mul
      (hχ.comp contDiff_snd)
  have has : tsupport a ⊆ univ ×ˢ tsupport χ := by
    intro z hz
    exact ⟨trivial,tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩
  obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1
    (K := Icc (1:ℝ) 2) isCompact_Icc hc ha has
  exact ⟨C+1,by linarith,fun t ht ↦ (hb t ht).2.trans
    (ENNReal.ofReal_le_ofReal (by linarith))⟩

end OAI.Analysis.Fourier.Dispersion
