import OAI.Analysis.Fourier.Dispersion.Propagator
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyWeights

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

open OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem lowHalfWave_weighted_bound {n : ℕ} {p : ℝ} (hp : 1≤p)
    {w : Space n → ℝ} (hw : w.HasTemperateGrowth) (hw0 : ∀ ξ,w ξ≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (velocityLowData f) z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
  let χ : Space n → ℂ := fun ξ ↦ (OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℂ)
  have hχ := OAI.Analysis.PDE.WaveEquation.contDiff_complex_velocityLowCutoff n
  have hc := OAI.Analysis.PDE.WaveEquation.hasCompactSupport_complex_velocityLowCutoff n
  obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_fixed_frequency_kernel_compact
    (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.contDiff_unweightedCutoff hχ hw hw0) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.hasCompactSupport_unweightedCutoff w hc)
    (isCompact_Icc (a := (1:ℝ)) (b := 2))
  have hk : ∀ t ∈ Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.waveKernel (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w) 1 t) 1 volume ≤ ENNReal.ofReal C := by
    intro t ht
    have he : OAI.Analysis.Fourier.LocalSmoothing.Interpolation.waveKernel (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w) 1 t =
        OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.WavePackets.waveAmplitude (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w) 1 t) := by
      funext x
      simpa only [OAI.Analysis.Fourier.LocalSmoothing.Interpolation.waveKernel,one_smul] using
        OAI.Analysis.Fourier.WavePackets.normalized_semiclassicalWaveKernel_eq_angularInverse
          (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w) (h := 1) (by norm_num) t x
    rw [he]
    exact hb t ht
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.fixedFrequency_weighted_bound_of_kernel hp hχ hc hw hw0 ⟨C,hC,hk⟩
  refine ⟨D,hD,fun f ↦ ?_⟩
  simpa only [halfWave_velocityLowData] using hd f

theorem massiveLow_weighted_bound {n : ℕ} (m : ℝ) (hm : m≠0) {p : ℝ} (hp : 1≤p)
    {w : Space n → ℝ} (hw : w.HasTemperateGrowth) (hw0 : ∀ ξ,w ξ≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 (velocityLowData f) z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
  let χ : Space n → ℂ := fun ξ ↦ (OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℂ)
  let a : ℝ × Space n → ℂ := fun z ↦
    Complex.exp (-Complex.I*(z.1*Real.sqrt (m^2+‖z.2‖^2):ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w z.2
  have hχ := OAI.Analysis.PDE.WaveEquation.contDiff_complex_velocityLowCutoff n
  have hc := OAI.Analysis.PDE.WaveEquation.hasCompactSupport_complex_velocityLowCutoff n
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Space n ↦ Real.sqrt (m^2+‖z.2‖^2)) :=
    (contDiff_const.add (ContDiff.norm_sq (𝕜 := ℝ) contDiff_snd)).sqrt
      (fun z ↦ by positivity)
  have ha : ContDiff ℝ ∞ a :=
    (Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul hs)))).mul
        ((OAI.Analysis.Fourier.LocalSmoothing.Interpolation.contDiff_unweightedCutoff hχ hw hw0).comp contDiff_snd)
  have has : tsupport a ⊆ univ ×ˢ tsupport (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ w) := by
    intro z hz
    exact ⟨trivial,tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩
  obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound
    (K := Icc (1:ℝ) 2) isCompact_Icc (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.hasCompactSupport_unweightedCutoff w hc) ha has
  refine ⟨C+1,by positivity,fun f ↦ ?_⟩
  apply OAI.Analysis.Fourier.LocalSmoothing.Interpolation.observation_norm_le_of_slices (continuous_massiveHalfWave m (velocityLowData f)).measurable
    (by linarith)
  intro t ht
  have he : massiveHalfWave m t (velocityLowData f) =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ a (t,ξ)) 1 0 (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) := by
    funext x
    simp only [massiveHalfWave,dispersionIntegral,OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave,zero_mul,Complex.ofReal_zero,
      mul_zero,Complex.exp_zero,one_mul,one_smul]
    congr 1
    funext ξ
    simp only [velocityLowData,OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (OAI.Analysis.PDE.WaveEquation.temperate_velocityLowCutoff n),
      OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hw,a,OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff,χ,Complex.real_smul,
      Complex.ofReal_inv]
    have hne : (w ξ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw0 ξ)
    field_simp
  change eLpNorm (massiveHalfWave m t (velocityLowData f)) _ _ ≤ _
  rw [he]
  exact (hb t ht 1 (by norm_num) (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f)
    (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f).integrable _
    (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : C≤C+1)) le_rfl)

end OAI.Analysis.Fourier.Dispersion
