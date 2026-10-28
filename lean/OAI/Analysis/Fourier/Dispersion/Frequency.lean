import OAI.Analysis.Fourier.Dispersion.Massive
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem angularSchwartzMultiplier_one {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier (fun _ : Space n ↦ (1:ℝ)) f = f := by
  ext x
  rw [OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier_eq_integral (Function.HasTemperateGrowth.const 1)]
  simpa only [one_smul] using OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x

theorem massive_bound_by_halfWave_and_input {n : ℕ} (m : ℝ) {p : ℝ} (hp : 1≤p) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C *
        (eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) + eLpNorm f (ENNReal.ofReal p) volume) := by
  by_cases hm : m=0
  · refine ⟨1,by norm_num,fun f ↦ ?_⟩
    simp only [hm,massiveHalfWave_zero,ENNReal.ofReal_one,one_mul]
    exact le_add_right le_rfl
  obtain ⟨L,hL,hl⟩ := lowHalfWave_weighted_bound hp
    (Function.HasTemperateGrowth.const (1:ℝ)) (fun _ : Space n ↦ one_ne_zero)
  obtain ⟨D,hD,hd⟩ := massiveLow_weighted_bound m hm hp
    (Function.HasTemperateGrowth.const (1:ℝ)) (fun _ : Space n ↦ one_ne_zero)
  simp only [angularSchwartzMultiplier_one] at hl hd
  obtain ⟨C,hC,hc⟩ := massiveCorrection_bound n m
  refine ⟨C+(C*L+D),by positivity,fun f ↦ ?_⟩
  have hp1 : 1≤ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let u : Space n × ℝ → ℂ := fun z ↦ massiveHalfWave m z.2 f z.1 -
    massiveHalfWave m z.2 (velocityLowData f) z.1
  let v : Space n × ℝ → ℂ := fun z ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1 -
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (velocityLowData f) z.1
  have hum : Measurable u := ((continuous_massiveHalfWave m f).sub
    (continuous_massiveHalfWave m (velocityLowData f))).measurable
  have hvm : Measurable v := ((OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).sub
    (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral (velocityLowData f))).measurable
  have huv : eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
    apply eLpNorm_observation_le_mul_of_slices hum hvm (by linarith) hC.le
    intro t ht
    have he : (fun x ↦ u (x,t)) =
        complexAngularSchwartzMultiplier (massiveCorrection m t) (smoothHighWave t f) := by
      funext x
      exact (massiveCorrection_high_eq_sub m t f x).symm
    have hv : (fun x ↦ v (x,t)) = smoothHighWave t f := by
      funext x
      exact (smoothHighWave_eq_sub t f x).symm
    rw [he,hv]
    exact hc t ht (smoothHighWave t f) _ hp1 ENNReal.ofReal_ne_top
  have hvb : eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) + ENNReal.ofReal L * eLpNorm f (ENNReal.ofReal p) volume :=
    (eLpNorm_sub_le hp1).trans (add_le_add le_rfl (hl f))
  have he : (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1) =
      fun z ↦ u z + massiveHalfWave m z.2 (velocityLowData f) z.1 := by
    funext z
    dsimp only [u]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) +
        eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 (velocityLowData f) z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal C * (eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) + ENNReal.ofReal L * eLpNorm f (ENNReal.ofReal p) volume) +
        ENNReal.ofReal D * eLpNorm f (ENNReal.ofReal p) volume :=
      add_le_add (huv.trans (mul_le_mul' le_rfl hvb)) (hd f)
    _ = ENNReal.ofReal C * eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) +
        ENNReal.ofReal (C*L+D) * eLpNorm f (ENNReal.ofReal p) volume := by
      rw [mul_add,add_assoc,← mul_assoc,← ENNReal.ofReal_mul hC.le,← add_mul,
        ← ENNReal.ofReal_add (mul_nonneg hC.le hL.le) hD.le]
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith : C≤C+(C*L+D))) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : C*L+D≤C+(C*L+D))) le_rfl)

def frequencyDispersion {n : ℕ} (disp : Space n → ℝ) (φ : Space n → ℂ) (h t : ℝ)
    (f : Space n → ℂ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ Complex.exp (-Complex.I*(t*disp ξ:ℝ))*φ (h•ξ)*OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x

theorem frequencyDispersion_eq_project {n : ℕ} (disp : Space n → ℝ) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0<h)
    (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyDispersion disp φ h t f x = dispersionIntegral disp t (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) x := by
  simp only [frequencyDispersion,dispersionIntegral,
    OAI.Analysis.Fourier.BochnerRiesz.angularFourier_annularProject hφ hc hh,mul_assoc]

theorem massive_frequency_bound_of_logarithmicRefinement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2≤n) {p : ℝ} (hp : 2≤p) (m : ℝ)
    {φ : Space n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hz : 0∉tsupport φ) :
    ∃ C : ℝ, 0<C ∧ ∀ h : ℝ, 0<h → h≤1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion (fun ξ ↦ Real.sqrt (m^2+‖ξ‖^2)) φ h z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A,hA,ha⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequency_bound_of_logarithmicRefinement
    hlog hn hp hφ hc hz
  obtain ⟨C,hC,hc'⟩ := massive_bound_by_halfWave_and_input (n := n) m (show 1≤p by linarith)
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.BochnerRiesz.annularProject_uniform_bound hφ hc
  refine ⟨C*(A+D),by positivity,fun h hh h1 f ↦ ?_⟩
  have hp1 : 1≤ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1≤p by linarith)
  let W : ℝ := h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5)
  have hW : 1≤W := by
    apply one_le_mul_of_one_le_of_one_le
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh h1
      exact neg_nonpos.mpr (le_max_left _ _)
    · apply one_le_pow₀
      have hl : 0≤Real.log (1/h) := Real.log_nonneg (by exact (one_le_div hh).mpr h1)
      linarith
  have H := hc' (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f)
  have hF := (ha h hh h1 f).2
  simp only [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral_projected hφ hc hh] at H
  have hi := hd h hh f (ENNReal.ofReal p) hp1 ENNReal.ofReal_ne_top
  have hD0 : 0≤D := hD.le
  have hAW : 0≤A*W := mul_nonneg hA.le (le_trans zero_le_one hW)
  calc
    _ ≤ ENNReal.ofReal C *
        (eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) +
         eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) (ENNReal.ofReal p) volume) := by
      simpa only [frequencyDispersion_eq_project _ hφ hc hh, massiveHalfWave] using H
    _ ≤ ENNReal.ofReal C *
        (ENNReal.ofReal (A*W)*eLpNorm f (ENNReal.ofReal p) volume +
         ENNReal.ofReal (D*W)*eLpNorm f (ENNReal.ofReal p) volume) := by
      apply mul_le_mul' le_rfl
      apply add_le_add
      · simpa only [W,mul_assoc] using hF
      · exact hi.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl)
    _ = _ := by
      rw [← add_mul,← ENNReal.ofReal_add hAW (mul_nonneg hD0 (by linarith)),
        ← mul_assoc,← ENNReal.ofReal_mul hC.le]
      congr 2
      dsimp only [W]
      ring

end OAI.Analysis.Fourier.Dispersion
