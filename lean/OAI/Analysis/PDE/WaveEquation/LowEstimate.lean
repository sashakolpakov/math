import OAI.Analysis.Fourier.WavePackets.WaveDataLowTime
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyCore
import OAI.Analysis.Fourier.SquareFunction.Minkowski

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

open OAI.Analysis.Fourier.LocalSmoothing.Interpolation

def frequencyWavePrimitive {n : ℕ} (χ : Space n → ℂ) (t : ℝ)
    (f : Space n → ℂ) (x : Space n) : ℂ :=
  t • ∫ s in Icc (0:ℝ) 1, (1/2:ℝ) •
    (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (t*s) f x + OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(t*s)) f x)

theorem measurable_frequencyWavePrimitive {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (f : SchwartzMap (Space n) ℂ) :
    Measurable (fun z : Space n × ℝ ↦ frequencyWavePrimitive χ z.2 f z.1) := by
  have hF := OAI.Analysis.Fourier.LocalSmoothing.continuous_frequencyHalfWave_schwartz hχ hc (show (0:ℝ)<1 by norm_num) f
  have hi : StronglyMeasurable (fun z : (Space n × ℝ) × ℝ ↦ (1/2:ℝ) •
      (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (z.1.2*z.2) f z.1.1 +
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(z.1.2*z.2)) f z.1.1)) := by
    apply Continuous.stronglyMeasurable
    exact ((hF.comp (show Continuous (fun z : (Space n × ℝ) × ℝ ↦
      (z.1.1,z.1.2*z.2)) by fun_prop)).add
        (hF.comp (show Continuous (fun z : (Space n × ℝ) × ℝ ↦
          (z.1.1,-(z.1.2*z.2))) by fun_prop))).const_smul (1/2:ℝ)
  exact measurable_snd.smul
    (hi.integral_prod_right' (ν := volume.restrict (Icc (0:ℝ) 1))).measurable

theorem frequencyWavePrimitive_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ, 1 ≤ p →
      eLpNorm (fun z : Space n × ℝ ↦ frequencyWavePrimitive χ z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_fixed_frequency_kernel_compact hχ hc
    (isCompact_Icc (a := (-2:ℝ)) (b := 2))
  refine ⟨4*C,by positivity,fun f p hp ↦ ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hslice (t : ℝ) (ht : t ∈ Icc (-2:ℝ) 2) :
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 t f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
    apply (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequencyWave_slice_young hχ.continuous hc (by norm_num)
      f.continuous.measurable f.integrable t hp1 ENNReal.ofReal_ne_top).trans
    apply mul_le_mul' _ le_rfl
    have he : OAI.Analysis.Fourier.LocalSmoothing.Interpolation.waveKernel χ 1 t = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.WavePackets.waveAmplitude χ 1 t) := by
      funext x
      simpa only [OAI.Analysis.Fourier.LocalSmoothing.Interpolation.waveKernel, one_smul] using
        OAI.Analysis.Fourier.WavePackets.normalized_semiclassicalWaveKernel_eq_angularInverse χ
          (h := 1) (by norm_num) t x
    rw [he]
    exact hb t ht
  apply OAI.Analysis.Fourier.LocalSmoothing.Interpolation.observation_norm_le_of_slices (measurable_frequencyWavePrimitive hχ hc f) (by linarith)
  intro t ht
  let clamp : ℝ → ℝ := fun s ↦ max 0 (min 1 s)
  have hcl (s : ℝ) : clamp s ∈ Icc (0:ℝ) 1 := by
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have htime (s : ℝ) : t * clamp s ∈ Icc (-2:ℝ) 2 ∧ -(t*clamp s) ∈ Icc (-2:ℝ) 2 := by
    have hs := hcl s
    constructor <;> constructor <;> nlinarith [ht.1,ht.2,hs.1,hs.2]
  let F : Space n × ℝ → ℂ := fun z ↦ (1/2:ℝ) •
    (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (t*clamp z.2) f z.1 +
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(t*clamp z.2)) f z.1)
  have hFc : Continuous F := by
    have hclc : Continuous clamp := by fun_prop
    have hw := OAI.Analysis.Fourier.LocalSmoothing.continuous_frequencyHalfWave_schwartz hχ hc (show (0:ℝ)<1 by norm_num) f
    exact ((hw.comp (show Continuous (fun z : Space n × ℝ ↦
      (z.1,t*clamp z.2)) by fun_prop)).add
        (hw.comp (show Continuous (fun z : Space n × ℝ ↦
          (z.1,-(t*clamp z.2))) by fun_prop))).const_smul (1/2:ℝ)
  let I : Space n → ℂ := fun x ↦ ∫ s in Icc (0:ℝ) 1,F (x,s)
  have hIm : Measurable I :=
    (hFc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Icc (0:ℝ) 1))).measurable
  have hI : eLpNorm I (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2*C) * eLpNorm f (ENNReal.ofReal p) volume := by
    have hh := OAI.Analysis.Fourier.SquareFunction.eLpNorm_weighted_integral_domination hFc.measurable
      (κ := fun _ : ℝ ↦ (1:ℝ≥0∞)) measurable_const hIm.aestronglyMeasurable hp
      (B := ENNReal.ofReal (2*C) * eLpNorm f (ENNReal.ofReal p) volume)
      (μ := (volume : Measure (Space n))) (T := I)
      (ν := volume.restrict (Icc (0:ℝ) 1))
    refine (hh ?_ ?_).trans_eq ?_
    · intro s
      change eLpNorm ((1/2:ℝ) • (fun x : Space n ↦
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (t*clamp s) f x +
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(t*clamp s)) f x)) _ _ ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤1/2)]
      calc
        _ ≤ eLpNorm (fun x : Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (t*clamp s) f x +
            OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(t*clamp s)) f x) (ENNReal.ofReal p) volume :=
          (mul_le_mul' (by norm_num : ENNReal.ofReal (1/2:ℝ)≤1) le_rfl).trans_eq (one_mul _)
        _ ≤ _ + _ := eLpNorm_add_le hp1
        _ ≤ _ := (add_le_add (hslice _ (htime s).1) (hslice _ (htime s).2)).trans_eq (by
          rw [← add_mul, ← ENNReal.ofReal_add hC.le hC.le]
          congr 2
          ring)
    · intro x
      simpa only [one_mul] using enorm_integral_le_lintegral_enorm (fun s ↦ F (x,s))
    · norm_num [Real.volume_Icc]
  have he : frequencyWavePrimitive χ t f = t • I := by
    funext x
    dsimp only [frequencyWavePrimitive, Pi.smul_apply, I]
    apply congrArg (fun v : ℂ ↦ t • v)
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    have hh : clamp s = s := by simp only [clamp, min_eq_right hs.2, max_eq_right hs.1]
    simp only [F,hh]
  change eLpNorm (frequencyWavePrimitive χ t f) (ENNReal.ofReal p) volume ≤ _
  rw [he,eLpNorm_const_smul, Real.enorm_eq_ofReal (by linarith [ht.1])]
  calc
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (2*C) * eLpNorm f (ENNReal.ofReal p) volume) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal ht.2) hI
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; congr 2; ring

end OAI.Analysis.PDE.WaveEquation
