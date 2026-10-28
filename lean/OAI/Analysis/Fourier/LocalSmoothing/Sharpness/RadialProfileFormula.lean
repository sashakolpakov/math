import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialFormula
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ProfileDecay

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

def radialVolumeWeight (n : ℕ) (σ : ℝ) : ℝ := σ^(n-1)*radialBump σ

theorem radialVolumeWeight_eq (n : ℕ) :
    radialVolumeWeight n = weightedRadialBump ((n-1:ℕ):ℝ) := by
  ext σ
  simp only [radialVolumeWeight,weightedRadialBump,Real.rpow_natCast]

theorem radialVolumeWeight_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (radialVolumeWeight n) := by
  rw [radialVolumeWeight_eq]
  exact weightedRadialBump_contDiff _

theorem radialVolumeWeight_hasCompactSupport (n : ℕ) :
    HasCompactSupport (radialVolumeWeight n) := by
  rw [radialVolumeWeight_eq]
  exact weightedRadialBump_hasCompactSupport _

theorem radialVolumeWeight_integrable (n : ℕ) : Integrable (radialVolumeWeight n) :=
  (radialVolumeWeight_contDiff n).continuous.integrable_of_hasCompactSupport
    (radialVolumeWeight_hasCompactSupport n)

/-- Changing the order of radial and angular integration gives an exact
one-dimensional profile representation, used away from the propagation cone. -/
theorem radialWave_eq_sphere_profile (n : ℕ) (t : ℝ) (x : Space n) :
    radialWave n t x = ∫ v, radialProfile (radialVolumeWeight n) (inner ℝ x v-t)
      ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  let H : ℝ × Space n → ℂ := fun z =>
    phase ((inner ℝ x z.2-t)*z.1) * (radialVolumeWeight n z.1 : ℂ)
  have hH : Integrable H (volume.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
    apply ((radialVolumeWeight_integrable n).norm.mul_prod
      (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1:ℝ))).mono'
    · have hg := (radialVolumeWeight_contDiff n).continuous
      have hcont : Continuous H := by unfold H phase; fun_prop
      exact hcont.aestronglyMeasurable
    · exact Eventually.of_forall fun z => by simp [H]
  calc
    radialWave n t x = ∫ σ, ∫ v, H (σ,v) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      unfold radialWave
      apply integral_congr_ae
      filter_upwards [] with σ
      unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      dsimp only [H,radialVolumeWeight]
      change ((σ^(n-1)*radialBump σ:ℝ):ℂ)*phase (-t*σ)*
        (phase (inner ℝ (σ•x) v)*1) = _
      rw [mul_one,real_inner_smul_left,mul_assoc,phase_mul]
      rw [show -t*σ+σ*inner ℝ x v = (inner ℝ x v-t)*σ by ring]
      ring
    _ = ∫ v, ∫ σ, H (σ,v) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      integral_integral_swap hH
    _ = _ := rfl

theorem radialWave_integrable_integrand (n : ℕ) (t : ℝ) (x : Space n) :
    Integrable (fun σ : ℝ => (radialVolumeWeight n σ:ℂ) * phase (-t*σ) *
      OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ•x)) := by
  have hS := OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension
    (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1:ℂ))
  simpa only [Function.comp_def,mul_comm (phase (-t*_) : ℂ)] using
    integrable_phase_weight (radialVolumeWeight_contDiff n).continuous
      (radialVolumeWeight_hasCompactSupport n) t (hS.comp (by fun_prop))

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
