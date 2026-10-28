import OAI.Analysis.Fourier.SquareFunction.Radius.Fourier
import OAI.Analysis.Fourier.SquareFunction.FourierL2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

def spatialPhase {n : ℕ} (x ξ : Space n) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I)

@[simp] theorem norm_spatialPhase {n : ℕ} (x ξ : Space n) : ‖spatialPhase x ξ‖ = 1 := by
  simp [spatialPhase, Complex.norm_exp]

theorem continuous_spatialPhase {n : ℕ} (x : Space n) : Continuous (spatialPhase x) := by
  unfold spatialPhase
  fun_prop

theorem integrable_spatialPhase_mul {n : ℕ} (x : Space n) {a : Space n → ℂ}
    (ha : Integrable a) : Integrable (fun ξ => spatialPhase x ξ * a ξ) := by
  apply ha.mono ((continuous_spatialPhase x).aestronglyMeasurable.mul ha.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ξ => by simp

/-- Thin radial shell without the auxiliary smooth amplitude, in cycles frequency. -/
def thinShellCycles {n : ℕ} (φ : ℝ → ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) (s : ℝ) : ℂ :=
  𝓕⁻ (fun ξ : Space n => φ ((s - ‖ξ‖) / δ) * (𝓕 f) ξ) x

theorem thinShellCycles_eq_radiusSuperposition {n : ℕ} (φ : ℝ → ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    thinShellCycles φ δ f x =
      radiusSuperposition volume φ δ (fun ξ : Space n => ‖ξ‖)
        (fun ξ => spatialPhase x ξ * (𝓕 f) ξ) := by
  funext s
  rw [thinShellCycles, Real.fourierInv_eq', radiusSuperposition]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [spatialPhase, smul_eq_mul]
    ring

theorem radiusPhase_norm_eq_wavePhase {n : ℕ} (t : ℝ) (ξ : Space n) :
    radiusPhase t ‖ξ‖ = OAI.Analysis.Fourier.Wave.wavePhase t ξ := by
  unfold radiusPhase OAI.Analysis.Fourier.Wave.wavePhase
  congr 1
  push_cast
  ring

theorem halfWaveIntegral_eq_spatialPhase {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x =
      ∫ ξ : Space n, radiusPhase t ‖ξ‖ * (spatialPhase x ξ * (𝓕 f) ξ) := by
  rw [OAI.Analysis.Fourier.Wave.halfWaveIntegral_eq_fourierInv, Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [radiusPhase_norm_eq_wavePhase]
    simp only [spatialPhase, smul_eq_mul]
    change spatialPhase x ξ * (OAI.Analysis.Fourier.Wave.wavePhase t ξ * (𝓕 f) ξ) =
      OAI.Analysis.Fourier.Wave.wavePhase t ξ * (spatialPhase x ξ * (𝓕 f) ξ)
    ring

/-- Fourier transformation in the radius converts a thin shell exactly into
the half-wave propagator weighted by the Fourier transform of its cutoff. -/
theorem fourier_thinShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) (t : ℝ) :
    𝓕 (thinShellCycles φ δ f x) t =
      (δ : ℂ) * (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x := by
  rw [thinShellCycles_eq_radiusSuperposition]
  have ham : Measurable (fun ξ : Space n => spatialPhase x ξ * (𝓕 f) ξ) :=
    (continuous_spatialPhase x).measurable.mul (𝓕 f).continuous.measurable
  rw [fourier_radiusSuperposition volume φ hδ continuous_norm.measurable ham
    (integrable_spatialPhase_mul x (𝓕 f).integrable) t,
    ← halfWaveIntegral_eq_spatialPhase]
  rfl

theorem integrable_thinShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (thinShellCycles φ δ f x) := by
  rw [thinShellCycles_eq_radiusSuperposition]
  exact integrable_radiusSuperposition volume φ hδ continuous_norm.measurable
    ((continuous_spatialPhase x).measurable.mul (𝓕 f).continuous.measurable)
    (integrable_spatialPhase_mul x (𝓕 f).integrable)

theorem memLp_thinShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    MemLp (thinShellCycles φ δ f x) 2 := by
  rw [thinShellCycles_eq_radiusSuperposition]
  exact memLp_radiusSuperposition volume φ hδ continuous_norm.measurable
    ((continuous_spatialPhase x).measurable.mul (𝓕 f).continuous.measurable)
    (integrable_spatialPhase_mul x (𝓕 f).integrable)

/-- The exact radius Plancherel step in the thin-shell transfer. -/
theorem thinShellCycles_radius_L2_identity {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    eLpNorm (thinShellCycles φ δ f x) 2 volume =
      ENNReal.ofReal δ *
        eLpNorm (fun t : ℝ => (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) 2 volume := by
  rw [← eLpNorm_fourier_line (integrable_thinShellCycles φ hδ f x)
    (memLp_thinShellCycles φ hδ f x)]
  have he : 𝓕 (thinShellCycles φ δ f x) = (δ : ℂ) •
      (fun t : ℝ => (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) := by
    funext t
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using
      fourier_thinShellCycles φ hδ f x t
  rw [he, eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hδ]

end OAI.Analysis.Fourier.SquareFunction
