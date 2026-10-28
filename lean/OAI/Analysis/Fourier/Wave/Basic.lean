import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.NormNum

open _root_.MeasureTheory FourierTransform
open scoped Real
noncomputable section
namespace OAI.Analysis.Fourier.Wave

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev WaveL2 (n : ℕ) := Lp (α := Space n) ℂ 2

/-- In mathlib's Fourier convention this is the symbol of the physical
half-wave propagator, expressed in cycles rather than angular frequency. -/
def wavePhase {n : ℕ} (t : ℝ) (ξ : Space n) : ℂ :=
  Complex.exp (((-2 * Real.pi * t * ‖ξ‖ : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_wavePhase {n : ℕ} (t : ℝ) (ξ : Space n) :
    ‖wavePhase t ξ‖ = 1 := by
  simp [wavePhase, Complex.norm_exp]

theorem continuous_wavePhase {n : ℕ} (t : ℝ) :
    Continuous (wavePhase (n := n) t) := by
  unfold wavePhase
  fun_prop

private theorem memLp_wavePhase_mul {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    MemLp (fun ξ ↦ wavePhase t ξ * f ξ) 2 := by
  apply (Lp.memLp f).congr_norm
    ((continuous_wavePhase t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun ξ ↦ by simp

/-- Multiplication by the unimodular half-wave symbol on Fourier-side `L²`. -/
def phaseMultiply {n : ℕ} (t : ℝ) (f : WaveL2 n) : WaveL2 n :=
  (memLp_wavePhase_mul t f).toLp _

theorem phaseMultiply_coe {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    (phaseMultiply t f : Space n → ℂ) =ᵐ[volume] fun ξ ↦ wavePhase t ξ * f ξ :=
  MemLp.coeFn_toLp _

@[simp] theorem norm_phaseMultiply {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    ‖phaseMultiply t f‖ = ‖f‖ := by
  rw [phaseMultiply, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    ((continuous_wavePhase t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f)
  exact Filter.Eventually.of_forall fun ξ ↦ by simp

/-- The Euclidean half-wave propagator, defined using the unitary `L²` Fourier transform. -/
def halfWaveL2 {n : ℕ} (t : ℝ) (f : WaveL2 n) : WaveL2 n :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).symm
    (phaseMultiply t ((Lp.fourierTransformₗᵢ (Space n) ℂ) f))

/-- Conservation of the `L²` norm, without assumptions on dimension or time. -/
@[simp] theorem norm_halfWaveL2 {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    ‖halfWaveL2 t f‖ = ‖f‖ := by
  simp [halfWaveL2]

/-- The squared time-integrated `L²` norm on the paper's observation interval.
This proves the zero-loss `p = 2` estimate in its iterated-norm form. -/
theorem halfWaveL2_time_energy {n : ℕ} (f : WaveL2 n) :
    (∫ t : ℝ in (1 : ℝ)..2, ‖halfWaveL2 t f‖ ^ 2) = ‖f‖ ^ 2 := by
  simp only [norm_halfWaveL2, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

@[simp] theorem wavePhase_zero {n : ℕ} (ξ : Space n) : wavePhase 0 ξ = 1 := by
  simp [wavePhase]

theorem wavePhase_add {n : ℕ} (s t : ℝ) (ξ : Space n) :
    wavePhase (s + t) ξ = wavePhase s ξ * wavePhase t ξ := by
  simp only [wavePhase, mul_add, add_mul, Complex.ofReal_add, Complex.exp_add]

@[simp] theorem phaseMultiply_zero {n : ℕ} (f : WaveL2 n) :
    phaseMultiply 0 f = f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe 0 f] with ξ hξ
  simpa using hξ

theorem phaseMultiply_add {n : ℕ} (s t : ℝ) (f : WaveL2 n) :
    phaseMultiply (s + t) f = phaseMultiply s (phaseMultiply t f) := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe (s + t) f,
    phaseMultiply_coe s (phaseMultiply t f), phaseMultiply_coe t f] with ξ h₁ h₂ h₃
  rw [h₁, h₂, h₃, wavePhase_add, mul_assoc]

theorem phaseMultiply_map_add {n : ℕ} (t : ℝ) (f g : WaveL2 n) :
    phaseMultiply t (f + g) = phaseMultiply t f + phaseMultiply t g := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe t (f + g), phaseMultiply_coe t f,
    phaseMultiply_coe t g, Lp.coeFn_add f g,
    Lp.coeFn_add (phaseMultiply t f) (phaseMultiply t g)] with ξ h h₁ h₂ h₃ h₄
  simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂, mul_add]

theorem phaseMultiply_map_smul {n : ℕ} (t : ℝ) (c : ℂ) (f : WaveL2 n) :
    phaseMultiply t (c • f) = c • phaseMultiply t f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe t (c • f), phaseMultiply_coe t f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseMultiply t f)] with ξ h h₁ h₂ h₃
  simp only [h, h₃, h₂, Pi.smul_apply, h₁, smul_eq_mul]
  ring

/-- The spectral phase action is unitary and has inverse at time `-t`. -/
def phaseMultiplyEquiv {n : ℕ} (t : ℝ) : WaveL2 n ≃ₗᵢ[ℂ] WaveL2 n where
  toFun := phaseMultiply t
  invFun := phaseMultiply (-t)
  left_inv f := by rw [← phaseMultiply_add]; simp
  right_inv f := by rw [← phaseMultiply_add]; simp
  map_add' := phaseMultiply_map_add t
  map_smul' := phaseMultiply_map_smul t
  norm_map' := norm_phaseMultiply t

/-- Unitarity of the physical half-wave flow. -/
def halfWaveEquiv {n : ℕ} (t : ℝ) : WaveL2 n ≃ₗᵢ[ℂ] WaveL2 n :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).trans
    ((phaseMultiplyEquiv t).trans (Lp.fourierTransformₗᵢ (Space n) ℂ).symm)

@[simp] theorem halfWaveEquiv_apply {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    halfWaveEquiv t f = halfWaveL2 t f := rfl

@[simp] theorem halfWaveL2_zero {n : ℕ} (f : WaveL2 n) : halfWaveL2 0 f = f := by
  simp [halfWaveL2]

theorem halfWaveL2_add {n : ℕ} (s t : ℝ) (f : WaveL2 n) :
    halfWaveL2 (s + t) f = halfWaveL2 s (halfWaveL2 t f) := by
  simp [halfWaveL2, phaseMultiply_add]

end OAI.Analysis.Fourier.Wave
