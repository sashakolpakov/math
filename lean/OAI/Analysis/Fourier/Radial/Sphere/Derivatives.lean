import OAI.Analysis.Fourier.Radial.Sphere.Kernel
import OAI.Analysis.Fourier.Radial.TrigIntegral

open OAI.Analysis.Fourier.Wave

/-! First and second directional derivatives of the actual sphere Fourier
kernel, obtained by differentiating the defining finite-measure integral. -/

open _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem ae_sphere_inner_bound {n : ℕ} (v : Space n) :
    ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n, |inner ℝ v ω| ≤ ‖v‖ := by
  filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
  simpa only [hω, mul_one] using abs_real_inner_le_norm v ω

theorem integrable_sphere_inner {n : ℕ} (v : Space n) :
    Integrable (fun ω => inner ℝ v ω) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) ‖v‖).mono' (by fun_prop)
  exact ae_sphere_inner_bound v

def sphereCosineLineDeriv {n : ℕ} (x v : Space n) (t : ℝ) : ℝ :=
  ∫ ω, -(inner ℝ v ω) * Real.sin (inner ℝ (x + t • v) ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n

def sphereCosineLineSecond {n : ℕ} (x v : Space n) (t : ℝ) : ℝ :=
  ∫ ω, -(inner ℝ v ω) ^ 2 * Real.cos (inner ℝ (x + t • v) ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n

theorem hasDerivAt_sphereCosineLine {n : ℕ} (x v : Space n) (t : ℝ) :
    HasDerivAt (fun s => sphereCosineKernel (x + s • v)) (sphereCosineLineDeriv x v t) t := by
  have H := hasDerivAt_cosineIntegral
    (w := fun _ : Space n => (1 : ℝ))
    (a := fun ω => inner ℝ x ω) (b := fun ω => inner ℝ v ω)
    (integrable_const _) (by fun_prop) (by fun_prop) (ae_sphere_inner_bound v) t
  simpa only [sphereCosineKernel, sphereCosineLineDeriv, one_mul, neg_mul,
    inner_add_left, real_inner_smul_left] using H

theorem hasDerivAt_sphereCosineLineDeriv {n : ℕ} (x v : Space n) (t : ℝ) :
    HasDerivAt (sphereCosineLineDeriv x v) (sphereCosineLineSecond x v t) t := by
  have H := hasDerivAt_sineIntegral (integrable_sphere_inner v).neg
    (a := fun ω => inner ℝ x ω) (b := fun ω => inner ℝ v ω)
    (by fun_prop) (by fun_prop) (ae_sphere_inner_bound v) t
  convert H using 1
  · funext s
    simp only [sphereCosineLineDeriv, inner_add_left, real_inner_smul_left, Pi.neg_apply]
  · apply integral_congr_ae
    filter_upwards [] with ω
    simp only [inner_add_left, real_inner_smul_left, Pi.neg_apply]
    ring

theorem hasDerivAt_axisSphereCosineKernel {n : ℕ} (v : Space n) (t : ℝ) :
    HasDerivAt (axisSphereCosineKernel v) (sphereCosineLineDeriv 0 v t) t := by
  change HasDerivAt (fun s => sphereCosineKernel (s • v)) _ t
  simpa only [zero_add] using hasDerivAt_sphereCosineLine 0 v t

end OAI.Analysis.Fourier.Radial
