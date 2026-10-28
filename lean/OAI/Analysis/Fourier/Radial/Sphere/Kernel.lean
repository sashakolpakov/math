import OAI.Analysis.Fourier.Radial.Sphere.Measure
import OAI.Analysis.Fourier.Restriction.Basic
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

/-! The real radial Fourier kernel of the manuscript surface measure. -/

open _root_.MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def sphereCosineKernel {n : ℕ} (x : Space n) : ℝ :=
  ∫ ω, Real.cos (inner ℝ x ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n

def axisSphereCosineKernel {n : ℕ} (v : Space n) (r : ℝ) : ℝ :=
  sphereCosineKernel (r • v)

theorem sphereCosineKernel_orthogonal {n : ℕ}
    (e : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    sphereCosineKernel (e x) = sphereCosineKernel x := by
  have H := (measurePreserving_sphere_orthogonal e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun ω => Real.cos (inner ℝ (e x) ω))
  simpa only [sphereCosineKernel, e.inner_map_map] using H.symm

theorem sphereCosineKernel_eq_of_norm_eq {n : ℕ} {x y : Space n}
    (h : ‖x‖ = ‖y‖) : sphereCosineKernel x = sphereCosineKernel y := by
  let e : Space n ≃ₗᵢ[ℝ] Space n := (ℝ ∙ (x - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub h
  rw [← he]
  exact (sphereCosineKernel_orthogonal e x).symm

theorem sphereCosineKernel_radial {n : ℕ} {v : Space n} (hv : ‖v‖ = 1)
    (x : Space n) : sphereCosineKernel x = axisSphereCosineKernel v ‖x‖ := by
  apply sphereCosineKernel_eq_of_norm_eq
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hv, mul_one]

theorem integrable_sphere_cosine {n : ℕ} (x : Space n) :
    Integrable (fun ω => Real.cos (inner ℝ x ω)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1 : ℝ)).mono'
    (by fun_prop)
  filter_upwards [] with ω
  exact Real.abs_cos_le_one _

theorem continuous_sphereCosineKernel (n : ℕ) : Continuous (sphereCosineKernel (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Eventually.of_forall (fun z => (integrable_sphere_cosine z).aestronglyMeasurable)
  · exact Eventually.of_forall (fun z => Eventually.of_forall (fun ω => Real.abs_cos_le_one _))
  · exact integrable_const _
  · exact Eventually.of_forall (fun ω => (by fun_prop : Continuous (fun z : Space n =>
      Real.cos (inner ℝ z ω))).tendsto x)

theorem axisSphereCosineKernel_zero {n : ℕ} (v : Space n) :
    axisSphereCosineKernel v 0 = (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real univ := by
  simp [axisSphereCosineKernel, sphereCosineKernel]

end OAI.Analysis.Fourier.Radial
