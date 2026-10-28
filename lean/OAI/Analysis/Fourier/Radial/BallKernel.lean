import OAI.Analysis.Fourier.Radial.Sphere.Transverse

open OAI.Analysis.Fourier.Wave

/-! Radial Fourier kernels of continuous weights on the unit ball. -/

open _root_.MeasureTheory Metric Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def unitBallVolume (n : ℕ) : Measure (Space n) :=
  volume.restrict (closedBall 0 1)

theorem integrable_unitBallVolume {n : ℕ} {w : Space n → ℝ} (hw : Continuous w) :
    Integrable w (unitBallVolume n) :=
  hw.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)

theorem ae_unitBall_inner_bound {n : ℕ} (v : Space n) :
    ∀ᵐ ξ ∂unitBallVolume n, |inner ℝ v ξ| ≤ ‖v‖ := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Space n)))
    measurableSet_closedBall] with ξ hξ
  have hnorm : ‖ξ‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hξ
  exact (abs_real_inner_le_norm v ξ).trans (by nlinarith [norm_nonneg v])

theorem measurePreserving_unitBall_orthogonal {n : ℕ}
    (e : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving e (unitBallVolume n) (unitBallVolume n) := by
  have he : e ⁻¹' closedBall (0 : Space n) 1 = closedBall 0 1 := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_zero_right, e.norm_map]
  simpa only [unitBallVolume, he] using e.measurePreserving.restrict_preimage
    (s := closedBall 0 1) measurableSet_closedBall

def ballCosineKernel {n : ℕ} (w : Space n → ℝ) (x : Space n) : ℝ :=
  ∫ ξ, w ξ * Real.cos (inner ℝ x ξ) ∂unitBallVolume n

def ballCosineLineDeriv {n : ℕ} (w : Space n → ℝ) (x v : Space n) (t : ℝ) : ℝ :=
  ∫ ξ, -(w ξ * inner ℝ v ξ) * Real.sin (inner ℝ (x + t • v) ξ) ∂unitBallVolume n

def ballCosineLineSecond {n : ℕ} (w : Space n → ℝ) (x v : Space n) (t : ℝ) : ℝ :=
  ∫ ξ, -(w ξ * (inner ℝ v ξ) ^ 2) * Real.cos (inner ℝ (x + t • v) ξ) ∂unitBallVolume n

theorem ballCosineKernel_orthogonal {n : ℕ} {w : Space n → ℝ}
    (hw : ∀ (e : Space n ≃ₗᵢ[ℝ] Space n) ξ, w (e ξ) = w ξ)
    (e : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    ballCosineKernel w (e x) = ballCosineKernel w x := by
  have H := (measurePreserving_unitBall_orthogonal e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun ξ => w ξ * Real.cos (inner ℝ (e x) ξ))
  simpa only [ballCosineKernel, e.inner_map_map, hw] using H.symm

theorem ballCosineKernel_radial {n : ℕ} {w : Space n → ℝ}
    (hw : ∀ (e : Space n ≃ₗᵢ[ℝ] Space n) ξ, w (e ξ) = w ξ)
    {v : Space n} (hv : ‖v‖ = 1) (x : Space n) :
    ballCosineKernel w x = ballCosineKernel w (‖x‖ • v) := by
  have hn : ‖x‖ = ‖‖x‖ • v‖ := by simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), hv, mul_one]
  let e : Space n ≃ₗᵢ[ℝ] Space n := (ℝ ∙ (x - ‖x‖ • v))ᗮ.reflection
  have he : e x = ‖x‖ • v := Submodule.reflection_sub hn
  rw [← he]
  exact (ballCosineKernel_orthogonal hw e x).symm

theorem hasDerivAt_ballCosineLine {n : ℕ} {w : Space n → ℝ}
    (hw : Continuous w) (x v : Space n) (t : ℝ) :
    HasDerivAt (fun s => ballCosineKernel w (x + s • v))
      (ballCosineLineDeriv w x v t) t := by
  have H := hasDerivAt_cosineIntegral (integrable_unitBallVolume hw)
    (a := fun ξ => inner ℝ x ξ) (b := fun ξ => inner ℝ v ξ)
    (by fun_prop) (by fun_prop) (ae_unitBall_inner_bound v) t
  simpa only [ballCosineKernel, ballCosineLineDeriv, inner_add_left, neg_mul,
    real_inner_smul_left] using H

theorem hasDerivAt_ballCosineLineDeriv {n : ℕ} {w : Space n → ℝ}
    (hw : Continuous w) (x v : Space n) (t : ℝ) :
    HasDerivAt (ballCosineLineDeriv w x v) (ballCosineLineSecond w x v t) t := by
  have hi : Integrable (fun ξ => -(w ξ * inner ℝ v ξ)) (unitBallVolume n) :=
    integrable_unitBallVolume (by fun_prop)
  have H := hasDerivAt_sineIntegral hi
    (a := fun ξ => inner ℝ x ξ) (b := fun ξ => inner ℝ v ξ)
    (by fun_prop) (by fun_prop) (ae_unitBall_inner_bound v) t
  convert H using 1
  · funext s
    simp only [ballCosineLineDeriv, inner_add_left, real_inner_smul_left]
  · apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [inner_add_left, real_inner_smul_left]
    ring

theorem ballCosine_transverse_deriv {n : ℕ} {w : Space n → ℝ}
    (hw : Continuous w) (hrot : ∀ (e : Space n ≃ₗᵢ[ℝ] Space n) ξ, w (e ξ) = w ξ)
    {v z : Space n} (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hvz : inner ℝ v z = 0)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ballCosineLineDeriv w (r • v) z t =
      ballCosineLineDeriv w 0 v (radialTransverseCurve r t) * (t / radialTransverseCurve r t) := by
  have ha : HasDerivAt (fun s => ballCosineKernel w (s • v))
      (ballCosineLineDeriv w 0 v (radialTransverseCurve r t)) (radialTransverseCurve r t) := by
    simpa only [zero_add] using hasDerivAt_ballCosineLine hw 0 v (radialTransverseCurve r t)
  have H := ha.comp t (hasDerivAt_radialTransverseCurve hr t)
  apply (hasDerivAt_ballCosineLine hw (r • v) z t).unique
  convert H using 1
  funext s
  rw [ballCosineKernel_radial hrot hv, norm_orthogonal_line hv hz hvz]
  rfl

theorem ballCosine_transverse_second {n : ℕ} {w : Space n → ℝ}
    (hw : Continuous w) (hrot : ∀ (e : Space n ≃ₗᵢ[ℝ] Space n) ξ, w (e ξ) = w ξ)
    {v z : Space n} (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hvz : inner ℝ v z = 0)
    {r : ℝ} (hr : 0 < r) :
    ballCosineLineSecond w (r • v) z 0 = ballCosineLineDeriv w 0 v r / r := by
  have H := hasDerivAt_radialTransverseSecond hr (hasDerivAt_ballCosineLineDeriv hw 0 v r)
  apply (hasDerivAt_ballCosineLineDeriv hw (r • v) z 0).unique
  have he : ballCosineLineDeriv w (r • v) z =
      (fun t => ballCosineLineDeriv w 0 v (radialTransverseCurve r t) *
        (t / radialTransverseCurve r t)) := by
    funext t
    exact ballCosine_transverse_deriv hw hrot hv hz hvz hr t
  rw [he]
  exact H

end OAI.Analysis.Fourier.Radial
