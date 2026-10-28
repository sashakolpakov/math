import OAI.Analysis.Fourier.WavePackets.AngularAtlas
import OAI.Analysis.PDE.Concentration.FrequencyParameters

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped RealInnerProductSpace

def angularChartAxis {d : ℕ} (c : Fin d → ℝ) : Space (d + 1) :=
  WithLp.toLp 2 (Fin.cases 1 c)

@[simp] theorem angularChartAxis_zero {d : ℕ} (c : Fin d → ℝ) :
    angularChartAxis c 0 = 1 := rfl

@[simp] theorem angularChartAxis_succ {d : ℕ} (c : Fin d → ℝ) (i : Fin d) :
    angularChartAxis c i.succ = c i := by simp [angularChartAxis]

theorem angularChartAxis_norm_ge_one {d : ℕ} (c : Fin d → ℝ) :
    1 ≤ ‖angularChartAxis c‖ := by
  simpa using PiLp.norm_apply_le (angularChartAxis c) 0

def angularChartRotation {d : ℕ} (c : Fin d → ℝ) :
    Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) :=
  Submodule.reflection (ℝ ∙ (angularChartAxis c -
    ‖angularChartAxis c‖ • EuclideanSpace.single 0 1))ᗮ

theorem angularChartRotation_axis {d : ℕ} (c : Fin d → ℝ) :
    angularChartRotation c (angularChartAxis c) =
      ‖angularChartAxis c‖ • EuclideanSpace.single 0 1 := by
  apply Submodule.reflection_sub
  simp [norm_smul]

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) : ‖x‖ ≤ ∑ i, |x i| := by
  have he : (∑ i, EuclideanSpace.single i (x i)) = x := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i, EuclideanSpace.single i (x i)‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := by simp

theorem angular_chart_residual_bound {d : ℕ} {γ : ℝ} (_ : 0 ≤ γ)
    (c : Fin d → ℝ) {ξ : Space (d + 1)} (_ : 0 ≤ ξ 0)
    (hw : ∀ i : Fin d, |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0) :
    ‖ξ - ξ 0 • angularChartAxis c‖ ≤ (d : ℝ) * γ * ξ 0 := by
  calc
    ‖ξ - ξ 0 • angularChartAxis c‖ ≤
        ∑ i : Fin (d + 1), |(ξ - ξ 0 • angularChartAxis c) i| :=
      euclidean_norm_le_sum_abs _
    _ = ∑ i : Fin d, |ξ i.succ - c i * ξ 0| := by
      rw [Fin.sum_univ_succ]
      simp [mul_comm]
    _ ≤ ∑ _ : Fin d, γ * ξ 0 := Finset.sum_le_sum (fun i _ => hw i)
    _ = (d : ℝ) * γ * ξ 0 := by simp; ring

theorem angular_chart_rotated_residual_bound {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (c : Fin d → ℝ) {ξ : Space (d + 1)} (hξ : 0 ≤ ξ 0)
    (hw : ∀ i : Fin d, |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0) :
    ‖angularChartRotation c ξ -
      (ξ 0 * ‖angularChartAxis c‖) • EuclideanSpace.single 0 1‖ ≤
        (d : ℝ) * γ * ξ 0 := by
  have he : angularChartRotation c (ξ - ξ 0 • angularChartAxis c) =
      angularChartRotation c ξ -
        (ξ 0 * ‖angularChartAxis c‖) • EuclideanSpace.single 0 1 := by
    rw [map_sub, map_smul, angularChartRotation_axis, smul_smul]
  rw [← he, (angularChartRotation c).norm_map]
  exact angular_chart_residual_bound hγ c hξ hw

theorem angular_chart_positive_rotated_axis {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hsmall : (d : ℝ) * γ ≤ 1 / 2)
    (c : Fin d → ℝ) {ξ : Space (d + 1)} (hξ : 0 ≤ ξ 0)
    (hw : ∀ i : Fin d, |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0) :
    ξ 0 / 2 ≤ angularChartRotation c ξ 0 := by
  have hr := angular_chart_rotated_residual_bound hγ c hξ hw
  have hc := PiLp.norm_apply_le (angularChartRotation c ξ -
      (ξ 0 * ‖angularChartAxis c‖) • EuclideanSpace.single 0 1) 0
  have hc' : |angularChartRotation c ξ 0 - ξ 0 * ‖angularChartAxis c‖| ≤
      (d : ℝ) * γ * ξ 0 := by
    simpa using hc.trans hr
  have haxis := mul_le_mul_of_nonneg_left (angularChartAxis_norm_ge_one c) hξ
  have hsize := mul_le_mul_of_nonneg_right hsmall hξ
  have hlo := (abs_le.mp hc').1
  nlinarith

/-- Dropping the real longitudinal coordinate is a contraction into the
complex transverse space. -/
theorem norm_transverseFrequency_le {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖OAI.Analysis.PDE.Concentration.transverseFrequency η‖ ≤ ‖η‖ := by
  have ht : ‖OAI.Analysis.PDE.Concentration.transverseFrequency η‖ ^ 2 = ∑ i : Fin d, η (some i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp [OAI.Analysis.PDE.Concentration.transverseFrequency, Complex.norm_real]
  have hη : ‖η‖ ^ 2 = η none ^ 2 + ∑ i : Fin d, η (some i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    simp
  nlinarith [sq_nonneg (η none), norm_nonneg η, norm_nonneg (OAI.Analysis.PDE.Concentration.transverseFrequency η)]

theorem norm_transverse_rotated_chart_le {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (c : Fin d → ℝ) {ξ : Space (d + 1)} (hξ : 0 ≤ ξ 0)
    (hw : ∀ i : Fin d, |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0) :
    ‖OAI.Analysis.PDE.Concentration.transverseFrequency ((OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (angularChartRotation c ξ))‖ ≤
      (d : ℝ) * γ * ξ 0 := by
  let v := angularChartRotation c ξ -
      (ξ 0 * ‖angularChartAxis c‖) • EuclideanSpace.single 0 1
  have he : OAI.Analysis.PDE.Concentration.transverseFrequency ((OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm v) =
      OAI.Analysis.PDE.Concentration.transverseFrequency ((OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (angularChartRotation c ξ)) := by
    ext i
    simp [OAI.Analysis.PDE.Concentration.transverseFrequency, OAI.Analysis.PDE.Concentration.spatialFinIsometry_symm_apply, v]
  rw [← he]
  exact (norm_transverseFrequency_le _).trans
    (by rw [(OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm.norm_map];
        exact angular_chart_rotated_residual_bound hγ c hξ hw)

/-- The projective-grid width gives the genuine Gaussian velocity
bound in the orthogonal packet frame. -/
theorem angular_chart_gaussian_velocity_bound {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hsmall : (d : ℝ) * γ ≤ 1 / 2)
    (c : Fin d → ℝ) {ξ : Space (d + 1)} (hξ : 0 < ξ 0)
    (hw : ∀ i : Fin d, |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0) :
    let η := (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (angularChartRotation c ξ)
    0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η ∧ ‖OAI.Analysis.PDE.Concentration.gaussianVelocity η‖ ≤ 4 * d * γ := by
  dsimp only
  let η := (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (angularChartRotation c ξ)
  have hη0 : ξ 0 / 2 ≤ η none := by
    simpa [η, OAI.Analysis.PDE.Concentration.spatialFinIsometry_symm_apply] using
      angular_chart_positive_rotated_axis hγ hsmall c hξ.le hw
  have hsqrt0 : 0 < Real.sqrt 2 := by positivity
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hk : ξ 0 / 4 ≤ OAI.Analysis.PDE.Concentration.gaussianFrequencyK η := by
    rw [OAI.Analysis.PDE.Concentration.gaussianFrequencyK, le_div_iff₀ hsqrt0]
    have hh := mul_le_mul_of_nonneg_left hsqrt2 (show 0 ≤ ξ 0 / 4 by positivity)
    nlinarith [norm_nonneg η]
  have hk0 : 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η := lt_of_lt_of_le (by positivity) hk
  refine ⟨hk0, ?_⟩
  change ‖(OAI.Analysis.PDE.Concentration.gaussianFrequencyK η)⁻¹ • OAI.Analysis.PDE.Concentration.transverseFrequency η‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), ← div_eq_inv_mul]
  apply (div_le_iff₀ hk0).mpr
  have ht := norm_transverse_rotated_chart_le hγ c hξ.le hw
  change ‖OAI.Analysis.PDE.Concentration.transverseFrequency η‖ ≤ (d : ℝ) * γ * ξ 0 at ht
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 4 * (d : ℝ) * γ by positivity)
  nlinarith

end OAI.Analysis.Fourier.WavePackets
