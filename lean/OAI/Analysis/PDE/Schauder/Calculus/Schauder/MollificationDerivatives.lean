import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Mollification

/-! Actual derivative commutation and convergence for the positive mollifiers. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology Convolution
namespace OAI.Analysis.PDE.Schauder

def standardMollifier (m k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) :=
  ⟨(1 / 2 : ℝ) ^ k / 2, (1 / 2 : ℝ) ^ k,
    half_pos (pow_pos (by norm_num) k), half_lt_self (pow_pos (by norm_num) k)⟩

theorem standardMollifier_radius_tendsto (m : ℕ) :
    Tendsto (fun k => (standardMollifier m k).rOut) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem fderiv_smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (smoothData φ f) x v = smoothData φ (fun y => fderiv ℝ f y v) x :=
  fderiv_scalarConvolution_data _ f φ.continuous_normed.locallyIntegrable hf hfc x v

theorem second_fderiv_smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v w : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fderiv ℝ (smoothData φ f)) x v w =
      smoothData φ (fun y => fderiv ℝ (fderiv ℝ f) y v w) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (fun y => fderiv ℝ f y w) := hDf.clm_apply contDiff_const
  have hDU : ContDiff ℝ 1 (fderiv ℝ (smoothData φ f)) :=
    (contDiff_smoothData φ f hf.continuous).fderiv_right (by simp)
  have he : (fun y => fderiv ℝ (smoothData φ f) y w) = smoothData φ (fun y => fderiv ℝ f y w) :=
    funext (fun y => fderiv_smoothData φ f hf1 hfc y w)
  rw [← fderiv_apply_const _ x w v (hDU.differentiable one_ne_zero x), he,
    fderiv_smoothData φ _ hg (hfc.fderiv_apply ℝ w)]
  congr 1
  funext y
  exact fderiv_apply_const _ y w v (hDf.differentiable one_ne_zero y)

theorem smoothData_tendsto {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f)
    (x : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun k => smoothData (standardMollifier m k) f x) atTop (𝓝 (f x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (standardMollifier_radius_tendsto m) hf x

theorem second_fderiv_smoothData_tendsto {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v w : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun k => fderiv ℝ (fderiv ℝ (smoothData (standardMollifier m k) f)) x v w)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) x v w)) := by
  simp_rw [second_fderiv_smoothData _ f hf hfc]
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact smoothData_tendsto _ ((hDf.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.clm_apply continuous_const) x

end OAI.Analysis.PDE.Schauder
