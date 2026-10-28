import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialDerivatives
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedMass

/-! Twice integrating smooth kernels against compactly supported data by parts. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem integral_mul_fderiv_compact {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ f y v) = -∫ y, fderiv ℝ K y v * f y := by
  have hDK : Continuous (fun y => fderiv ℝ K y v) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDf : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDK.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    ((hK.continuous.mul hDf).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_left)
    ((hK.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    (fun y _ => hK.differentiable one_ne_zero y) (fun y _ => hf.differentiable one_ne_zero y)

theorem integral_mul_second_fderiv_compact {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 2 K) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (v w : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ (fderiv ℝ f) y v w) =
      ∫ y, fderiv ℝ (fderiv ℝ K) y w v * f y := by
  have hDK : ContDiff ℝ 1 (fderiv ℝ K) := hK.fderiv_right (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hKv : ContDiff ℝ 1 (fun y => fderiv ℝ K y v) := hDK.clm_apply contDiff_const
  have hfw : ContDiff ℝ 1 (fun y => fderiv ℝ f y w) := hDf.clm_apply contDiff_const
  calc
    _ = ∫ y, K y * fderiv ℝ (fun z => fderiv ℝ f z w) y v := by
      congr 1
      funext y
      rw [fderiv_apply_const _ y w v (hDf.differentiable one_ne_zero y)]
    _ = -∫ y, fderiv ℝ K y v * fderiv ℝ f y w :=
      integral_mul_fderiv_compact K _ (hK.of_le (by norm_num)) hfw (hfc.fderiv_apply ℝ w) v
    _ = ∫ y, fderiv ℝ (fun z => fderiv ℝ K z v) y w * f y := by
      rw [integral_mul_fderiv_compact _ f hKv (hf.of_le (by norm_num)) hfc w, neg_neg]
    _ = _ := by
      congr 1
      funext y
      rw [fderiv_apply_const _ y v w (hDK.differentiable one_ne_zero y)]

theorem shiftedRadialHessian_green {m : ℕ} (p : ℝ) {s : ℝ} (hs : 0 < s)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (v w : EuclideanSpace ℝ (Fin m)) :
    (∫ y, shiftedRadialPower p s y * fderiv ℝ (fderiv ℝ f) y v w) =
      ∫ y, shiftedRadialHessian p s y v w * f y := by
  rw [integral_mul_second_fderiv_compact _ f
    ((contDiff_shiftedRadialPower p hs).of_le (by norm_num)) hf hfc v w]
  congr 1
  funext y
  rw [second_fderiv_shiftedRadialPower p hs y]
  congr 1
  simp only [shiftedRadialHessian_apply, real_inner_comm w v]
  ring

end OAI.Analysis.PDE.Schauder
