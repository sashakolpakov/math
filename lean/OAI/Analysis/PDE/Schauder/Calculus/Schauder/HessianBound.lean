import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Decomposition
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Bilinear

/-! A global Hessian bound for compactly supported Newtonian data, uniform under mollification. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace
namespace OAI.Analysis.PDE.Schauder

theorem truncatedNewtonianEntry_unit_bound {m : ℕ}
    (v w y : EuclideanSpace ℝ (Fin m)) :
    |truncatedNewtonianEntry m v w 1 y| ≤ newtonianSizeConstant m * ‖v‖ * ‖w‖ := by
  have hD := newtonianSizeConstant_nonneg m
  by_cases hy : ‖y‖ ≤ 1
  · rw [truncatedNewtonianEntry_zero m v w (by norm_num) hy, abs_zero]
    positivity
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hb := newtonianEntry_bound m hy0 v w
  have hp : ‖y‖ ^ (-(m : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hy) (neg_nonpos.mpr (Nat.cast_nonneg m))
  have hc : |1 - radialCutoff 1 y| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one 1 y))]
    linarith [radialCutoff_nonneg 1 y]
  change |(1 - radialCutoff 1 y) * newtonianSecond m y v w| ≤ _
  rw [abs_mul]
  calc
    _ ≤ 1 * |newtonianSecond m y v w| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ newtonianSizeConstant m * ‖y‖ ^ (-(m : ℝ)) * ‖v‖ * ‖w‖ := by simpa using hb
    _ ≤ _ := by
      gcongr
      simpa using mul_le_mul_of_nonneg_left hp hD

theorem scalarConvolution_bound_of_bounded_kernel {m : ℕ}
    (K f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Integrable f)
    {B : ℝ} (hb : ∀ y, |K y| ≤ B) (x : EuclideanSpace ℝ (Fin m)) :
    |scalarConvolution K f x| ≤ B * ∫ y, |f y| := by
  change ‖∫ y, K y * f (x - y)‖ ≤ _
  have hi : Integrable (fun y => B * |f (x - y)|) := (hf.comp_sub_left x).norm.const_mul B
  have hmajor : ∀ᵐ y, ‖K y * f (x - y)‖ ≤ B * |f (x - y)| := by
    filter_upwards with y
    simpa only [norm_mul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (hb y) (abs_nonneg (f (x - y)))
  have h := norm_integral_le_of_norm_le hi hmajor
  have he : (∫ y, |f (x - y)|) = ∫ y, |f y| := integral_sub_left_eq_self (fun y => |f y|) volume x
  rw [integral_const_mul, he] at h
  exact h

theorem newtonianPotential_hessian_entry_bound {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {H U I : ℝ}
    (hH : 0 ≤ H) (hU : 0 ≤ U) (_ : 0 ≤ I)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hu : ∀ x, |f x| ≤ U) (hi : (∫ y, |f y|) ≤ I)
    (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤
      H * newtonianSizeConstant m * rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α * 3 ^ α +
        newtonianSizeConstant m * I +
        U * |volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m)| := by
  rw [newtonianPotential_hessian_near_far hm f hf hfc x i j (by norm_num : (0 : ℝ) < 1)]
  have hn := nearSingularPart_bound (show 1 ≤ m by omega) f x
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hH hα (fun y => by simpa only [sub_sub_cancel_left, norm_neg] using hh (x - y) x)
  simp only [mul_one, PiLp.norm_single, norm_one] at hn
  have hfar := scalarConvolution_bound_of_bounded_kernel
    (truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) 1)
    f (hf.continuous.integrable_of_hasCompactSupport hfc)
    (fun y => by simpa using (truncatedNewtonianEntry_unit_bound
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y)) x
  have hfar' : |scalarConvolution
      (truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) 1) f x| ≤
      newtonianSizeConstant m * I := hfar.trans (mul_le_mul_of_nonneg_left hi (newtonianSizeConstant_nonneg m))
  have hdelta : |f x * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0)| ≤
      U * |volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m)| := by
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hu x) (abs_nonneg _)
    · simp only [mul_zero, abs_zero]
      positivity
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hn hfar')) hdelta)

theorem newtonianPotential_hessian_bound {m : ℕ} (hm : 2 ≤ m) {α : ℝ} (hα : 0 < α) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ H U I, 0 ≤ H → 0 ≤ U → 0 ≤ I →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, |f x| ≤ U) → (∫ y, |f y|) ≤ I →
      ∀ x, ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x‖ ≤ C * (H + U + I) := by
  let a := newtonianSizeConstant m * rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α * 3 ^ α
  let b := newtonianSizeConstant m
  let c := |volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m)|
  have ha : 0 ≤ a := by dsimp [a]; exact mul_nonneg (mul_nonneg (newtonianSizeConstant_nonneg m)
    (rieszBallMass_nonneg volume α)) (Real.rpow_nonneg (by norm_num) _)
  have hb : 0 ≤ b := newtonianSizeConstant_nonneg m
  have hc : 0 ≤ c := abs_nonneg _
  refine ⟨(m : ℝ) * m * (a + b + c) + 1, by positivity, ?_⟩
  intro f hf hfc H U I hH hU hI hh hu hi x
  have he (i j : Fin m) : |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤
      (a + b + c) * (H + U + I) := by
    have h := newtonianPotential_hessian_entry_bound hm hα f hf hfc hH hU hI hh hu hi x i j
    have haU := mul_nonneg ha hU
    have haI := mul_nonneg ha hI
    have hbH := mul_nonneg hb hH
    have hbU := mul_nonneg hb hU
    have hcH := mul_nonneg hc hH
    have hcI := mul_nonneg hc hI
    change _ ≤ H * newtonianSizeConstant m * rieszBallMass volume α * 3 ^ α + b * I + U * c at h
    dsimp only [a] at *
    nlinarith
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (a + b + c) * (H + U + I) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
    _ = (m : ℝ) * m * (a + b + c) * (H + U + I) := by simp; ring
    _ ≤ _ := by nlinarith

end OAI.Analysis.PDE.Schauder
