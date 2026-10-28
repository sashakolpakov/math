import OAI.Analysis.Calculus.Coefficients.Compact

open Set Filter _root_.MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Schauder

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem standardMollifier_radius_le_one (j : ℕ) :
    (OAI.Analysis.PDE.Schauder.standardMollifier m j).rOut ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

omit [CompleteSpace F] in
theorem smoothField_bound_on_ball
    (f : EuclideanSpace ℝ (Fin m) → F) {R B : ℝ}
    (hf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (R+1), ‖f x‖ ≤ B)
    (j : ℕ) {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ closedBall 0 R) :
    ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x‖ ≤ B := by
  let φ := OAI.Analysis.PDE.Schauder.standardMollifier m j
  rw [smoothField_eq_integral]
  have h := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const B)
    (Eventually.of_forall fun y ↦ show ‖φ.normed volume y • f (x-y)‖ ≤ φ.normed volume y*B from by
      by_cases hy : φ.normed volume y=0
      · simp [hy]
      · have hys : y ∈ ball (0 : EuclideanSpace ℝ (Fin m)) φ.rOut := by
          rw [←φ.support_normed_eq (μ := volume)]; exact hy
        have hyN : ‖y‖ ≤ 1 := by
          have hy' : ‖y‖ < φ.rOut := by simpa only [mem_ball,dist_zero_right] using hys
          exact hy'.le.trans (standardMollifier_radius_le_one j)
        have hxN : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
        have hxy : x-y ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (R+1) := by
          simpa only [mem_closedBall,dist_zero_right] using
            (norm_sub_le x y).trans (add_le_add hxN hyN)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed y)]
        exact mul_le_mul_of_nonneg_left (hf (x-y) hxy) (φ.nonneg_normed y))
  simpa only [integral_mul_const,φ.integral_normed,one_mul] using h

omit [CompleteSpace F] in
theorem smoothField_uniform_bound_on_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x‖ ≤ B := by
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (R+1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro j x hx
  apply (smoothField_bound_on_ball f hB j ?_).trans (le_max_left _ _)
  simpa only [mem_closedBall,dist_zero_right,id_eq] using hR x hx

omit [CompleteSpace F] in
theorem smoothField_uniform_derivative_bound_on_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ‖fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) x‖ ≤ B := by
  simp_rw [fderiv_smoothField _ f hf]
  exact smoothField_uniform_bound_on_compact _ (hf.continuous_fderiv one_ne_zero) hK

omit [CompleteSpace F] in
theorem smoothField_uniform_lipschitz_on_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ∀ y, y ∈ K →
      ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x-smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f y‖ ≤ B*‖x-y‖ := by
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hsub : K ⊆ closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
    intro x hx
    simpa only [mem_closedBall,dist_zero_right,id_eq] using hR x hx
  obtain ⟨B,hB,hDf⟩ := smoothField_uniform_derivative_bound_on_compact f hf
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R)
  refine ⟨B,hB,?_⟩
  intro j x hx y hy
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (contDiff_smoothField _ f hf.continuous).differentiable (by simp) z)
    (fun z hz ↦ hDf j z hz) (hsub hy) (hsub hx)

omit [CompleteSpace F] in
theorem smoothField_uniform_holder_on_compact
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ∀ y, y ∈ K →
      ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x-smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f y‖ ≤ B*‖x-y‖^α := by
  obtain ⟨U,hU,hu⟩ := smoothField_uniform_bound_on_compact f hf.continuous hK
  obtain ⟨L,hL,hl⟩ := smoothField_uniform_lipschitz_on_compact f hf hK
  refine ⟨L+2*U,by positivity,?_⟩
  intro j x hx y hy
  by_cases hd : ‖x-y‖ ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hd hα1
    exact (hl j x hx y hy).trans ((mul_le_mul_of_nonneg_left hp hL).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)))
  · have hp : 1 ≤ ‖x-y‖^α := Real.one_le_rpow (le_of_not_ge hd) hα
    have hb : ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x-smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f y‖ ≤ 2*U :=
      (norm_sub_le _ _).trans (by linarith [hu j x hx,hu j y hy])
    calc
      _ ≤ 2*U := hb
      _ ≤ 2*U*‖x-y‖^α := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.Calculus.Coefficients
