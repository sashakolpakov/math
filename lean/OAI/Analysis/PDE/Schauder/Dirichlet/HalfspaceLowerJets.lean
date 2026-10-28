import OAI.Analysis.PDE.Schauder.Dirichlet.HalfspaceInterpolation

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Schauder

theorem convex_coordinate_halfspace {m : ℕ} (k : Fin m) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin m) | 0 ≤ x k} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x k + b * y k
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

theorem halfspace_fderiv_lipschitz {m : ℕ} (k : Fin m)
    {u : EuclideanSpace ℝ (Fin m) → ℝ} (hu : ContDiff ℝ 2 u) {D : ℝ}
    (hD : ∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ D) :
    ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ D * ‖x-y‖ := by
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  intro x hx y hy
  exact (convex_coordinate_halfspace k).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hDu.differentiable one_ne_zero z) hD hy hx

theorem euclidean_linear_norm_le_of_entries {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hA : ∀ i : Fin m, |A (EuclideanSpace.single i 1)| ≤ D) : ‖A‖ ≤ (m : ℝ) * D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  have he : A v = ∑ i : Fin m, v i * A (EuclideanSpace.single i 1) := by
    calc
      A v = A (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ)) := congrArg A hv.symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  rw [he, Real.norm_eq_abs]
  calc
    _ ≤ ∑ i : Fin m, |v i * A (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ‖v‖ * D := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i)
        (hA i) (abs_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * D * ‖v‖ := by simp; ring

/-- Unit forward segments stay in the closed halfspace. The mean-value
theorem on these segments bounds every first derivative without using
values from the opposite side of the boundary. -/
theorem halfspace_gradient_bound {m : ℕ} (k : Fin m)
    {u : EuclideanSpace ℝ (Fin m) → ℝ} (hu : ContDiff ℝ 2 u) {D M : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hH : ∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ D)
    (hbound : ∀ x, 0 ≤ x k → |u x| ≤ M) :
    ∀ x, 0 ≤ x k → ‖fderiv ℝ u x‖ ≤ (m : ℝ) * (D + 2 * M) := by
  intro x hx
  apply euclidean_linear_norm_le_of_entries _ (by positivity)
  intro i
  let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hvk : 0 ≤ v k := by simp [v, PiLp.single_apply]; split_ifs <;> norm_num
  have hline (t : ℝ) (ht : 0 ≤ t) : 0 ≤ (x + t • v) k := by
    change 0 ≤ x k + t * v k
    exact add_nonneg hx (mul_nonneg ht hvk)
  let f : ℝ → ℝ := fun t ↦ u (x + t • v)
  have hf (t : ℝ) : HasDerivAt f (fderiv ℝ u (x + t • v) v) t := by
    have h := (hu.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add x)
    simpa only [one_smul, Function.comp_def, id_eq, f] using h
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t ↦ (hf t).continuousAt)
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f
    (fun t ↦ fderiv ℝ u (x + t • v) v) (by norm_num : (0 : ℝ) < 1)
    hfc.continuousOn (fun t _ ↦ hf t)
  simp only [f, one_smul, zero_smul, add_zero, sub_zero, div_one] at he
  have hLip := halfspace_fderiv_lipschitz k hu hH x hx (x+t•v) (hline t ht.1.le)
  have hdist : ‖x - (x+t•v)‖ = t := by
    rw [norm_sub_rev]
    simp only [add_sub_cancel_left, norm_smul, hv, Real.norm_eq_abs, abs_of_pos ht.1, mul_one]
  rw [hdist] at hLip
  have hentry : |fderiv ℝ u x v - fderiv ℝ u (x+t•v) v| ≤ D := by
    have hh := (fderiv ℝ u x - fderiv ℝ u (x+t•v)).le_opNorm v
    simp only [sub_apply, Real.norm_eq_abs, hv, mul_one] at hh
    exact hh.trans (hLip.trans (by nlinarith [ht.2]))
  have hslope : |fderiv ℝ u (x+t•v) v| ≤ 2 * M := by
    rw [he]
    exact (abs_sub _ _).trans (by
      have ha := hbound (x+v) (by simpa only [one_smul] using hline 1 zero_le_one)
      have hb := hbound x hx
      linarith)
  have hh := abs_add_le (fderiv ℝ u x v - fderiv ℝ u (x+t•v) v)
    (fderiv ℝ u (x+t•v) v)
  rw [sub_add_cancel] at hh
  exact hh.trans (add_le_add hentry hslope)

theorem halfspace_holder_of_bounded_lipschitz {m : ℕ} (k : Fin m)
    {F : Type*} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin m) → F)
    {α U L : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hu : ∀ x, 0 ≤ x k → ‖f x‖ ≤ U)
    (hl : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → ‖f x-f y‖ ≤ L * ‖x-y‖) :
    ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → ‖f x-f y‖ ≤ (L + 2*U) * ‖x-y‖ ^ α := by
  intro x hx y hy
  by_cases hd : ‖x-y‖ ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hd hα1
    exact (hl x hx y hy).trans ((mul_le_mul_of_nonneg_left hp hL).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)))
  · have hp : 1 ≤ ‖x-y‖ ^ α := Real.one_le_rpow (le_of_not_ge hd) hα
    have hb : ‖f x-f y‖ ≤ 2*U := (norm_sub_le _ _).trans (by linarith [hu x hx, hu y hy])
    calc
      _ ≤ 2*U := hb
      _ ≤ 2*U*‖x-y‖ ^ α := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Schauder
