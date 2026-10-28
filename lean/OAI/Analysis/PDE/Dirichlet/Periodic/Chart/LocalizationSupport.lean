import OAI.Analysis.PDE.Nonlinear.LocalHolder

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- The separated-support Hölder extension estimate restricted to an
arbitrary set, notably a closed halfspace. No off-set bound is needed. -/
theorem holder_on_of_support_separated
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (T : Set E) (x₀ : E) {r R α C M : ℝ}
    (hrR : r < R) (hα : 0 ≤ α) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : ∀ x ∈ T, x ∉ closedBall x₀ r → f x = 0)
    (hb : ∀ x ∈ T, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ T ∩ closedBall x₀ R, ∀ y ∈ T ∩ closedBall x₀ R,
      ‖f x-f y‖ ≤ C*‖x-y‖^α) :
    ∀ x ∈ T, ∀ y ∈ T,
      ‖f x-f y‖ ≤ (C+2*M/(R-r)^α)*‖x-y‖^α := by
  have hgap : 0 < (R-r)^α := Real.rpow_pos_of_pos (sub_pos.mpr hrR) _
  have hcoef : 0 ≤ C+2*M/(R-r)^α := by positivity
  have hout (x y : E) (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ∉ closedBall x₀ R) :
      ‖f x-f y‖ ≤ (C+2*M/(R-r)^α)*‖x-y‖^α := by
    have hxr : x ∉ closedBall x₀ r := fun h ↦ hx (closedBall_subset_closedBall hrR.le h)
    rw [hs x hxT hxr]
    by_cases hy : y ∈ closedBall x₀ r
    · have hd : R-r ≤ ‖x-y‖ := by
        have hx' : R < dist x x₀ := lt_of_not_ge hx
        have ht := dist_triangle x y x₀
        have hy' : dist y x₀ ≤ r := hy
        rw [dist_eq_norm x y] at ht
        linarith only [hx',ht,hy']
      have hp := Real.rpow_le_rpow (sub_nonneg.mpr hrR.le) hd hα
      have hratio : 2*M ≤ (2*M/(R-r)^α)*‖x-y‖^α := by
        calc
          _ = (2*M/(R-r)^α)*(R-r)^α := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
      simp only [zero_sub,norm_neg]
      calc
        ‖f y‖ ≤ M := hb y hyT
        _ ≤ 2*M := by linarith only [hM]
        _ ≤ (2*M/(R-r)^α)*‖x-y‖^α := hratio
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC])
          (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [hs y hyT hy,sub_zero,norm_zero]
      positivity
  intro x hxT y hyT
  by_cases hx : x ∈ closedBall x₀ R
  · by_cases hy : y ∈ closedBall x₀ R
    · exact (hh x ⟨hxT,hx⟩ y ⟨hyT,hy⟩).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          (Real.rpow_nonneg (norm_nonneg _) _))
    · simpa only [norm_sub_rev] using hout y x hyT hxT hy
  · exact hout x y hxT hyT hx

end OAI.Analysis.PDE.Dirichlet
