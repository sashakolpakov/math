import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Reflection

/-! Even reflection is a norm-preserving fold onto the closed halfspace. -/

noncomputable section
open Set InnerProductSpace
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def normalFold (e x : E) : E := if 0 ≤ inner ℝ e x then x else normalReflection e x

omit [FiniteDimensional ℝ E] in
theorem normalFold_nonneg (e x : E) (he : ‖e‖ = 1) : 0 ≤ inner ℝ e (normalFold e x) := by
  by_cases hx : 0 ≤ inner ℝ e x
  · simp [normalFold, hx]
  · simp only [normalFold, ite_eq_right hx, inner_normalReflection e x he]
    linarith

omit [FiniteDimensional ℝ E] in
theorem norm_normalFold (e x : E) : ‖normalFold e x‖ = ‖x‖ := by
  by_cases hx : 0 ≤ inner ℝ e x <;> simp [normalFold, hx]

omit [FiniteDimensional ℝ E] in
theorem norm_sub_normalReflection_le (e x y : E) (he : ‖e‖ = 1)
    (hx : 0 ≤ inner ℝ e x) (hy : inner ℝ e y ≤ 0) :
    ‖x - normalReflection e y‖ ≤ ‖x - y‖ := by
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have heq : ‖x - normalReflection e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ e x * inner ℝ e y := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, normalReflection_apply e y he]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hee,
      real_inner_comm x e, real_inner_comm y e]
    ring
  have hp := mul_nonpos_of_nonneg_of_nonpos hx hy
  nlinarith [norm_nonneg (x - normalReflection e y), norm_nonneg (x - y)]

omit [FiniteDimensional ℝ E] in
theorem normalFold_norm_sub_le (e x y : E) (he : ‖e‖ = 1) :
    ‖normalFold e x - normalFold e y‖ ≤ ‖x - y‖ := by
  by_cases hx : 0 ≤ inner ℝ e x <;> by_cases hy : 0 ≤ inner ℝ e y
  · simp [normalFold, hx, hy]
  · simpa only [normalFold, ite_eq_left hx, ite_eq_right hy] using
      norm_sub_normalReflection_le e x y he hx (le_of_lt (lt_of_not_ge hy))
  · simpa only [normalFold, ite_eq_right hx, ite_eq_left hy, norm_sub_rev] using
      norm_sub_normalReflection_le e y x he hy (le_of_lt (lt_of_not_ge hx))
  · simp only [normalFold, ite_eq_right hx, ite_eq_right hy, ← map_sub, (normalReflection e).norm_map, le_refl]

omit [FiniteDimensional ℝ E] in
theorem normalFold_lipschitz (e : E) (he : ‖e‖ = 1) : LipschitzWith 1 (normalFold e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using normalFold_norm_sub_le e x y he

omit [FiniteDimensional ℝ E] in
theorem evenNormalExtension_holder (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hh : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α) (x y : E) :
    |f (normalFold e x) - f (normalFold e y)| ≤ H * ‖x - y‖ ^ α := by
  exact (hh _ (normalFold_nonneg e x he) _ (normalFold_nonneg e y he)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (normalFold_norm_sub_le e x y he) hα) hH)

end OAI.Analysis.PDE.Schauder
