import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Reflection and the zero-trace Hölder extension at a flat boundary. -/

noncomputable section
open Set Metric InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def normalReflection (e : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ e)ᗮ.reflection

def normalProjection (e x : E) : E := x - inner ℝ e x • e

omit [FiniteDimensional ℝ E] in
theorem normalReflection_apply (e x : E) (he : ‖e‖ = 1) :
    normalReflection e x = x - (2 * inner ℝ e x) • e := by
  rw [normalReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  norm_num [← mul_smul, neg_sub]
  simp [two_smul, two_mul, add_smul]

omit [FiniteDimensional ℝ E] in
theorem inner_normalReflection (e x : E) (he : ‖e‖ = 1) :
    inner ℝ e (normalReflection e x) = -inner ℝ e x := by
  rw [normalReflection_apply e x he, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, he]
  ring

omit [FiniteDimensional ℝ E] in
theorem normalReflection_eq_self (e x : E) (he : ‖e‖ = 1)
    (hx : inner ℝ e x = 0) : normalReflection e x = x := by
  simp [normalReflection_apply e x he, hx]

omit [FiniteDimensional ℝ E] in
theorem inner_normalProjection (e x : E) (he : ‖e‖ = 1) :
    inner ℝ e (normalProjection e x) = 0 := by
  simp [normalProjection, inner_sub_right, inner_smul_right, he]

omit [FiniteDimensional ℝ E] in
theorem norm_sub_normalProjection (e x : E) (he : ‖e‖ = 1) :
    ‖x - normalProjection e x‖ = |inner ℝ e x| := by
  simp [normalProjection, norm_smul, he, Real.norm_eq_abs]

def oddNormalExtension (e : E) (f : E → ℝ) (x : E) : ℝ :=
  if 0 ≤ inner ℝ e x then f x else -f (normalReflection e x)

omit [FiniteDimensional ℝ E] in
theorem halfspace_value_le_height (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    {α H : ℝ} (_ : 0 ≤ H)
    (hzero : ∀ x, inner ℝ e x = 0 → f x = 0)
    (hHolder : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : E) (hx : 0 ≤ inner ℝ e x) : |f x| ≤ H * |inner ℝ e x| ^ α := by
  have hz := inner_normalProjection e x he
  simpa only [hzero _ hz, sub_zero, norm_sub_normalProjection e x he] using
    hHolder x hx (normalProjection e x) hz.ge

omit [FiniteDimensional ℝ E] in
theorem oddNormalExtension_abs_le_height (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    {α H : ℝ} (hH : 0 ≤ H)
    (hzero : ∀ x, inner ℝ e x = 0 → f x = 0)
    (hHolder : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : E) :
    |oddNormalExtension e f x| ≤ H * |inner ℝ e x| ^ α := by
  by_cases hx : 0 ≤ inner ℝ e x
  · simpa only [oddNormalExtension, ite_eq_left hx] using halfspace_value_le_height e he f hH hzero hHolder x hx
  · have hr : 0 ≤ inner ℝ e (normalReflection e x) := by
      rw [inner_normalReflection e x he]
      linarith
    simpa only [oddNormalExtension, ite_eq_right hx, abs_neg, inner_normalReflection e x he] using
      halfspace_value_le_height e he f hH hzero hHolder (normalReflection e x) hr

omit [FiniteDimensional ℝ E] in
theorem opposite_heights_le_dist (e : E) (he : ‖e‖ = 1) (x y : E)
    (hx : 0 ≤ inner ℝ e x) (hy : inner ℝ e y ≤ 0) :
    |inner ℝ e x| ≤ ‖x - y‖ ∧ |inner ℝ e y| ≤ ‖x - y‖ := by
  have h := abs_real_inner_le_norm e (x - y)
  rw [he, one_mul, inner_sub_right, abs_of_nonneg (sub_nonneg.mpr (hy.trans hx))] at h
  rw [abs_of_nonneg hx, abs_of_nonpos hy]
  constructor <;> linarith

omit [FiniteDimensional ℝ E] in
theorem oddNormalExtension_holder (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hzero : ∀ x, inner ℝ e x = 0 → f x = 0)
    (hHolder : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α) (x y : E) :
    |oddNormalExtension e f x - oddNormalExtension e f y| ≤ 2 * H * ‖x - y‖ ^ α := by
  have hcross (a b : E) (ha : 0 ≤ inner ℝ e a) (hb : inner ℝ e b ≤ 0) :
      |oddNormalExtension e f a - oddNormalExtension e f b| ≤ 2 * H * ‖a - b‖ ^ α := by
    obtain ⟨hax, hbx⟩ := opposite_heights_le_dist e he a b ha hb
    have ha' := (oddNormalExtension_abs_le_height e he f hH hzero hHolder a).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hax hα) hH)
    have hb' := (oddNormalExtension_abs_le_height e he f hH hzero hHolder b).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hbx hα) hH)
    have ht := abs_sub (oddNormalExtension e f a) (oddNormalExtension e f b)
    linarith
  by_cases hx : 0 ≤ inner ℝ e x <;> by_cases hy : 0 ≤ inner ℝ e y
  · simp only [oddNormalExtension, ite_eq_left hx, ite_eq_left hy]
    exact (hHolder x hx y hy).trans (by nlinarith [mul_nonneg hH (Real.rpow_nonneg (norm_nonneg (x-y)) α)])
  · exact hcross x y hx (le_of_lt (lt_of_not_ge hy))
  · simpa only [abs_sub_comm, norm_sub_rev] using hcross y x hy (le_of_lt (lt_of_not_ge hx))
  · have hrx : 0 ≤ inner ℝ e (normalReflection e x) := by rw [inner_normalReflection e x he]; linarith
    have hry : 0 ≤ inner ℝ e (normalReflection e y) := by rw [inner_normalReflection e y he]; linarith
    have hh := hHolder (normalReflection e x) hrx (normalReflection e y) hry
    rw [← map_sub, (normalReflection e).norm_map] at hh
    simp only [oddNormalExtension, ite_eq_right hx, ite_eq_right hy, neg_sub_neg, abs_sub_comm]
    exact hh.trans (by nlinarith [mul_nonneg hH (Real.rpow_nonneg (norm_nonneg (x-y)) α)])

end OAI.Analysis.PDE.Schauder
