import Mathlib

/-! # Quadratic Newton -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.QuadraticNewton

noncomputable section

/-! A fixed-derivative Newton map is a contraction near a unit-valued
approximate square root in an ultrametric field of odd residue characteristic. -/

open scoped Classical

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

def quadraticNewton (a c x : K) : K := x - (x ^ 2 - c) / (2 * a)

omit [IsUltrametricDist K] in
theorem quadraticNewton_difference (a c x y : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    quadraticNewton a c x - quadraticNewton a c y =
      -(x - y) * ((x - a) + (y - a)) / (2 * a) := by
  unfold quadraticNewton
  field_simp
  ring

theorem quadraticNewton_norm_difference (a c : K) (ha : ‖a‖ = 1) (h2 : ‖(2 : K)‖ = 1)
    {r : ℝ} {x y : K} (hx : ‖x - a‖ ≤ r) (hy : ‖y - a‖ ≤ r) :
    ‖quadraticNewton a c x - quadraticNewton a c y‖ ≤ r * ‖x - y‖ := by
  have ha₀ : a ≠ 0 := by intro h; simp [h] at ha
  have h2₀ : (2 : K) ≠ 0 := by intro h; simp [h] at h2
  rw [quadraticNewton_difference a c x y ha₀ h2₀, norm_div, norm_mul, norm_neg,
    norm_mul, ha, h2, mul_one, div_one]
  calc
    ‖x - y‖ * ‖(x - a) + (y - a)‖ ≤ ‖x - y‖ * r :=
      mul_le_mul_of_nonneg_left
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)) (norm_nonneg _)
    _ = r * ‖x - y‖ := mul_comm _ _

omit [IsUltrametricDist K] in
theorem quadraticNewton_norm_step (a c : K) (ha : ‖a‖ = 1) (h2 : ‖(2 : K)‖ = 1) :
    ‖quadraticNewton a c a - a‖ = ‖a ^ 2 - c‖ := by
  have he : quadraticNewton a c a - a = -(a ^ 2 - c) / (2 * a) := by
    unfold quadraticNewton
    rw [neg_div]
    abel
  rw [he, norm_div, norm_neg, norm_mul, ha, h2, mul_one, div_one]

theorem quadraticNewton_maps_ball (a c : K) (ha : ‖a‖ = 1) (h2 : ‖(2 : K)‖ = 1)
    (herr : ‖a ^ 2 - c‖ < 1) :
    Set.MapsTo (quadraticNewton a c) {x | ‖x - a‖ ≤ ‖a ^ 2 - c‖}
      {x | ‖x - a‖ ≤ ‖a ^ 2 - c‖} := by
  intro x hx
  have hdiff := quadraticNewton_norm_difference a c ha h2 (x := x) (y := a) hx
    (by simpa only [sub_self, norm_zero] using norm_nonneg (a ^ 2 - c))
  have hbound : ‖quadraticNewton a c x - quadraticNewton a c a‖ ≤ ‖a ^ 2 - c‖ := by
    exact hdiff.trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans
      (mul_le_of_le_one_right (norm_nonneg _) herr.le))
  change ‖quadraticNewton a c x - a‖ ≤ ‖a ^ 2 - c‖
  have he : quadraticNewton a c x - a =
      (quadraticNewton a c x - quadraticNewton a c a) + (quadraticNewton a c a - a) := by abel
  rw [he]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le hbound (le_of_eq (quadraticNewton_norm_step a c ha h2)))

end

end OAI.NumberTheory.Quaternion.Arithmetic.QuadraticNewton
