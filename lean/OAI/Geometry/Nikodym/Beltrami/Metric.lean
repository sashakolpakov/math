import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The common denominator of spherical gnomonic and hyperbolic Klein
coordinates. Positive, zero and negative `κ` give the three space forms. -/
def beltramiDenominator (κ : ℝ) (x : E) : ℝ := 1 + κ * ‖x‖ ^ 2

/-- The actual space-form metric in straight-line (Beltrami) coordinates. -/
def beltramiMetric (κ : ℝ) (x u v : E) : ℝ :=
  (beltramiDenominator κ x * ⟪u,v⟫ - κ * ⟪x,u⟫ * ⟪x,v⟫) /
    beltramiDenominator κ x ^ 2

/-- Christoffel bilinear map for the metric above. -/
def beltramiChristoffel (κ : ℝ) (x u v : E) : E :=
  -(κ / beltramiDenominator κ x) • (⟪x,u⟫ • v + ⟪x,v⟫ • u)

theorem beltramiMetric_symmetric (κ : ℝ) (x u v : E) :
    beltramiMetric κ x u v = beltramiMetric κ x v u := by
  unfold beltramiMetric
  rw [real_inner_comm u v]
  ring

theorem beltramiChristoffel_symmetric (κ : ℝ) (x u v : E) :
    beltramiChristoffel κ x u v = beltramiChristoffel κ x v u := by
  simp only [beltramiChristoffel,add_comm]

omit [InnerProductSpace ℝ E] in
theorem beltramiDenominator_small {κ : ℝ} {x : E}
    (hx : |κ| * ‖x‖ ^ 2 ≤ 1/2) :
    1/2 ≤ beltramiDenominator κ x ∧ beltramiDenominator κ x ≤ 3/2 := by
  have h₁ := mul_le_mul_of_nonneg_right (neg_abs_le κ) (sq_nonneg ‖x‖)
  have h₂ := mul_le_mul_of_nonneg_right (le_abs_self κ) (sq_nonneg ‖x‖)
  unfold beltramiDenominator
  constructor <;> nlinarith

private theorem inner_sq_le (x v : E) : ⟪x,v⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
  have h : ‖⟪x,v⟫‖ ≤ ‖x‖ * ‖v‖ := norm_inner_le_norm x v
  rw [Real.norm_eq_abs] at h
  have hsq := sq_le_sq₀ (abs_nonneg ⟪x,v⟫) (mul_nonneg (norm_nonneg x) (norm_nonneg v)) |>.2 h
  simpa only [sq_abs,mul_pow] using hsq

/-- Uniform metric comparison on a fixed sufficiently small model chart.
The constants are explicit and work for every sign of the curvature. -/
theorem beltramiMetric_small_bounds {κ : ℝ} {x : E}
    (hx : |κ| * ‖x‖ ^ 2 ≤ 1/2) (v : E) :
    (1/8) * ‖v‖ ^ 2 ≤ beltramiMetric κ x v v ∧
      beltramiMetric κ x v v ≤ 8 * ‖v‖ ^ 2 := by
  obtain ⟨hq₁,hq₂⟩ := beltramiDenominator_small hx
  have hq : 0 < beltramiDenominator κ x := lt_of_lt_of_le (by norm_num) hq₁
  have hcs := inner_sq_le x v
  have hnum : (1/2) * ‖v‖ ^ 2 ≤
      beltramiDenominator κ x * ‖v‖ ^ 2 - κ * ⟪x,v⟫ ^ 2 ∧
      beltramiDenominator κ x * ‖v‖ ^ 2 - κ * ⟪x,v⟫ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    by_cases hk : 0 ≤ κ
    · have hcs' := mul_le_mul_of_nonneg_left hcs hk
      have hp := mul_nonneg hk (sq_nonneg ⟪x,v⟫)
      have hqv := mul_le_mul_of_nonneg_right hq₂ (sq_nonneg ‖v‖)
      dsimp [beltramiDenominator] at *
      constructor <;> nlinarith [sq_nonneg ‖v‖]
    · have hk' : κ ≤ 0 := le_of_not_ge hk
      have hcs' := mul_le_mul_of_nonpos_left hcs hk'
      have hp := mul_nonpos_of_nonpos_of_nonneg hk' (sq_nonneg ⟪x,v⟫)
      have hqv := mul_le_mul_of_nonneg_right hq₁ (sq_nonneg ‖v‖)
      dsimp [beltramiDenominator] at *
      constructor <;> nlinarith [sq_nonneg ‖v‖]
  have hsq₁ : 1/4 ≤ beltramiDenominator κ x ^ 2 := by nlinarith
  have hsq₂ : beltramiDenominator κ x ^ 2 ≤ 4 := by nlinarith
  unfold beltramiMetric
  rw [real_inner_self_eq_norm_sq]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hq)).2
    have hmul := mul_le_mul_of_nonneg_right hsq₂ (sq_nonneg ‖v‖)
    nlinarith [hnum.1]
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).2
    have hmul := mul_le_mul_of_nonneg_right hsq₁ (sq_nonneg ‖v‖)
    nlinarith [hnum.2]

theorem beltramiMetric_small_pos {κ : ℝ} {x v : E}
    (hx : |κ| * ‖x‖ ^ 2 ≤ 1/2) (hv : v ≠ 0) : 0 < beltramiMetric κ x v v := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    (beltramiMetric_small_bounds hx v).1

theorem beltramiMetric_zero (x u v : E) : beltramiMetric 0 x u v = ⟪u,v⟫ := by
  simp [beltramiMetric,beltramiDenominator]

end OAI.Geometry.Nikodym
