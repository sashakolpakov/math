import Mathlib

/-!
Scalar identities underlying Section `stein_square.tex`.
The integral below is the exact constant occurring after spatial Plancherel
and the change of variables `u = |ξ|²/r²` in the `p = 2` argument.
-/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory intervalIntegral

/-- The beta integral needed for Stein's square function. -/
theorem beta_integral {a : ℝ} (ha : -1 < a) :
    (∫ u : ℝ in (0 : ℝ)..1, u * (1 - u) ^ a) =
      1 / ((a + 1) * (a + 2)) := by
  have hs : (∫ u : ℝ in (0 : ℝ)..1, u * (1 - u) ^ a) =
      ∫ u : ℝ in (0 : ℝ)..1, (1 - u) * u ^ a := by
    simpa only [sub_zero, sub_self, sub_sub_cancel] using
      (integral_comp_sub_left (fun u : ℝ => u * (1 - u) ^ a) 1
        (a := (0 : ℝ)) (b := 1)).symm
  rw [hs]
  have he : (∫ u : ℝ in (0 : ℝ)..1, (1 - u) * u ^ a) =
      ∫ u : ℝ in (0 : ℝ)..1, (u ^ a - u ^ (a + 1)) := by
    apply integral_congr_Ioo_of_le zero_le_one
    intro u hu
    dsimp
    rw [Real.rpow_add_one (ne_of_gt hu.1)]
    ring
  rw [he, integral_sub (intervalIntegrable_rpow' ha)
    (intervalIntegrable_rpow' (by linarith : -1 < a + 1)),
    integral_rpow (Or.inl ha),
    integral_rpow (Or.inl (by linarith : -1 < a + 1))]
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : a + 1 + 1 ≠ 0 := by linarith
  simp only [Real.one_rpow, Real.zero_rpow h1, Real.zero_rpow h2, sub_zero]
  have h3 : a + 2 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ; ring

/-- Exact square of the `L²` operator constant in the source. -/
theorem square_function_constant {α : ℝ} (hα : 1 / 2 < α) :
    2 * α ^ 2 * (∫ u : ℝ in (0 : ℝ)..1, u * (1 - u) ^ (2 * α - 2)) =
      α / (2 * α - 1) := by
  rw [beta_integral (by linarith : -1 < 2 * α - 2)]
  have h1 : 2 * α - 1 ≠ 0 := by linarith
  have h2 : 2 * α - 2 + 1 ≠ 0 := by linarith
  have h3 : 2 * α - 2 + 2 ≠ 0 := by linarith
  rw [mul_one_div]
  apply (div_eq_div_iff (mul_ne_zero h2 h3) h1).2
  ring

/-- The summability threshold in the final shell decomposition. -/
theorem threshold_identity (n p : ℝ) :
    1 / 2 + max (n * (1 / 2 - 1 / p) - 1 / 2) 0 =
      max (1 / 2) (n * (1 / 2 - 1 / p)) := by
  rw [add_max, max_comm]
  congr 1 <;> ring

theorem shell_decay_positive_iff (n p α : ℝ) :
    0 < α - 1 / 2 - max (n * (1 / 2 - 1 / p) - 1 / 2) 0 ↔
      max (1 / 2) (n * (1 / 2 - 1 / p)) < α := by
  rw [← threshold_identity]
  constructor <;> intro h <;> linarith

/-- Exponential shell decay absorbs any real power of the dyadic index. -/
theorem summable_shell_weights {d : ℝ} (hd : 0 < d) (A : ℝ) :
    Summable (fun j : ℕ => (2 : ℝ) ^ (-(j : ℝ) * d) * (1 + (j : ℝ)) ^ A) := by
  obtain ⟨k, hk⟩ := exists_nat_gt A
  let r : ℝ := 2 ^ (-d)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase : Summable (fun j : ℕ => (j : ℝ) ^ k * r ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one k (r := r) hr
  have hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ k * r ^ (j + 1)) :=
    (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ k * r ^ j) 1).2 hbase
  have hmajor : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ k * r ^ j) := by
    convert hsum.mul_right r⁻¹ using 1
    ext j
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ; ring
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hmajor
  intro j
  have he : (2 : ℝ) ^ (-(j : ℝ) * d) = r ^ j := by
    rw [show -(j : ℝ) * d = (-d) * (j : ℝ) by ring]
    exact Real.rpow_mul_natCast (by norm_num) (-d) j
  rw [he, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hrpos) j)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le
    (by have := Nat.cast_nonneg (α := ℝ) j; linarith) hk.le

/-- Precisely the summability used at the end of the Stein square-function proof. -/
theorem summable_stein_shell_weights {n p α : ℝ}
    (hα : max (1 / 2) (n * (1 / 2 - 1 / p)) < α) (A : ℝ) :
    Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℝ) *
        (α - 1 / 2 - max (n * (1 / 2 - 1 / p) - 1 / 2) 0)) *
        (1 + (j : ℝ)) ^ A) :=
  summable_shell_weights ((shell_decay_positive_iff n p α).2 hα) A

end OAI.Analysis.Fourier.SquareFunction
