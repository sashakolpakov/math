import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Section 6: real exponent arithmetic

These are inequalities of actual real powers. They do not themselves establish
that a program runs within any of these bounds. The fixed multiplicative factor
depends on p and is independent of the Boolean input size n.
-/

namespace SubexponentialSAT.ExponentArithmetic

noncomputable section

/-- The real base-two logarithm used in the field-to-Boolean conversion. -/
def log2 (p : ℝ) : ℝ := Real.log p / Real.log 2

/-- The coefficient in the exponent before rounding up to 0.79. -/
def leafCoefficient (ell : ℝ) : ℝ :=
  3 * (ell + 1) / (4 * ell) + 128 / ell

/-- The explicit fixed factor due to replacing D = ceil (n/ell) by n/ell+1. -/
def fixedFactor (p : ℝ) : ℝ :=
  p ^ (3 / 4 : ℝ) * (2 : ℝ) ^ (128 : ℝ)

/-- The exponential part of the field-variable cost in Section 6. -/
def fieldCost (p D : ℝ) : ℝ :=
  p ^ (3 * D / 4) * (2 : ℝ) ^ (128 * D)

/-- Base-two exponent per field variable. -/
def fieldCoefficient (p : ℝ) : ℝ := 3 / 4 * log2 p + 128

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem log2_nonneg {p : ℝ} (hp : 1 ≤ p) : 0 ≤ log2 p :=
  div_nonneg (Real.log_nonneg hp) log_two_pos.le

theorem fieldCoefficient_nonneg {p : ℝ} (hp : 1 ≤ p) :
    0 ≤ fieldCoefficient p := by
  unfold fieldCoefficient
  have h := log2_nonneg hp
  linarith

theorem fixedFactor_pos {p : ℝ} (hp : 0 < p) : 0 < fixedFactor p :=
  mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos (by norm_num) _)

theorem leafCoefficient_eq {ell : ℝ} (hell : ell ≠ 0) :
    leafCoefficient ell = 3 / 4 + (515 / 4) / ell := by
  unfold leafCoefficient
  field_simp
  ring

/-- The exact worst-case coefficient allowed by ell ≥ 4096. -/
theorem leafCoefficient_le_exact {ell : ℝ} (hell : 4096 ≤ ell) :
    leafCoefficient ell ≤ 12803 / 16384 := by
  have hellpos : 0 < ell := by linarith
  rw [leafCoefficient_eq (ne_of_gt hellpos)]
  have hdiv : (515 / 4 : ℝ) / ell ≤ 515 / 16384 := by
    apply (div_le_iff₀ hellpos).2
    linarith
  linarith

theorem leafCoefficient_lt_079 {ell : ℝ} (hell : 4096 ≤ ell) :
    leafCoefficient ell < 79 / 100 := by
  have h := leafCoefficient_le_exact hell
  linarith

theorem leafCoefficient_lt_079_nat {ell : ℕ} (hell : 4096 ≤ ell) :
    leafCoefficient (ell : ℝ) < 79 / 100 :=
  leafCoefficient_lt_079 (by exact_mod_cast hell)

theorem rounded_exponent_sum :
    (79 / 100 : ℝ) + 1 / 32 = 657 / 800 := by norm_num

theorem rounded_exponent_lt_09 :
    (79 / 100 : ℝ) + 1 / 32 < 9 / 10 := by norm_num

theorem leaf_plus_sparsification_lt_09 {ell : ℝ} (hell : 4096 ≤ ell) :
    leafCoefficient ell + 1 / 32 < 9 / 10 := by
  have h := leafCoefficient_lt_079 hell
  linarith

/-- Natural ceiling, cast back into the reals, has the required additive-one bound. -/
theorem ceil_div_le_add_one {n ell : ℝ} (hn : 0 ≤ n) (hell : 0 < ell) :
    (⌈n / ell⌉₊ : ℝ) ≤ n / ell + 1 :=
  (Nat.ceil_lt_add_one (div_nonneg hn hell.le)).le

theorem log2_lt_floor_add_one (p : ℝ) :
    log2 p < (⌊log2 p⌋₊ : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem fieldCost_eq_two_rpow {p : ℝ} (hp : 0 < p) (D : ℝ) :
    fieldCost p D = (2 : ℝ) ^ (fieldCoefficient p * D) := by
  unfold fieldCost fieldCoefficient log2
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  congr 1
  field_simp

theorem fixedFactor_eq_two_rpow {p : ℝ} (hp : 0 < p) :
    fixedFactor p = (2 : ℝ) ^ fieldCoefficient p := by
  simpa [fieldCost, fixedFactor] using fieldCost_eq_two_rpow hp 1

theorem fieldCoefficient_div_le_leafCoefficient {p ell : ℝ}
    (hell : 0 < ell) (hlog : log2 p ≤ ell + 1) :
    fieldCoefficient p / ell ≤ leafCoefficient ell := by
  unfold fieldCoefficient leafCoefficient
  have hnum : (3 / 4 : ℝ) * log2 p + 128 ≤ 3 / 4 * (ell + 1) + 128 := by
    linarith
  have h := div_le_div_of_nonneg_right hnum hell.le
  convert h using 1
  field_simp

/-- Actual real-power bound, with the ceiling and logarithm bounds as explicit
arithmetic assumptions. Its multiplicative factor depends only on p. -/
theorem fieldCost_le_fixedFactor {p n ell D : ℝ}
    (hp : 1 ≤ p) (hn : 0 ≤ n) (hell : 0 < ell)
    (hD : D ≤ n / ell + 1) (hlog : log2 p ≤ ell + 1) :
    fieldCost p D ≤ fixedFactor p * (2 : ℝ) ^ (leafCoefficient ell * n) := by
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  rw [fieldCost_eq_two_rpow hppos, fixedFactor_eq_two_rpow hppos,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdim := mul_le_mul_of_nonneg_left hD (fieldCoefficient_nonneg hp)
  have hcoefficient := mul_le_mul_of_nonneg_right
    (fieldCoefficient_div_le_leafCoefficient hell hlog) hn
  calc
    fieldCoefficient p * D ≤ fieldCoefficient p * (n / ell + 1) := hdim
    _ = fieldCoefficient p + fieldCoefficient p / ell * n := by ring
    _ ≤ fieldCoefficient p + leafCoefficient ell * n :=
      add_le_add_right hcoefficient (fieldCoefficient p)

/-- The advertised per-leaf exponential bound once the bit capacity is large. -/
theorem fieldCost_le_079 {p n ell D : ℝ}
    (hp : 1 ≤ p) (hn : 0 ≤ n) (hell : 4096 ≤ ell)
    (hD : D ≤ n / ell + 1) (hlog : log2 p ≤ ell + 1) :
    fieldCost p D ≤ fixedFactor p * (2 : ℝ) ^ ((79 / 100 : ℝ) * n) := by
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  calc
    fieldCost p D ≤ fixedFactor p * (2 : ℝ) ^ (leafCoefficient ell * n) :=
      fieldCost_le_fixedFactor hp hn (by linarith) hD hlog
    _ ≤ fixedFactor p * (2 : ℝ) ^ ((79 / 100 : ℝ) * n) := by
      apply mul_le_mul_of_nonneg_left _ (fixedFactor_pos hppos).le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right (leafCoefficient_lt_079 hell).le hn

/-- Multiplying the per-leaf exponential factor by the sparsification factor
leaves room below the theorem's exponent 0.9. -/
theorem sparsification_times_leaf_le_09 {n : ℝ} (hn : 0 ≤ n) :
    (2 : ℝ) ^ (n / 32) * (2 : ℝ) ^ ((79 / 100 : ℝ) * n) ≤
      (2 : ℝ) ^ ((9 / 10 : ℝ) * n) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

/-- The combined numerical bound. Any actual runtime bound by the left-hand
side, including its polynomial overhead, is a separate algorithmic obligation. -/
theorem combinedCost_le_09 {p n ell D : ℝ}
    (hp : 1 ≤ p) (hn : 0 ≤ n) (hell : 4096 ≤ ell)
    (hD : D ≤ n / ell + 1) (hlog : log2 p ≤ ell + 1) :
    (2 : ℝ) ^ (n / 32) * fieldCost p D ≤
      fixedFactor p * (2 : ℝ) ^ ((9 / 10 : ℝ) * n) := by
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  calc
    (2 : ℝ) ^ (n / 32) * fieldCost p D ≤
        (2 : ℝ) ^ (n / 32) *
          (fixedFactor p * (2 : ℝ) ^ ((79 / 100 : ℝ) * n)) :=
      mul_le_mul_of_nonneg_left (fieldCost_le_079 hp hn hell hD hlog)
        (Real.rpow_nonneg (by norm_num) _)
    _ = fixedFactor p *
        ((2 : ℝ) ^ (n / 32) * (2 : ℝ) ^ ((79 / 100 : ℝ) * n)) := by ring
    _ ≤ fixedFactor p * (2 : ℝ) ^ ((9 / 10 : ℝ) * n) :=
      mul_le_mul_of_nonneg_left (sparsification_times_leaf_le_09 hn)
        (fixedFactor_pos hppos).le

/-- Per-leaf bound after substituting the actual natural floor and ceiling.
There are no independently assumed rounding or logarithm estimates here. -/
theorem packed_fieldCost_le_079 {p : ℝ} (hp : 1 ≤ p)
    (hell : 4096 ≤ ⌊log2 p⌋₊) (n : ℕ) :
    fieldCost p (⌈(n : ℝ) / (⌊log2 p⌋₊ : ℝ)⌉₊ : ℝ) ≤
      fixedFactor p * (2 : ℝ) ^ ((79 / 100 : ℝ) * (n : ℝ)) := by
  have hellreal : (4096 : ℝ) ≤ (⌊log2 p⌋₊ : ℝ) := by exact_mod_cast hell
  apply fieldCost_le_079 hp (Nat.cast_nonneg _) hellreal
  · exact ceil_div_le_add_one (Nat.cast_nonneg _) (by linarith)
  · exact (log2_lt_floor_add_one p).le

/-- Section 6's combined bound with the actual packing parameters. -/
theorem packed_combinedCost_le_09 {p : ℝ} (hp : 1 ≤ p)
    (hell : 4096 ≤ ⌊log2 p⌋₊) (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 32) *
        fieldCost p (⌈(n : ℝ) / (⌊log2 p⌋₊ : ℝ)⌉₊ : ℝ) ≤
      fixedFactor p * (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ)) := by
  have hellreal : (4096 : ℝ) ≤ (⌊log2 p⌋₊ : ℝ) := by exact_mod_cast hell
  apply combinedCost_le_09 hp (Nat.cast_nonneg _) hellreal
  · exact ceil_div_le_add_one (Nat.cast_nonneg _) (by linarith)
  · exact (log2_lt_floor_add_one p).le

/-- On the bounded brute-force range, the remaining factor is independent of n. -/
theorem bruteForce_le_fixedFactor {n ell Dstar : ℝ} (hn : n ≤ ell * Dstar) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ ((1 / 10 : ℝ) * ell * Dstar) *
      (2 : ℝ) ^ ((9 / 10 : ℝ) * n) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

end

end SubexponentialSAT.ExponentArithmetic

end OAI.Algorithms
