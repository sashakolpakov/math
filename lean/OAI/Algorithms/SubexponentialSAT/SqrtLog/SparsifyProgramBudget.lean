import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgramInputs
import OAI.Algorithms.SubexponentialSAT.DyadicNodeBudget

namespace OAI.Algorithms

/-!
# Polynomial overhead around the actual dyadic masked search

The envelope keeps initialization, the fixed-width scan, input encoding,
and the final quadratic node overhead outside the masked-loop budget. The
square is absorbed into the varying polynomial exponent before converting
to a subexponential bound.
-/

namespace SubexponentialSAT.SqrtLog.SparsifyProgram

open Filter Asymptotic SparsificationConstants
open DyadicMaskedSearchBounds

def stageCoefficient (k T : ℕ) : ℕ :=
  (2 * k + 20) * (thresholdCoefficient k T + 1) +
    256 * (thresholdCoefficient k T + 1) ^ 3 + 16

def overheadCoefficient (k T : ℕ) : ℕ :=
  100000 + (k + 1) * (stageCoefficient k T + 10)

/-- `H` is a fixed coefficient for the concrete surrounding instructions. -/
def budget (k T H n m : ℕ) : ℕ :=
  let r := threshold k T n
  let L := localSize n m r k
  k * sourceBudget k m r (callbackCoefficient k T * L ^ 24) + H * L ^ 6

def exponent (k T n : ℕ) : ℕ :=
  2 * (searchDegree k 24 (threshold k T n) + 1) + 1

theorem sourceBudget_mono {k m r R c C : ℕ} (hr : r ≤ R) (hc : c ≤ C) :
    sourceBudget k m r c ≤ sourceBudget k m R C := by
  have hp : (2 * (m + 1)) ^ r ≤ (2 * (m + 1)) ^ R :=
    Nat.pow_le_pow_right (by omega) hr
  have hrow := Nat.mul_le_mul_right (DyadicWidth.width m) hr
  have hcounter : c + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 ≤
      C + 14 * (k + R * DyadicWidth.width m) + 14 * (R + 1) + 12 := by omega
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hcounter) 3


theorem threshold_eventually_le_n (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, threshold k T n ≤ n :=
  Asymptotic.eventually_polynomial_schedule_le_n _
    (SparsificationBudgetProgram.dyadicThresholdCap_polynomialBound T k)

theorem eventually_budget_le_power (k T H : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ (2 * n + 1) ^ k →
      budget k T H n m ≤
        (n + 1) ^ (searchDegree k 24 (threshold k T n) + 1) := by
  filter_upwards [threshold_eventually_le_n k T, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop k, eventually_ge_atTop (callbackCoefficient k T + 54),
    eventually_ge_atTop (k + H)] with n hr hn hk hC hH
  intro m hm
  let L := localSize n m (threshold k T n) k
  let e := searchDegree k 24 (threshold k T n)
  have hs : sourceBudget k m (threshold k T n)
      (callbackCoefficient k T * L ^ 24) ≤ (n + 1) ^ e :=
    sourceBudget_le_power hn hk (by omega) hr hm (Nat.le_refl _)
  have hlocal : L ≤ (n + 1) ^ (2 * k + 3) := localSize_le_power hn hk hr hm
  have h6e : (2 * k + 3) * 6 ≤ e := by dsimp [e, searchDegree]; omega
  have h6 : L ^ 6 ≤ (n + 1) ^ e := by
    calc
      _ ≤ ((n + 1) ^ (2 * k + 3)) ^ 6 := Nat.pow_le_pow_left hlocal 6
      _ = (n + 1) ^ ((2 * k + 3) * 6) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) h6e
  change k * sourceBudget k m (threshold k T n)
    (callbackCoefficient k T * L ^ 24) + H * L ^ 6 ≤ (n + 1) ^ (e + 1)
  calc
    _ ≤ k * (n + 1) ^ e + H * (n + 1) ^ e :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hs) (Nat.mul_le_mul_left _ h6)
    _ = (k + H) * (n + 1) ^ e := by ring
    _ ≤ (n + 1) * (n + 1) ^ e := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [pow_succ]; ring

/-- The fixed quadratic finish and worklist-update coefficient is charged. -/
theorem eventually_squared_budget_le_power (k T H : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ (2 * n + 1) ^ k →
      1001000 * (budget k T H n m) ^ 2 ≤ (n + 1) ^ exponent k T n := by
  filter_upwards [eventually_budget_le_power k T H,
    eventually_ge_atTop (1001000 : ℕ)] with n hn hC
  intro m hm
  calc
    _ ≤ (n + 1) * ((n + 1) ^ (searchDegree k 24 (threshold k T n) + 1)) ^ 2 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (hn m hm) 2)
    _ = _ := by rw [← pow_mul, ← pow_succ']; congr 1; unfold exponent; omega

theorem exponent_polynomialBound (k T : ℕ) :
    PolynomialBound (fun s => 2 * (searchDegree k 24
      (SparsificationBudget.thresholdCap (SparsificationBudgetProgram.dyadicM T s) k) + 1) + 1) :=
  ((polynomialBound_const 2).mul
    ((searchDegree_polynomialBound k T 24).add (polynomialBound_const 1))).add
      (polynomialBound_const 1)

theorem exists_exponent_power (k T : ℕ) :
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop, exponent k T n ≤ (s n + 2) ^ q := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power
    (exponent_polynomialBound k T)
  exact ⟨q, Filter.Eventually.of_forall (fun n => hq (s n))⟩

/-- A single exponent, fixed before the input size, covers the actual
quadratic overhead once its explicit local envelope has been established. -/
theorem eventually_squared_budget_le_closed_power (k T H : ℕ) :
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ (2 * n + 1) ^ k →
      1001000 * (budget k T H n m) ^ 2 ≤ (n + 1) ^ ((s n + 2) ^ q) := by
  obtain ⟨q, hq⟩ := exists_exponent_power k T
  refine ⟨q, ?_⟩
  filter_upwards [eventually_squared_budget_le_power k T H, hq] with n hn hq
  intro m hm
  exact (hn m hm).trans (Nat.pow_le_pow_right (by omega) hq)

theorem exponentPower_subexponential (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, (((n + 1) ^ exponent k T n : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Statement.runtimeScale n := by
  obtain ⟨q, hq⟩ := exists_exponent_power k T
  have he : ∀ᶠ n : ℕ in atTop, (exponent k T n : ℝ) ≤
      (1 : ℝ) * ((s n : ℝ) + 2) ^ q := by
    filter_upwards [hq] with n hn
    simp only [one_mul]
    exact_mod_cast hn
  exact Asymptotic.eventually_variable_search_target (exponent k T) q (by norm_num) he

theorem eventually_squared_budget_subexponential (k T H : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ (2 * n + 1) ^ k →
      ((1001000 * (budget k T H n m) ^ 2 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ Statement.runtimeScale n := by
  filter_upwards [eventually_squared_budget_le_power k T H,
    exponentPower_subexponential k T] with n hn he
  intro m hm
  exact (Nat.cast_le.mpr (hn m hm)).trans he

end SubexponentialSAT.SqrtLog.SparsifyProgram

end OAI.Algorithms
