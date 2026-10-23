import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact wall arithmetic and the binomial entropy estimate

The factorial in the Barone--Basu binomial sum is essential.  Keeping it
machine-visible is what changes the naive base `N²` into a base proportional to
`N` when the ambient dimension is proportional to `N`.
-/

namespace StickKnots

/-- Number of unordered pairs of nonincident edges in an `N`-cycle.  It is
written as all unordered pairs minus the `N` adjacent pairs. -/
def nonincidentWallCount (N : ℕ) : ℕ := N.choose 2 - N

/-- Add one adjacent-edge wall for each vertex. -/
def wallCount (N : ℕ) : ℕ := nonincidentWallCount N + N

/-- Numerical slice-size expression used after the external affine-normalization
argument; this definition is not itself a geometric dimension theorem. -/
def affineSliceDim (N : ℕ) : ℕ := 3 * N - 12

theorem choose_two_ge_self {N : ℕ} (hN : 3 ≤ N) : N ≤ N.choose 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [show 3 + k = (k + 2) + 1 by omega, Nat.choose_succ_succ]
  simp only [Nat.choose_one_right]
  have hp : 0 < (k + 2).choose 2 := Nat.choose_pos (by omega)
  exact Nat.add_le_add_left hp (k + 2)

theorem wallCount_eq_choose_two {N : ℕ} (hN : 3 ≤ N) :
    wallCount N = N.choose 2 := by
  exact Nat.sub_add_cancel (choose_two_ge_self hN)

theorem twice_choose_two (N : ℕ) : 2 * N.choose 2 = N * (N - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd]

/-- The familiar exact cyclic count `N(N-3)/2`, stated without hiding
integrality behind rational arithmetic. -/
theorem twice_nonincidentWallCount {N : ℕ} (hN : 3 ≤ N) :
    2 * nonincidentWallCount N = N * (N - 3) := by
  have hadd : nonincidentWallCount N + N = N.choose 2 := by
    exact Nat.sub_add_cancel (choose_two_ge_self hN)
  have htwice := congrArg (fun x : ℕ ↦ 2 * x) hadd
  rw [mul_add, twice_choose_two] at htwice
  have hpred : N - 1 = (N - 3) + 2 := by omega
  rw [hpred, mul_add] at htwice
  have : 2 * nonincidentWallCount N + 2 * N = N * (N - 3) + 2 * N := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwice
  exact Nat.add_right_cancel this

theorem nonincidentWallCount_eq {N : ℕ} (hN : 3 ≤ N) :
    nonincidentWallCount N = N * (N - 3) / 2 := by
  exact Nat.eq_div_of_mul_eq_right two_ne_zero (twice_nonincidentWallCount hN)

theorem twice_wallCount {N : ℕ} (hN : 3 ≤ N) :
    2 * wallCount N = N * (N - 1) := by
  rw [wallCount_eq_choose_two hN, twice_choose_two]

theorem wallCount_eq {N : ℕ} (hN : 3 ≤ N) :
    wallCount N = N * (N - 1) / 2 := by
  rw [wallCount_eq_choose_two hN, Nat.choose_two_right]

theorem affineSliceDim_eq {N : ℕ} (hN : 4 ≤ N) :
    affineSliceDim N = 3 * (N - 4) := by
  unfold affineSliceDim
  omega

/-- At most `N-3` nonincident partners per edge, and two edges meet a changed
vertex.  This is the exact arithmetic behind the `2(N-3)` bounded-difference
constant in the projection paper. -/
abbrev AffectedCrossingSlots (N : ℕ) := Fin 2 × Fin (N - 3)

theorem card_affectedCrossingSlots (N : ℕ) :
    Fintype.card (AffectedCrossingSlots N) = 2 * (N - 3) := by
  simp [AffectedCrossingSlots]

/-- A concrete indexing type for directed nonincident edge pairs.  Reversing
the pair is free; hence its cardinal is twice the unordered wall count. -/
abbrev DirectedNonincidentSlots (N : ℕ) := Fin N × Fin (N - 3)

theorem card_directedNonincidentSlots (N : ℕ) :
    Fintype.card (DirectedNonincidentSlots N) = N * (N - 3) := by
  simp [DirectedNonincidentSlots]

theorem card_directed_eq_twice_walls {N : ℕ} (hN : 3 ≤ N) :
    Fintype.card (DirectedNonincidentSlots N) = 2 * nonincidentWallCount N := by
  rw [card_directedNonincidentSlots, twice_nonincidentWallCount hN]

private theorem choose_mono_to_half {n j m : ℕ}
    (hjm : j ≤ m) (hm : m ≤ n / 2) : n.choose j ≤ n.choose m := by
  induction m, hjm using Nat.le_induction with
  | base => rfl
  | succ m hjm ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem factorial_lower_three (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) / 3) ^ m ≤ (m.factorial : ℝ) := by
  have hsqrt : 1 ≤ √(2 * Real.pi * (m : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hbase : (m : ℝ) / 3 ≤ (m : ℝ) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1)
    exact Real.exp_one_lt_three.le
  calc
    ((m : ℝ) / 3) ^ m ≤ ((m : ℝ) / Real.exp 1) ^ m := by
      exact pow_le_pow_left₀ (by positivity) hbase m
    _ ≤ √(2 * Real.pi * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (m.factorial : ℝ) := Stirling.le_factorial_stirling m

private theorem choose_le_three_mul_div {n m : ℕ} (hm : 1 ≤ m) :
    (n.choose m : ℝ) ≤ ((3 * n : ℕ) : ℝ) ^ m / (m : ℝ) ^ m := by
  calc
    (n.choose m : ℝ) ≤ (n : ℝ) ^ m / (m.factorial : ℝ) :=
      Nat.choose_le_pow_div m n
    _ ≤ (n : ℝ) ^ m / (((m : ℝ) / 3) ^ m) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_lower_three m hm)
    _ = ((3 * n : ℕ) : ℝ) ^ m / (m : ℝ) ^ m := by
      push_cast
      rw [div_pow]
      field_simp
      all_goals ring

/-- The exact binomial estimate used after Barone--Basu.  The left side is
their characteristic `4^j * choose n j` partial sum.  The right side has base
`12 n / m`, not base `n`; this is the Lean-checked factorial saving.

For the knot application, `n = wallCount N + 1 = Theta(N²)` and
`m = affineSliceDim N = Theta(N)`, so the base is `O(N)`. -/
theorem weighted_partial_choose_le
    {n m : ℕ} (hm : 1 ≤ m) (hhalf : m ≤ n / 2) :
    ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ j * n.choose j
      ≤ (m + 1 : ℝ) * (((12 * n : ℕ) : ℝ) ^ m / (m : ℝ) ^ m) := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (4 : ℝ) ^ j * n.choose j ≤ (4 : ℝ) ^ m * n.choose m := by
    intro j hj
    have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
    have hp : (4 : ℝ) ^ j ≤ 4 ^ m := by
      exact pow_le_pow_right₀ (by norm_num) hjm
    have hcNat : n.choose j ≤ n.choose m := choose_mono_to_half hjm hhalf
    have hc : (n.choose j : ℝ) ≤ n.choose m := by exact_mod_cast hcNat
    exact mul_le_mul hp hc (by positivity) (by positivity)
  calc
    ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ j * n.choose j
        ≤ ∑ _j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * n.choose m := by
          exact Finset.sum_le_sum fun j hj ↦ hterm j hj
    _ = (m + 1 : ℝ) * ((4 : ℝ) ^ m * n.choose m) := by simp
    _ ≤ (m + 1 : ℝ) * ((4 : ℝ) ^ m *
          (((3 * n : ℕ) : ℝ) ^ m / (m : ℝ) ^ m)) := by
      gcongr
      exact choose_le_three_mul_div hm
    _ = (m + 1 : ℝ) * (((12 * n : ℕ) : ℝ) ^ m / (m : ℝ) ^ m) := by
      push_cast
      have hp : (4 : ℝ) ^ m * 3 ^ m = 12 ^ m := by
        rw [← mul_pow]
        norm_num
      rw [mul_pow, mul_pow, ← hp]
      ring

private theorem choose_two_linear_lower {N : ℕ} (hN : 5 ≤ N) :
    6 * N - 25 ≤ N.choose 2 := by
  rcases hN.eq_or_lt with rfl | hNgt
  · decide
  · have h6N : 6 ≤ N := by omega
    refine Nat.le_induction (by decide) (fun n h6n ih ↦ ?_) N h6N
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    change 6 * (n + 1) - 25 ≤ n + n.choose 2
    omega

/-- In the knot specialization the affine dimension lies in the lower half of
the Barone--Basu binomial sum. -/
theorem knot_parameters_half_range {N : ℕ} (hN : 5 ≤ N) :
    affineSliceDim N ≤ (wallCount N + 1) / 2 := by
  have hs : 6 * N - 25 ≤ wallCount N := by
    rw [wallCount_eq_choose_two (by omega)]
    exact choose_two_linear_lower hN
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  unfold affineSliceDim
  omega

/-- Arc-index cutoff for the earlier baseline lower bound retained for
comparison; the stronger word-family construction is in `StrongLower`. -/
def arcIndexBudget (N : ℕ) : ℕ := 2 * N / 3 + 1

/-- Exact budget arithmetic for the Huh--Oh conversion
`stick(K) ≤ 3(arc(K)-1)/2`: every knot of arc index at most
`floor(2N/3)+1` fits within `N` sticks. -/
theorem arcIndexBudget_fits (N : ℕ) :
    3 * (arcIndexBudget N - 1) ≤ 2 * N := by
  simpa [arcIndexBudget] using Nat.mul_div_le (2 * N) 3

/-- Factorial rank in the earlier Malyutin--Stupakov consequence
`floor((k+4)/11)!`, evaluated at `k = arcIndexBudget N`.  This is a baseline
lemma, not the strongest asymptotic developed in the manuscript. -/
def factorialRank (N : ℕ) : ℕ := (arcIndexBudget N + 4) / 11

/-- Upper floor-error control: `factorialRank N = 2N/33 + O(1)`. -/
theorem factorialRank_upper (N : ℕ) :
    33 * factorialRank N ≤ 2 * N + 15 := by
  unfold factorialRank arcIndexBudget
  omega

/-- Lower floor-error control: `factorialRank N = 2N/33 + O(1)`. -/
theorem factorialRank_lower (N : ℕ) :
    2 * N ≤ 33 * factorialRank N + 17 := by
  unfold factorialRank arcIndexBudget
  omega

theorem factorialRank_pos {N : ℕ} (hN : 9 ≤ N) : 1 ≤ factorialRank N := by
  unfold factorialRank arcIndexBudget
  omega

/-- Machine-checked power lower bound for the factorial in that baseline
consequence. -/
theorem factorialRank_factorial_lower {N : ℕ} (hN : 9 ≤ N) :
    (((factorialRank N : ℕ) : ℝ) / 3) ^ factorialRank N ≤
      ((factorialRank N).factorial : ℝ) :=
  factorial_lower_three (factorialRank N) (factorialRank_pos hN)

end StickKnots
