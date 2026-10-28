import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationBudgetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpSmallInputs
import OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval

namespace OAI.Algorithms

/-!
# The directly computed dyadic parameter schedule

The width k and control constant T are fixed before the input size varies.
Only admissibility needs the certificate Control k T; all numerical fields
are computed by explicit natural-number formulas.
-/

namespace SubexponentialSAT.DyadicSchedule

open SubexpPackingParameters
open Filter

def M (T n : ℕ) : ℕ := SparsificationBudgetProgram.dyadicM T (s n)

theorem M_ge_two (T n : ℕ) : 2 ≤ M T n :=
  SparsificationBudgetProgram.dyadicM_ge_two T (s n)

theorem M_admissible (k T : ℕ) (hk : 2 ≤ k)
    (hT : SparsificationBudgetProgram.Control k T) (n : ℕ) (hn : GoodInput n) :
    SparsificationBudget.ReciprocalAdmissible k (s n) (M T n) :=
  hT.admissible hk (s n) (goodInput_s_pos hn)

theorem M_quadratic_bound (T n : ℕ) (hn : GoodInput n) :
    M T n ≤ (4 * 2 ^ T) * s n ^ 2 :=
  SparsificationBudgetProgram.dyadicM_quadratic_bound T (s n) (goodInput_s_pos hn)

def B (k T n : ℕ) : ℕ := SparsificationConstants.occurrenceCap (M T n) k

def delta (k T n : ℕ) : ℕ := 1 + ell n * B k T n

theorem delta_pos (k T n : ℕ) : 0 < delta k T n := by
  simp only [delta]
  omega

def tau (n : ℕ) : ℚ := 1 / (s n : ℚ)

def Q (n : ℕ) : ℕ := SubexpParameters.sizeQ (p n)

def R (k T n : ℕ) : ℕ := SubexpParameters.degreeR (p n) k (delta k T n)

def N (k T n : ℕ) : ℕ := SubexpParameters.blockSize (s n) (p n) (delta k T n)

def Dstar (k T n : ℕ) : ℕ := s n ^ 2 * N k T n ^ 3 * (1 + delta k T n * k)

theorem tau_pos {n : ℕ} (hn : GoodInput n) : 0 < tau n := by
  unfold tau
  exact one_div_pos.mpr (Nat.cast_pos.mpr (goodInput_s_pos hn))

theorem tau_le_half {n : ℕ} (hn : GoodInput n) : tau n ≤ 1 / 2 := by
  have hs : (2 : ℚ) ≤ s n := by
    exact_mod_cast (show 2 ≤ s n by have h := hn; unfold GoodInput at h; omega)
  exact one_div_le_one_div_of_le (by norm_num) hs

theorem Q_pos (n : ℕ) : 0 < Q n := by
  have hp : 2 ≤ p n := le_of_lt (p_gt_two n)
  have hh := Nat.pow_le_pow_left hp 4
  change 0 < p n ^ 4 - 1
  norm_num at hh
  omega

/-- Coefficient and degree are chosen before the input size. -/
theorem exists_occurrence_bound (k T : ℕ) :
    ∃ C d : ℕ, ∀ n, GoodInput n → B k T n ≤ C * (s n + 1) ^ d := by
  obtain ⟨C, d, h⟩ := SparsificationBudgetProgram.dyadicOccurrenceCap_polynomialBound T k
  refine ⟨C, d, ?_⟩
  intro n hn
  have hs : 2 ≤ s n := by unfold GoodInput at hn; omega
  exact (h (s n) hs).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_succ _) d))

/-- The packing factor increases the fixed polynomial degree by one. -/
theorem exists_incidence_bound (k T : ℕ) :
    ∃ C d : ℕ, ∀ n, GoodInput n → delta k T n ≤ C * (s n + 1) ^ d := by
  obtain ⟨C, d, h⟩ := exists_occurrence_bound k T
  refine ⟨C + 1, d + 1, ?_⟩
  intro n hn
  have hell : ell n ≤ s n + 1 := (u_le_s n).trans (Nat.le_succ _)
  have hp : 1 ≤ (s n + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  calc
    delta k T n = 1 + ell n * B k T n := rfl
    _ ≤ 1 + (s n + 1) * (C * (s n + 1) ^ d) := by
      gcongr
      exact h n hn
    _ = 1 + C * (s n + 1) ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ (C + 1) * (s n + 1) ^ (d + 1) := by nlinarith

def checks (k T : ℕ) : SubexpSmallInputs.CheckData :=
  SubexpSmallInputs.actualChecks k (delta k T)

def Ready (k T n : ℕ) : Prop := SubexpSmallInputs.Ready (checks k T) n

instance (k T n : ℕ) : Decidable (Ready k T n) :=
  inferInstanceAs (Decidable (SubexpSmallInputs.Ready (checks k T) n))

def intervalStart (k T n : ℕ) : ℕ :=
  Subexp.TailInterval.intervalStart (r n) (Q n) (R k T n)

end SubexponentialSAT.DyadicSchedule

end OAI.Algorithms
