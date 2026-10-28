import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

namespace OAI.Algorithms

/-! Computable descending triangular solution for the original parity coefficients.
There are R coordinate updates, each scanning R potential upper entries.
No matrix inverse is executed. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

def target (A j : ℕ) : ℤ := (-1 : ℤ) ^ A * (-2 : ℤ) ^ j

def upperTail (A R : ℕ) (j : Fin R) (v : Fin R → ℤ) : ℤ :=
  ∑ k : Fin R, if j.val < k.val then
    (A.choose (k.val - j.val) : ℤ) * v k else 0

def solve (A R : ℕ) : ℕ → (Fin R → ℤ)
  | 0 => fun _ => 0
  | n + 1 =>
    let v := solve A R n
    if h : n < R then
      let j : Fin R := ⟨R - 1 - n, by omega⟩
      Function.update v j (target A j.val - upperTail A R j v)
    else v

theorem solve_processed (A R n : ℕ) (hn : n ≤ R) (j : Fin R)
    (hj : R - n ≤ j.val) :
    solve A R n j = parityCoefficients (K := ℤ) A R j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    have hnr : n < R := by omega
    have hnle : n ≤ R := by omega
    let i : Fin R := ⟨R - 1 - n, by omega⟩
    change (if h : n < R then
      Function.update (solve A R n) (⟨R - 1 - n, by omega⟩ : Fin R)
        (target A (R - 1 - n) -
          upperTail A R (⟨R - 1 - n, by omega⟩ : Fin R) (solve A R n))
      else solve A R n) j = _
    rw [dite_eq_left hnr]
    by_cases hji : j = i
    · rw [hji]
      dsimp [i]
      simp only [Function.update, dite_true]
      rw [parity_upper_recurrence A R i]
      congr 1
      unfold upperTail
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with hik
      · rw [ih hnle k (by dsimp [i] at hik; omega)]
      · rfl
    · simp only [Function.update, dite_eq_right (by simpa only [i] using hji)]
      apply ih hnle j
      have hne : j.val ≠ R - 1 - n := fun he => hji (Fin.ext he)
      omega

theorem solve_unprocessed (A R n : ℕ) (hn : n ≤ R) (j : Fin R)
    (hj : j.val < R - n) : solve A R n j = 0 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have hnr : n < R := by omega
    have hne : j ≠ (⟨R - 1 - n, by omega⟩ : Fin R) := by
      intro he
      have hev := congrArg Fin.val he
      simp only at hev
      omega
    simp only [solve, dite_eq_left hnr]
    simp only [Function.update, dite_eq_right hne]
    apply ih (by omega) j (by omega)

theorem solve_eq (A R : ℕ) :
    solve A R R = parityCoefficients (K := ℤ) A R := by
  funext j
  exact solve_processed A R R (by omega) j (by omega)

/-- Increasing coefficient order, suitable for a physical list buffer. -/
def coefficientList (A R : ℕ) : List ℤ := List.ofFn (solve A R R)

@[simp] theorem coefficientList_length (A R : ℕ) :
    (coefficientList A R).length = R := by simp [coefficientList]

theorem coefficientList_getElem (A R j : ℕ) (hj : j < R) :
    (coefficientList A R)[j]'(by simpa using hj) =
      parityCoefficients (K := ℤ) A R ⟨j, hj⟩ := by
  simp [coefficientList, solve_eq]

theorem solve_natAbs_le (A R Q n : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q)
    (hn : n ≤ R) (j : Fin R) :
    (solve A R n j).natAbs ≤ (4 * Q) ^ R := by
  by_cases hj : R - n ≤ j.val
  · rw [solve_processed A R n hn j hj]
    exact natAbs_parityCoefficients_le A R Q hAQ hQ j
  · rw [solve_unprocessed A R n hn j (by omega)]
    simp

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
