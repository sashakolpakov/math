import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryScalar

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

def coefficientAt (A R j : ℕ) : ℤ :=
  if h : j < R then solve A R R ⟨j, h⟩ else 0

theorem coefficientAt_eq (A R j : ℕ) :
    coefficientAt A R j = extendCoefficients (parityCoefficients (K := ℤ) A R) j := by
  simp [coefficientAt, extendCoefficients, solve_eq]

/-- The numeric loop uses only sign, powers, binomial coefficients, and a prefix sum. -/
def scalarSum (A R d h : ℕ) : ℤ :=
  (-1 : ℤ) ^ d * ∑ k ∈ Finset.range (R - d),
    coefficientAt A R (d + k) * 2 ^ (R - 1 - (d + k)) * (h.choose k : ℤ)

variable {r Q Δ : ℕ}

def scalarEntry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) : ℤ :=
  if Compatible i t u y then
    scalarSum A R (unchanged i t u y).card (transposed i t u y).card
  else 0

theorem scalarEntry_cast (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (scalarEntry i t A R u y : ℚ) =
      (LayoutNumerator.denominator R : ℚ) * matrixEntry i t R
        (fun j => (coefficientAt A R j : ℚ)) u y := by
  let a : ℕ → ℚ := fun j => (coefficientAt A R j : ℚ) * (2 : ℚ)⁻¹ ^ j
  have ha : (fun j => a j * (2 : ℚ) ^ j) =
      fun j => (coefficientAt A R j : ℚ) := by
    funext j
    dsimp [a]
    rw [mul_assoc, ← mul_pow]
    norm_num
  have he := matrixEntry_normalized (K := ℚ) (by norm_num) i t R a u y
  rw [ha] at he
  rw [he]
  by_cases hc : Compatible i t u y
  · simp only [scalarEntry, ite_eq_left hc, scalarSum, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_sum, Int.cast_ofNat, Int.cast_natCast]
    rw [mul_left_comm (LayoutNumerator.denominator R : ℚ)]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hj : (unchanged i t u y).card + k < R := by
      have hk' := Finset.mem_range.mp hk
      omega
    have hp := LayoutNumerator.pow_two_clear ℚ (by norm_num) R
      ((unchanged i t u y).card + k) hj
    simp only [LayoutNumerator.denominator, Int.cast_pow, Int.cast_ofNat]
    dsimp [a]
    rw [hp]
    ring
  · simp [scalarEntry, hc]

/-- Equality with the semantic integer numerator used in all rank and support proofs. -/
theorem scalarEntry_eq_entry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    scalarEntry i t A R u y = LayoutNumerator.entry i t A R u y := by
  have he := scalarEntry_cast i t A R u y
  have hc := LayoutNumerator.entry_cast ℚ (by norm_num) i t A R u y
  have hcoeff : (fun j => (coefficientAt A R j : ℚ)) =
      extendCoefficients (parityCoefficients (K := ℚ) A R) := by
    funext j
    rw [coefficientAt_eq, LayoutNumerator.extend_parityCoefficients_intCast]
  rw [hcoeff] at he
  exact_mod_cast he.trans hc.symm

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
