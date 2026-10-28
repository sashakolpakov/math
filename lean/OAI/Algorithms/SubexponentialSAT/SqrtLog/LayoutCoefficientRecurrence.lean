import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

namespace OAI.Algorithms

/-! A positive Pascal-prefix cache for the original parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open Matrix SubexponentialSAT.BinomialInterpolation

/-- Unsigned coefficients, indexed by translation and distance from the top. -/
def H : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | A + 1, m + 1 => H A (m + 1) + 2 * H (A + 1) m
termination_by A m => (A, m)

@[simp] theorem H_zero (m : ℕ) : H 0 m = 1 := by rw [H]
@[simp] theorem H_zero_right (A : ℕ) : H A 0 = 1 := by cases A <;> rw [H]
theorem H_succ_succ (A m : ℕ) :
    H (A + 1) (m + 1) = H A (m + 1) + 2 * H (A + 1) m := by rw [H]

def shift (R : ℕ) : Matrix (Fin R) (Fin R) ℤ :=
  fun j k => if j.val + 1 = k.val then 1 else 0

theorem shift_mulVec (R : ℕ) (v : Fin R → ℤ) (j : Fin R) :
    (shift R *ᵥ v) j = if h : j.val + 1 < R then v ⟨j.val + 1, h⟩ else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, shift]
  split_ifs with h
  · let k : Fin R := ⟨j.val + 1, h⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b hb hbk
      have hne : j.val + 1 ≠ b.val := by
        intro he
        apply hbk
        exact Fin.ext he.symm
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    have hne : j.val + 1 ≠ b.val := by omega
    simp [hne]

theorem binomial_succ (A R : ℕ) :
    SubexponentialSAT.BinomialMatrix.B ℤ (A + 1) R =
      SubexponentialSAT.BinomialMatrix.B ℤ A R * (1 + shift R) := by
  classical
  rw [Matrix.mul_add, Matrix.mul_one]
  ext d j
  simp only [Matrix.add_apply, SubexponentialSAT.BinomialMatrix.B_apply, Matrix.mul_apply, shift]
  by_cases hj : j.val = 0
  · simp [hj]
  · have hjpos : 0 < j.val := by omega
    let k : Fin R := ⟨j.val - 1, by omega⟩
    rw [Finset.sum_eq_single k]
    · have hjk : k.val + 1 = j.val := by dsimp [k]; omega
      simp only [hjk, ite_true, mul_one]
      have hp := Nat.choose_succ_succ (A + d.val) k.val
      rw [show A + 1 + d.val = (A + d.val) + 1 by omega, ← hjk, hp]
      push_cast
      ring
    · intro b hb hbk
      have hne : b.val + 1 ≠ j.val := by
        intro he
        apply hbk
        apply Fin.ext
        dsimp [k]
        omega
      simp [hne]
    · simp

theorem parity_step_vector (A R : ℕ) :
    parityCoefficients (K := ℤ) (A + 1) R +
      shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R =
        -parityCoefficients (K := ℤ) A R := by
  let B := SubexponentialSAT.BinomialMatrix.B ℤ A R
  let target : Fin R → ℤ := fun d => (-1 : ℤ) ^ (A + 1 + d.val)
  have hleft : B *ᵥ (parityCoefficients (K := ℤ) (A + 1) R +
      shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R) = target := by
    have hf : (1 + shift R) *ᵥ parityCoefficients (K := ℤ) (A + 1) R =
        parityCoefficients (K := ℤ) (A + 1) R +
          shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
    rw [← hf, Matrix.mulVec_mulVec]
    change (SubexponentialSAT.BinomialMatrix.B ℤ A R * (1 + shift R)) *ᵥ _ = _
    rw [← binomial_succ]
    exact mulVec_coefficients _ (isUnit_det_binomial (A + 1) R) _
  have hright : B *ᵥ (-parityCoefficients (K := ℤ) A R) = target := by
    rw [Matrix.mulVec_neg]
    change -(SubexponentialSAT.BinomialMatrix.B ℤ A R *ᵥ
      coefficients (SubexponentialSAT.BinomialMatrix.B ℤ A R) (fun d => (-1 : ℤ) ^ (A + d.val))) = _
    rw [mulVec_coefficients _ (isUnit_det_binomial A R)]
    funext d
    simp only [Pi.neg_apply, target]
    rw [show A + 1 + d.val = (A + d.val) + 1 by omega, pow_succ]
    ring
  exact (coefficients_unique B (isUnit_det_binomial A R) target _ hleft).trans
    (coefficients_unique B (isUnit_det_binomial A R) target _ hright).symm

theorem parity_step (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) (A + 1) R j +
      (if h : j.val + 1 < R then parityCoefficients (K := ℤ) (A + 1) R
        ⟨j.val + 1, h⟩ else 0) = -parityCoefficients (K := ℤ) A R j := by
  have h := congrFun (parity_step_vector A R) j
  simpa only [Pi.add_apply, Pi.neg_apply, shift_mulVec] using h

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
