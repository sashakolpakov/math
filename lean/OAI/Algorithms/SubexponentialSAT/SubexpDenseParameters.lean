import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-! Absolute-degree parameter bounds for the physical dense-product budget. -/

namespace SubexponentialSAT.SubexpDenseParameters

open SubexpSymbolicCost SubexpLiftRing

theorem polynomial_le_parameterPower (C B I N X M : ℕ)
    (hX : 1 ≤ X) (hM : 1 ≤ M) (hB : B ≤ X^2) (hI : I ≤ 2 * X^2)
    (hN : N ≤ M * X^2) :
    C * (B + I + 1)^3 * (N + 1)^3 ≤ (C * 512) * X^12 * M^4 := by
  have hX2 : 1 ≤ X^2 := by nlinarith
  have hwidth : B + I + 1 ≤ 4 * X^2 := by omega
  have hMX : 1 ≤ M * X^2 := by simpa using Nat.mul_le_mul hM hX2
  have hcount : N + 1 ≤ 2 * (M * X^2) := by omega
  have hM34 : M^3 ≤ M^4 := Nat.pow_le_pow_right hM (by decide)
  calc
    _ ≤ C * (4 * X^2)^3 * (2 * (M * X^2))^3 := by gcongr
    _ = ((C * 512) * X^12) * M^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hM34

/-- This specializes to actual widths/capacity, without a supplied width
bound, for every natural dimension and modulus. -/
theorem polynomial_le_uniform (C p D : ℕ) :
    C * (baseWidth p (D + 1) + indexBits D + 1)^3 * (slotCount D + 1)^3 ≤
      (C * 512) * (parameterSize D 4 (Nat.log 2 p + 1))^12 * (monomialCount D)^4 := by
  let X := parameterSize D 4 (Nat.log 2 p + 1)
  have hX : 1 ≤ X := by dsimp [X, parameterSize]; omega
  have hD : D + 1 ≤ X := by dsimp [X, parameterSize]; omega
  have hb : Nat.log 2 p + 1 ≤ X := by dsimp [X, parameterSize]; omega
  have hB : baseWidth p (D + 1) ≤ X^2 := by
    simpa only [baseWidth, pow_two] using Nat.mul_le_mul hD hb
  have hI : indexBits D ≤ 2 * X^2 := indexBits_degree D 4 (Nat.log 2 p + 1)
  have hM : 1 ≤ monomialCount D := Nat.choose_pos (by omega : D ≤ 3 * D + 1)
  have hslots : slotCount D ≤ monomialCount D * X^2 := by
    apply Nat.mul_le_mul_left
    simpa only [pow_two] using Nat.mul_le_mul hD ((Nat.le_succ D).trans hD)
  exact polynomial_le_parameterPower C _ _ _ X _ hX hM hB hI hslots

end SubexponentialSAT.SubexpDenseParameters

end OAI.Algorithms
