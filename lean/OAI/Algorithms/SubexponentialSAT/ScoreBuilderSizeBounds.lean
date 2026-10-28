import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTypeVariance

namespace OAI.Algorithms

/-! The concrete score-builder expression is polynomial in the actual
instance parameters, including the full type count N. -/

namespace SubexponentialSAT.ScoreBuilderSizeBounds

def sourceSize (D E N Q r Δ : ℕ) : ℕ := D + E + N + Q + r + Δ + 1

theorem wordChoices_le (r Q Δ N : ℕ) (hr : 1 ≤ r)
    (hN : N = r ^ (Q * (Δ + 1))) : r ^ Q ≤ N := by
  rw [hN]
  apply Nat.pow_le_pow_right hr
  nlinarith

theorem pair_completions_eq (r Q Δ N : ℕ)
    (hN : N = r ^ (Q * (Δ + 1))) : (r ^ Q) ^ (2 * (Δ + 1)) = N ^ 2 := by
  rw [hN, ← pow_mul, ← pow_mul]
  congr 1
  ring

theorem input_expression_le (D E N Q r Δ : ℕ) (hr : 1 ≤ r)
    (hN : N = r ^ (Q * (Δ + 1))) :
    16 * ((E + (Δ + 1) * D) + D + r ^ Q + Q * r + Δ + 1) ^ 2 ≤
      1024 * sourceSize D E N Q r Δ ^ 4 := by
  let S := sourceSize D E N Q r Δ
  have hS : 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hD : D ≤ S := by dsimp [S, sourceSize]; omega
  have hE : E ≤ S := by dsimp [S, sourceSize]; omega
  have hQ : Q ≤ S := by dsimp [S, sourceSize]; omega
  have hrS : r ≤ S := by dsimp [S, sourceSize]; omega
  have hΔ : Δ + 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hq : r ^ Q ≤ S := (wordChoices_le r Q Δ N hr hN).trans (by dsimp [S, sourceSize]; omega)
  have hS2 : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 2 by decide)
  have hM : (Δ + 1) * D ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hΔ hD
  have hw : Q * r ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hQ hrS
  have hsum : (E + (Δ + 1) * D) + D + r ^ Q + Q * r + Δ + 1 ≤ 8 * S ^ 2 := by omega
  calc
    _ ≤ 16 * (8 * S ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
    _ = 1024 * sourceSize D E N Q r Δ ^ 4 := by dsimp [S]; ring

theorem runtime_expression_le (D E N Q r Δ : ℕ) (hr : 1 ≤ r)
    (hN : N = r ^ (Q * (Δ + 1))) :
    10000 * 31 ^ 6 *
        (16 * ((E + (Δ + 1) * D) + D + r ^ Q + Q * r + Δ + 1) ^ 2 + 1) ^ 12 *
          (r ^ Q) ^ (2 * (Δ + 1)) ≤
      (10000 * 31 ^ 6 * 1025 ^ 12) * sourceSize D E N Q r Δ ^ 50 := by
  let S := sourceSize D E N Q r Δ
  have hS : 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hS4 : 1 ≤ S ^ 4 := by simpa using Nat.pow_le_pow_left hS 4
  have hin := input_expression_le D E N Q r Δ hr hN
  have hin' : 16 * ((E + (Δ + 1) * D) + D + r ^ Q + Q * r + Δ + 1) ^ 2 + 1 ≤
      1025 * S ^ 4 := by change _ ≤ 1024 * S ^ 4 at hin; omega
  have hNS : N ≤ S := by dsimp [S, sourceSize]; omega
  rw [pair_completions_eq r Q Δ N hN]
  calc
    _ ≤ (10000 * 31 ^ 6) * (1025 * S ^ 4) ^ 12 * S ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hin' 12))
        (Nat.pow_le_pow_left hNS 2)
    _ = (10000 * 31 ^ 6 * 1025 ^ 12) * sourceSize D E N Q r Δ ^ 50 := by dsimp [S]; ring

end SubexponentialSAT.ScoreBuilderSizeBounds

end OAI.Algorithms
