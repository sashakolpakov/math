import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionRuntime

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.FinalCost
open SubexponentialSAT.SqrtLog.Statement

theorem runtimeBound_product (C A D B : ℝ) (d e L n : ℕ) :
    runtimeBound C A d L n * runtimeBound D B e L n =
      runtimeBound (C*D) (A+B) (d+e) L n := by
  unfold runtimeBound
  rw [pow_add]
  rw [show (A+B)*runtimeScale n=A*runtimeScale n+B*runtimeScale n by ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  ring

/-- A polynomial in a measured state-size envelope preserves the target form. -/
theorem runtimeBound_substitute {C A H B : ℝ} (hC : 0 ≤ C)
    (d e L W n : ℕ)
    (hsize : (W:ℝ)+1 ≤ runtimeBound H B e L n) :
    runtimeBound C A d W n ≤
      runtimeBound (C*H^d) (A+(d:ℝ)*B) (e*d) L n := by
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (W:ℝ)+1) hsize d
  calc
    _ ≤ C*(runtimeBound H B e L n)^d*(2:ℝ)^(A*runtimeScale n) := by
      unfold runtimeBound at ⊢
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity)
    _ = runtimeBound C A 0 L n * runtimeBound (H^d) ((d:ℝ)*B) (e*d) L n := by
      rw [runtimeBound_pow]
      simp only [runtimeBound,pow_zero,mul_one]
      ring
    _ = _ := by rw [runtimeBound_product]; simp

/-- The whole physical state-size budget after prefix/setup and splitting. -/
theorem state_size_bound {Cp : ℝ} (hCp : 0 ≤ Cp) (q L n P S : ℕ)
    (hP : (P:ℝ) ≤ Cp*((L:ℝ)+1)^q)
    (hS : (S:ℝ) ≤ 3617*((L:ℝ)+1)^2*(2:ℝ)^(130*runtimeScale n)) :
    ((L+P+S:ℕ):ℝ)+1 ≤ runtimeBound (Cp+3618) 130 (q+2) L n := by
  let X : ℝ := (L:ℝ)+1
  let E : ℝ := (2:ℝ)^(130*runtimeScale n)
  have hX : 1 ≤ X := by dsimp [X]; have := Nat.cast_nonneg (α:=ℝ) L; linarith
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num) (by nlinarith [runtimeScale_nonneg n])
  have hq : X^q ≤ X^(q+2) := pow_le_pow_right₀ hX (by omega)
  have h2 : X^2 ≤ X^(q+2) := pow_le_pow_right₀ hX (by omega)
  have h1 : X ≤ X^(q+2) := by simpa using pow_le_pow_right₀ hX (by omega : 1 ≤ q+2)
  have hl : X ≤ X^(q+2)*E := h1.trans (le_mul_of_one_le_right (by positivity) hE)
  have hp : (P:ℝ) ≤ Cp*X^(q+2)*E := by
    calc
      _ ≤ Cp*X^q := hP
      _ ≤ Cp*X^(q+2) := mul_le_mul_of_nonneg_left hq hCp
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hCp (by positivity)) hE
  have hs : (S:ℝ) ≤ 3617*X^(q+2)*E := by
    calc
      _ ≤ 3617*X^2*E := hS
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by linarith)
  unfold runtimeBound
  change ((L+P+S:ℕ):ℝ)+1 ≤ (Cp+3618)*X^(q+2)*E
  push_cast
  dsimp [X] at hl
  nlinarith only [hl,hp,hs]

end SubexponentialSAT.SqrtLog.Execution.FinalCost

end OAI.Algorithms
