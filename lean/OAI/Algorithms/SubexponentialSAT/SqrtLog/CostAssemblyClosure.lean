import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

/-- The outer sparsification tree, failed-candidate loops, or any other exact
multiplicative counter add their target coefficients. -/
theorem mul_target_bounds (f g : ℕ → ℕ) {C D A B : ℝ}
    (hf : ∀n,(f n:ℝ) ≤ C*(2:ℝ)^(A*Statement.runtimeScale n))
    (hg : ∀n,(g n:ℝ) ≤ D*(2:ℝ)^(B*Statement.runtimeScale n)) :
    ∀n, ((f n*g n:ℕ):ℝ) ≤ (C*D)*(2:ℝ)^((A+B)*Statement.runtimeScale n) := by
  intro n
  have hD : 0 ≤ D*(2:ℝ)^(B*Statement.runtimeScale n) :=
    (Nat.cast_nonneg (g n)).trans (hg n)
  have hh := mul_le_mul (hf n) (hg n) (Nat.cast_nonneg (g n))
    ((Nat.cast_nonneg (f n)).trans (hf n))
  push_cast
  calc
    _ ≤ (C*(2:ℝ)^(A*Statement.runtimeScale n))*(D*(2:ℝ)^(B*Statement.runtimeScale n)) := hh
    _ = _ := by
      rw [show (C*(2:ℝ)^(A*Statement.runtimeScale n))*(D*(2:ℝ)^(B*Statement.runtimeScale n)) =
        (C*D)*((2:ℝ)^(A*Statement.runtimeScale n)*(2:ℝ)^(B*Statement.runtimeScale n)) by ring]
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 2
      ring

/-- A fixed polynomial simulation overhead multiplies the exponent by a
fixed integer and preserves the requested explicit runtime form. -/
theorem pow_target_bound (f : ℕ → ℕ) (p : ℕ) {C A : ℝ}
    (hf : ∀n,(f n:ℝ) ≤ C*(2:ℝ)^(A*Statement.runtimeScale n)) :
    ∀n, ((f n^p:ℕ):ℝ) ≤ C^p*(2:ℝ)^(((p:ℝ)*A)*Statement.runtimeScale n) := by
  intro n
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (f n)) (hf n) p
  push_cast
  calc
    _ ≤ (C*(2:ℝ)^(A*Statement.runtimeScale n))^p := hh
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
      congr 2
      ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
