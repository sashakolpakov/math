import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Asymptotics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

/-! Numerical transport for the frozen endpoint signatures in `specification/main-theorem.md`.
The existence of the required finite counting program is not asserted in this module. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem runtimeBound_le_eth {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) (hn : 20 ≤ n) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (d : ℕ) :
    SqrtLog.Statement.runtimeBound C A d (Encoding.formulaBitLength F) n ≤
      (C * ((8 * k + 7 : ℕ) : ℝ) ^ d) * ((n + F.card + 1 : ℕ) : ℝ) ^ (2 * d) *
        (2 : ℝ) ^ ((4 * A) * rho n) := by
  have hexponent : A * SqrtLog.Statement.runtimeScale n ≤ (4 * A) * rho n := by
    calc
      A * SqrtLog.Statement.runtimeScale n ≤ A * (4 * rho n) :=
        mul_le_mul_of_nonneg_left (runtimeScale_le_four_rho hn) hA
      _ = _ := by ring
  unfold SqrtLog.Statement.runtimeBound
  calc
    C * ((Encoding.formulaBitLength F : ℝ) + 1) ^ d *
        (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
      C * (((8 * k + 7 : ℕ) : ℝ) ^ d * ((n + F.card + 1 : ℕ) : ℝ) ^ (2 * d)) *
        (2 : ℝ) ^ ((4 * A) * rho n) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (encoding_pow_le_declaredSize F hw d) hC
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      · positivity
      · positivity
    _ = _ := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
