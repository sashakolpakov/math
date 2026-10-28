import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionRuntime

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement

/-- Simultaneous monotonicity keeps the actual supplied input length. -/
theorem runtime_mono {C D A B : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (hAB : A ≤ B)
    {d e X Y n : ℕ} (hde : d ≤ e) (hXY : X ≤ Y) :
    runtimeBound C A d X n ≤ runtimeBound D B e Y n := by
  have hD : 0 ≤ D := hC.trans hCD
  have hbase : (1:ℝ) ≤ (Y:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) Y; linarith
  have hin : ((X:ℝ)+1)^d ≤ ((Y:ℝ)+1)^d := by gcongr
  have hpow := hin.trans (pow_le_pow_right₀ hbase hde)
  have hex : (2:ℝ)^(A*runtimeScale n) ≤ (2:ℝ)^(B*runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hAB (runtimeScale_nonneg n))
  unfold runtimeBound
  exact mul_le_mul (mul_le_mul hCD hpow (by positivity) (by linarith)) hex
    (by positivity) (by positivity)

 theorem ceil_runtime_mono {C D A B : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (hAB : A ≤ B)
    {d e X Y n : ℕ} (hde : d ≤ e) (hXY : X ≤ Y) :
    Nat.ceil (runtimeBound C A d X n) ≤ Nat.ceil (runtimeBound D B e Y n) :=
  Nat.ceil_le_ceil (runtime_mono hC hCD hAB hde hXY)

/-- The common constants are chosen before either actual source length. -/
theorem common_queries {Rm Ra Am Aa : ℝ}
    (hRm : 0 ≤ Rm) (hRa : 0 ≤ Ra) (hAm : 0 ≤ Am) (hAa : 0 ≤ Aa)
    (em ea : ℕ) :
    1 ≤ Rm+Ra+1 ∧ 0 ≤ Am+Aa ∧
    ∀ Xm Xa X n : ℕ, Xm ≤ X → Xa ≤ X →
      Nat.ceil (runtimeBound Rm Am em Xm n) ≤
        Nat.ceil (runtimeBound (Rm+Ra+1) (Am+Aa) (em+ea) X n) ∧
      Nat.ceil (runtimeBound Ra Aa ea Xa n) ≤
        Nat.ceil (runtimeBound (Rm+Ra+1) (Am+Aa) (em+ea) X n) := by
  refine ⟨by linarith,by linarith,?_⟩
  intro Xm Xa X n hm ha
  constructor
  · exact ceil_runtime_mono hRm (by linarith) (by linarith) (by omega) hm
  · exact ceil_runtime_mono hRa (by linarith) (by linarith) (by omega) ha

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms
