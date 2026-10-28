import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec
import OAI.Algorithms.SubexponentialSAT.DyadicParameterBounds

namespace OAI.Algorithms

/-! A single input-polynomial bound for the numerical loop parameters used by
the fixed setup program. This is derived from the implemented dyadic schedule. -/

namespace SubexponentialSAT.SubexpSetupParameterBound

open Filter SubexpPackingParameters SubexpSetupProgram SubexpSetupBoundSpec

def parameterBudget (c : Config) (n : ℕ) : ℕ :=
  n + DyadicSchedule.Q n * (DyadicSchedule.delta c.k c.T n + 1) + 1

theorem prime_scale_le (c : Config) (n : ℕ) (hn : GoodInput n) :
    2 ^ u n ≤ parameterBudget c n := by
  have hpow : 2 ^ u n ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (u_le_s n)).trans
      ((pow_s_le_log2 (goodInput_two_le hn)).trans (Nat.log2_le_self n))
  exact hpow.trans (by unfold parameterBudget; omega)

theorem block_exponent_le (c : Config) (n : ℕ) :
    DyadicSchedule.Q n * (DyadicSchedule.delta c.k c.T n + 1) ≤
      parameterBudget c n := by
  unfold parameterBudget
  omega

theorem parameterBudget_polynomial (c : Config) :
    PolynomialFunction (parameterBudget c) := by
  obtain ⟨C, d, hC, hentries⟩ := DyadicParameterBounds.eventually_entries_polynomial c.k c.T
  refine ⟨C * (C + 1) + 1, 2 * (d + 1), by omega, by omega, ?_⟩
  filter_upwards [hentries] with n hentries
  have hzero : 0 ≤ DyadicSchedule.delta c.k c.T n * D n := Nat.zero_le _
  have hQ : DyadicSchedule.Q n ≤ C * (n + 1) ^ d := by
    apply hentries 0 hzero
    simp [DyadicParameterBounds.parameters, DyadicParameterBounds.parametersOfIncidence,
      SubexpRuntime.GrowingParameters.entries, DyadicSchedule.Q]
  have hdelta : DyadicSchedule.delta c.k c.T n ≤ C * (n + 1) ^ d := by
    apply hentries 0 hzero
    simp [DyadicParameterBounds.parameters, DyadicParameterBounds.parametersOfIncidence,
      SubexpRuntime.GrowingParameters.entries]
  let X := (n + 1) ^ (d + 1)
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hpow : (n + 1) ^ d ≤ X :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hQX : DyadicSchedule.Q n ≤ C * X :=
    hQ.trans (Nat.mul_le_mul_left C hpow)
  have hdX : DyadicSchedule.delta c.k c.T n + 1 ≤ (C + 1) * X := by
    calc
      DyadicSchedule.delta c.k c.T n + 1 ≤ C * X + X :=
        Nat.add_le_add (hdelta.trans (Nat.mul_le_mul_left C hpow)) hX
      _ = (C + 1) * X := by ring
  have hprod : DyadicSchedule.Q n * (DyadicSchedule.delta c.k c.T n + 1) ≤
      C * (C + 1) * X ^ 2 := by
    calc
      _ ≤ (C * X) * ((C + 1) * X) := Nat.mul_le_mul hQX hdX
      _ = _ := by ring
  have hnX : n + 1 ≤ X := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by omega : 1 ≤ d + 1)
  have hXX : X ≤ X ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 2)
  calc
    parameterBudget c n ≤ C * (C + 1) * X ^ 2 + X ^ 2 := by
      unfold parameterBudget
      have := hnX.trans hXX
      omega
    _ = (C * (C + 1) + 1) * X ^ 2 := by ring
    _ = (C * (C + 1) + 1) * (n + 1) ^ (2 * (d + 1)) := by
      dsimp only [X]
      rw [← pow_mul]
      congr 1
      congr 1
      omega

end SubexponentialSAT.SubexpSetupParameterBound

end OAI.Algorithms
