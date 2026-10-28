import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyCodeParameters

namespace OAI.Algorithms

/-! A uniform numerical envelope for the actual finite code searches.
Search dimensions occur only in the exponential factor. Encoded metadata
lengths remain in a separate fixed polynomial factor. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open Filter
open scoped Topology
open CostAssembly Asymptotic

def exponent (C H : ℕ) : ℕ := 7*(C+(H+1)^2)+6

def envelope (C H W : ℕ) : ℕ := 3 ^ exponent C H * (W+1)^6

theorem self_le_three_pow (n : ℕ) : n ≤ 3^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 3^n := Nat.one_le_pow _ _ (by decide)
    omega

theorem envelope_le_power (C H W n u : ℕ) (hn : 2 ≤ n) (hW : W ≤ (n+1)^u) :
    envelope C H W ≤ (n+1)^(exponent C H+6*(u+1)) := by
  have hp : 1 ≤ (n+1)^u := Nat.one_le_pow _ _ (by omega)
  have hw : W+1 ≤ (n+1)^(u+1) := by
    rw [pow_succ]
    nlinarith
  calc
    envelope C H W ≤ (n+1)^exponent C H * ((n+1)^(u+1))^6 := by
      unfold envelope
      gcongr
      omega
    _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega

def degreeConstant (C A u : ℕ) : ℕ := 7*(C+(A+1)^2)+6+6*(u+1)

theorem exponent_le (C A H u n q : ℕ) (hH : H ≤ A*L n^q) :
    exponent C H+6*(u+1) ≤ degreeConstant C A u * L n^(2*q) := by
  have hp : 1 ≤ L n^q := Nat.one_le_pow _ _ (L_pos n)
  have hp2 : 1 ≤ L n^(2*q) := Nat.one_le_pow _ _ (L_pos n)
  have hh : H+1 ≤ (A+1)*L n^q := by nlinarith
  have hsq : (H+1)^2 ≤ (A+1)^2*L n^(2*q) := by
    calc
      _ ≤ ((A+1)*L n^q)^2 := by gcongr
      _ = _ := by ring
  unfold exponent degreeConstant
  nlinarith

/-- One cutoff works for all admissible dimensions and metadata lengths. -/
theorem eventually_envelope (C A q u : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀ H W:ℕ, H ≤ A*L n^q → W ≤ (n+1)^u →
      (envelope C H W:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  let K := degreeConstant C A u
  have hK : (0:ℝ) < K := by dsimp [K,degreeConstant]; positivity
  have hd : ∀ᶠ n:ℕ in atTop,
      ((K*L n^(2*q):ℕ):ℝ) ≤ (K:ℝ)*(L n:ℝ)^(2*q) := by
    filter_upwards [] with n
    push_cast
    rfl
  have hh := eventually_polylog_degree_target (fun n => K*L n^(2*q)) (2*q) hK hd
  filter_upwards [hh,eventually_ge_atTop 2] with n hn htwo H W hH hW
  have hb : envelope C H W ≤ (n+1)^(K*L n^(2*q)) := by
    exact (envelope_le_power C H W n u htwo hW).trans
      (Nat.pow_le_pow_right (by omega) (exponent_le C A H u n q hH))
  calc
    (envelope C H W:ℝ) ≤ (((n+1)^(K*L n^(2*q)):ℕ):ℝ) := by exact_mod_cast hb
    _ ≤ _ := hn

/-- Arbitrarily padded encodings retain their visible polynomial factor. -/
theorem eventually_envelope_with_words (C A q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀ H W:ℕ, H ≤ A*L n^q →
      (envelope C H W:ℝ) ≤ ((W:ℝ)+1)^6*(2:ℝ)^Statement.runtimeScale n := by
  filter_upwards [eventually_envelope C A q 0] with n hn H W hH
  have he := hn H 0 hH (by simp)
  simp only [envelope,zero_add,one_pow,mul_one] at he
  push_cast at he
  unfold envelope
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right he (show 0 ≤ ((W:ℝ)+1)^6 by positivity)]

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
