import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidual

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Uniform joint-label and head enumeration for any residual layout retaining
at least half the ambient variables. The exact same coefficient works for
all high-incidence branches. -/
theorem eventually_residual_enumeration_bound :
    ∀ᶠ n : ℕ in atTop, ∀ m base rows heads headSize: ℕ,
      m ≤ n → n ≤ 2*m → 0 < base →
      16*(layoutR m: ℝ)*(L m: ℝ)^2*(rows: ℝ) ≤ m →
      Real.log (base: ℝ) ≤ 4*(L m: ℝ)^2 →
      heads ≤ m+1 → (headSize: ℝ) ≤ 2*(m: ℝ)/layoutR m →
      (enumerationWork base rows heads headSize: ℝ) ≤
        (2: ℝ)^(641*Statement.runtimeScale n) := by
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0: ℝ) < 1)
  filter_upwards [eventually_residual_inverse_target, hpoly]
    with n hi hp m base rows heads headSize hmn hnm hb hr hh hd hs
  have hInv := hi m hmn hnm
  have hrpos : (0: ℝ) < layoutR m := by
    have := layoutR_ge_two m
    exact_mod_cast (by omega : 0 < layoutR m)
  have hmn' : (m: ℝ) ≤ n := by exact_mod_cast hmn
  have he := signature_log_budget base rows hrpos hr hh
  have hmnInv : (m: ℝ)/layoutR m ≤ (n: ℝ)/layoutR m :=
    div_le_div_of_nonneg_right hmn' hrpos.le
  have hE : (rows: ℝ)*Real.logb 2 base ≤ 128*Statement.runtimeScale n := by
    have : (m: ℝ)/(2*layoutR m) = ((m: ℝ)/layoutR m)/2 := by ring
    rw [this] at he
    linarith
  have hF : (headSize: ℝ) ≤ 512*Statement.runtimeScale n := by
    have : 2*(m: ℝ)/layoutR m = 2*((m: ℝ)/layoutR m) := by ring
    rw [this] at hs
    linarith
  have hG : (heads: ℝ) ≤ (2: ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hp
    calc
      _ ≤ (m: ℝ)+1 := by exact_mod_cast hd
      _ ≤ (n: ℝ)+16 := by linarith
      _ = (2: ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  convert enumerationWork_le base rows heads headSize hb hE hF hG using 1
  congr 1
  ring

/-- Ambient seeds may be chosen before restricting heads to free variables.
The larger head bound still has coefficient 641: its numerator is already the
ambient dimension in the residual inverse-schedule estimate. -/
theorem eventually_residual_enumeration_ambient_bound :
    ∀ᶠ n : ℕ in atTop, ∀ m base rows heads headSize: ℕ,
      m ≤ n → n ≤ 2*m → 0 < base →
      16*(layoutR m: ℝ)*(L m: ℝ)^2*(rows: ℝ) ≤ m →
      Real.log (base: ℝ) ≤ 4*(L m: ℝ)^2 →
      heads ≤ n+1 → (headSize: ℝ) ≤ 2*(n: ℝ)/layoutR m →
      (enumerationWork base rows heads headSize: ℝ) ≤
        (2: ℝ)^(641*Statement.runtimeScale n) := by
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0: ℝ) < 1)
  filter_upwards [eventually_residual_inverse_target, hpoly]
    with n hi hp m base rows heads headSize hmn hnm hb hr hh hd hs
  have hInv := hi m hmn hnm
  have hrpos : (0: ℝ) < layoutR m := by
    have := layoutR_ge_two m
    exact_mod_cast (by omega : 0 < layoutR m)
  have hmn' : (m: ℝ) ≤ n := by exact_mod_cast hmn
  have he := signature_log_budget base rows hrpos hr hh
  have hmnInv : (m: ℝ)/layoutR m ≤ (n: ℝ)/layoutR m :=
    div_le_div_of_nonneg_right hmn' hrpos.le
  have hE : (rows: ℝ)*Real.logb 2 base ≤ 128*Statement.runtimeScale n := by
    have : (m: ℝ)/(2*layoutR m) = ((m: ℝ)/layoutR m)/2 := by ring
    rw [this] at he
    linarith
  have hF : (headSize: ℝ) ≤ 512*Statement.runtimeScale n := by
    have : 2*(n: ℝ)/layoutR m = 2*((n: ℝ)/layoutR m) := by ring
    rw [this] at hs
    linarith
  have hG : (heads: ℝ) ≤ (2: ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hp
    calc
      _ ≤ (n: ℝ)+1 := by exact_mod_cast hd
      _ ≤ (n: ℝ)+16 := by linarith
      _ = (2: ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  convert enumerationWork_le base rows heads headSize hb hE hF hG using 1
  congr 1
  ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
