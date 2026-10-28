import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblySupport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyMoment

namespace OAI.Algorithms

/-! Numerical assembly of the sparse-query costs.  `sparseWork` is an explicit
natural-valued upper cost, not a running-time oracle. Connecting an executable
program to these counters and charging coefficient arithmetic are separate
machine-refinement obligations. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- All resource counters remain visible. `ordinary` contains the fixed
polynomial work outside support enumeration; `bits` charges primitive
arithmetic. `calls` includes unsuccessful hash candidates and marked counts. -/
def sparseWork (n J setup calls branches labels bits ordinary : ℕ) : ℕ :=
  setup + calls * branches * labels * bits * (ordinary + 1)^8 *
    (SupportProgram.count n J + 1)^4

/-- Fixed polynomial overhead in n is negligible at the target scale. -/
theorem eventually_polynomial_target (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (((n+1)^d : ℕ) : ℝ) ≤
      (2 : ℝ)^Statement.runtimeScale n := by
  apply eventually_variable_search_target (fun _ => d) 0
    (show (0:ℝ) < (d:ℝ)+1 by positivity)
  filter_upwards [] with n
  simp

/-- A polynomial-log exponent gives a full exponential cost bound. -/
theorem eventually_counter_target (f : ℕ → ℕ) (q : ℕ) {C : ℝ} (hC : 0 < C)
    (hf : ∀ᶠ n : ℕ in atTop, Real.logb 2 ((f n : ℝ)+1) ≤ C*logSize n^q) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (2 : ℝ)^Statement.runtimeScale n := by
  have he := eventually_polylog_bounded_target
    (fun n => Real.logb 2 ((f n : ℝ)+1)) q hC hf
  filter_upwards [he] with n hn
  calc
    (f n : ℝ) ≤ (f n : ℝ)+1 := by linarith
    _ = (2 : ℝ)^Real.logb 2 ((f n : ℝ)+1) := by
      symm
      exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

/-- A high-incidence branching exponent n/sqrt(L) costs at most a fixed
multiple of the requested runtime exponent. -/
theorem high_branch_exponent_le (n : ℕ) :
    (n : ℝ)/Real.sqrt (L n : ℝ) ≤ 64*Statement.runtimeScale n := by
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have h := weighted_scale_le_target n
  have hh : (n : ℝ)/Real.sqrt (L n : ℝ) ≤
      (n : ℝ)*(w n:ℝ)^2/Real.sqrt (L n:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hs : (1:ℝ) ≤ (w n:ℝ)^2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
  exact hh.trans h

/-- Pointwise assembly. The factor 17 charges the +1 support and the separate
setup. Every exponent is a constant coefficient of the same target scale. -/
theorem sparseWork_le (n J setup calls branches labels bits ordinary : ℕ)
    {T A B E : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hsetup : (setup:ℝ) ≤ (2:ℝ)^T)
    (hcalls : (calls:ℝ) ≤ (2:ℝ)^T)
    (hbranches : (branches:ℝ) ≤ (2:ℝ)^(B*T))
    (hlabels : (labels:ℝ) ≤ (2:ℝ)^(A*T))
    (hordinary : (bits:ℝ)*(ordinary+1:ℕ)^8 ≤ (2:ℝ)^T)
    (hsupport : (SupportProgram.count n J:ℝ) ≤ (2:ℝ)^(E*T)) :
    (sparseWork n J setup calls branches labels bits ordinary:ℝ) ≤
      17*(2:ℝ)^((2+B+A+4*E)*T) := by
  have hone : (1:ℝ) ≤ (2:ℝ)^(E*T) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hE hT)
  have hs : (SupportProgram.count n J:ℝ)+1 ≤ 2*(2:ℝ)^(E*T) := by linarith
  have hp : ((SupportProgram.count n J:ℝ)+1)^4 ≤
      16*(2:ℝ)^((4*E)*T) := by
    calc
      _ ≤ (2*(2:ℝ)^(E*T))^4 := by gcongr
      _ = _ := by
        have hpow : ((2:ℝ)^(E*T))^4 = (2:ℝ)^((E*T)*(4:ℝ)) := by
          exact (Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (E*T) 4).symm
        rw [mul_pow, hpow]
        norm_num
        congr 1
        ring
  have hmain : (calls:ℝ)*(branches:ℝ)*(labels:ℝ)*
      ((bits:ℝ)*(ordinary+1:ℕ)^8)*((SupportProgram.count n J:ℝ)+1)^4 ≤
      16*(2:ℝ)^((2+B+A+4*E)*T) := by
    calc
      _ ≤ (2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*
          (16*(2:ℝ)^((4*E)*T)) := by gcongr
      _ = _ := by
        rw [show (2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*
          (16*(2:ℝ)^((4*E)*T)) =
          16*((2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*(2:ℝ)^((4*E)*T)) by ring]
        simp only [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 2
        ring
  have hmono : T ≤ (2+B+A+4*E)*T := by nlinarith
  have hsetup' := hsetup.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hmono)
  unfold sparseWork
  push_cast
  calc
    _ = (setup:ℝ) + (calls:ℝ)*(branches:ℝ)*(labels:ℝ)*
        ((bits:ℝ)*(ordinary+1:ℕ)^8)*((SupportProgram.count n J:ℝ)+1)^4 := by push_cast; ring
    _ ≤ _ := by linarith

/-- The explicit cost has a global C*2^(A*runtimeScale) bound once its exact
setup/query counters have polylogarithmic logarithms, its ordinary bit work is
polynomial, and its head/branch exponents satisfy the numerical budgets.
Only finitely many small inputs are absorbed by C. -/
theorem sparseWork_target
    (J setup calls branches labels bits ordinary : ℕ → ℕ)
    (setupPower callsPower ordinaryPower : ℕ)
    {setupConstant callsConstant C A B : ℝ}
    (hsetupConstant : 0 < setupConstant) (hcallsConstant : 0 < callsConstant)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ : ∀ᶠ n : ℕ in atTop, (J n : ℝ) ≤ entropyCutoff n C)
    (hsetup : ∀ᶠ n : ℕ in atTop,
      Real.logb 2 ((setup n : ℝ) + 1) ≤ setupConstant * logSize n ^ setupPower)
    (hcalls : ∀ᶠ n : ℕ in atTop,
      Real.logb 2 ((calls n : ℝ) + 1) ≤ callsConstant * logSize n ^ callsPower)
    (hbranches : ∀ᶠ n : ℕ in atTop,
      (branches n : ℝ) ≤ (2 : ℝ) ^ (B * Statement.runtimeScale n))
    (hlabels : ∀ᶠ n : ℕ in atTop,
      (labels n:ℝ) ≤ (2:ℝ)^(A*Statement.runtimeScale n))
    (hordinary : ∀ᶠ n : ℕ in atTop,
      bits n*(ordinary n+1)^8 ≤ (n+1)^ordinaryPower) :
    ∃K:ℝ, 0 < K ∧ ∀n,
      (sparseWork n (J n) (setup n) (calls n) (branches n) (labels n)
        (bits n) (ordinary n):ℝ) ≤
      K*(2:ℝ)^((2+B+A+4*(384*C+1))*Statement.runtimeScale n) := by
  have he := eventually_support_target J hC hJ
  have hs := eventually_counter_target setup setupPower hsetupConstant hsetup
  have hc := eventually_counter_target calls callsPower hcallsConstant hcalls
  have hp := eventually_polynomial_target ordinaryPower
  have ha : 0 ≤ 2+B+A+4*(384*C+1) := by linarith
  have hev : ∀ᶠ n : ℕ in atTop,
      (sparseWork n (J n) (setup n) (calls n) (branches n) (labels n)
        (bits n) (ordinary n):ℝ)/17 ≤
      (2:ℝ)^((2+B+A+4*(384*C+1))*Statement.runtimeScale n) := by
    filter_upwards [he,hs,hc,hp,hbranches,hlabels,hordinary]
      with n hnE hnS hnC hnP hnB hnA hnO
    have ho : (bits n:ℝ)*(ordinary n+1:ℕ)^8 ≤ (2:ℝ)^Statement.runtimeScale n := by
      exact (show (bits n:ℝ)*(ordinary n+1:ℕ)^8 ≤ ((n+1)^ordinaryPower:ℕ) by exact_mod_cast hnO).trans hnP
    have h := sparseWork_le n (J n) (setup n) (calls n) (branches n) (labels n)
      (bits n) (ordinary n) (Statement.runtimeScale_nonneg n) hA hB
      (show 0 ≤ 384*C+1 by linarith) hnS hnC hnB hnA ho hnE
    linarith
  obtain ⟨K,hK,hbound⟩ := finite_prefix_absorption _ ha hev
  refine ⟨17*K,by positivity,?_⟩
  intro n
  have h := hbound n
  nlinarith

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
