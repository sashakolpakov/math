import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgramWork
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyBounds
import OAI.Algorithms.SubexponentialSAT.ExecEncodedSparsifier

namespace OAI.Algorithms

/-! Quantitative bounds for the actual observed program, rather than a
separate pure-list splitter. -/
namespace SubexponentialSAT.SqrtLog.SparsifyProgram

open Filter BitProgram
open ExecSparsifyObserved ExecSparsifyBoundary
open ExecSparsifyNode (Data)
open Asymptotic
open SparsificationConstants SparsificationBudgetProgram

def visitPrefactor (k T s : ℕ) : ℕ :=
  (C (dyadicM T s) (k - 1) + 1) * (k + 1)

theorem visitPrefactor_polynomialBound (k T : ℕ) :
    PolynomialBound (visitPrefactor k T) :=
  ((dyadicC_polynomialBound T (k - 1)).add (polynomialBound_const 1)).mul
    (polynomialBound_const (k + 1))

/-- The actual observed run has the quantitative sunflower-tree bound. -/
theorem visits_polynomial (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ q : ℕ, ∀ n : ℕ, 0 < Asymptotic.s n → ∀ (frame : Data k)
      (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
      (F : Formula n), Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((ExecSparsifyWorklist.run (branching frame (arity T n) hf hb (arity_ge_two k T n))
        (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤
          ((s n + 2) ^ q : ℕ) * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ ((n : ℝ) / s n) := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power
    (visitPrefactor_polynomialBound k T)
  refine ⟨q, ?_⟩
  intro n hn frame hf hb F hF hanti
  have hs := hn
  have hv := visits_quantitative frame (SparsificationBudgetProgram.dyadicM T (s n)) hf hb
    (arity_ge_two k T n) F hF hanti (SparsificationBudgetProgram.dyadicM_ge_two T (s n)) (by omega)
    (1 / (s n : ℝ)) (hT.ratio_le hk (s n) hs) (hT.logb_budget hk (s n) hs)
  change ((ExecSparsifyWorklist.run
    (branching frame (arity T n) hf hb (arity_ge_two k T n))
    (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤ _ at hv
  have hp : (visitPrefactor k T (s n) : ℝ) ≤ ((s n + 2) ^ q : ℕ) := by
    exact_mod_cast hq (s n)
  calc
    _ ≤ (visitPrefactor k T (s n) : ℝ) * ((n : ℝ) + 1) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s n) := by
      simpa only [visitPrefactor, Nat.cast_mul, one_div,
        div_eq_mul_inv, one_mul, mul_comm (s n : ℝ)⁻¹ (n : ℝ), mul_assoc] using hv
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) (by positivity)


theorem eventually_visits_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame) (F : Formula n),
      Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((ExecSparsifyWorklist.run (branching frame (arity T n) hf hb (arity_ge_two k T n))
        (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤
          (2 : ℝ) ^ (129 * Statement.runtimeScale n) := by
  obtain ⟨q, hq⟩ := visits_polynomial k T hk hT
  filter_upwards [SparsifyBounds.eventually_prefactor_target 1 q,
    eventually_le_s 1, eventually_inverse_schedule_target] with n hp hs hi
  intro frame hf hb F hF hanti
  have hv := hq n (by omega) frame hf hb F hF hanti
  have hp' : (((s n + 2) ^ q : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 2 ≤
      (2 : ℝ) ^ Statement.runtimeScale n := by
    simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, one_mul] using hp
  have he : (2 : ℝ) ^ ((n : ℝ) / s n) ≤
      (2 : ℝ) ^ (128 * Statement.runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hi
  calc
    _ ≤ _ := hv
    _ ≤ (2 : ℝ) ^ Statement.runtimeScale n *
        (2 : ℝ) ^ (128 * Statement.runtimeScale n) :=
      mul_le_mul hp' he (Real.rpow_nonneg (by norm_num) _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring


/-- The actual ordered leaf list, not a separately selected output. -/
theorem eventually_leaves_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame) (F : Formula n),
      Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((leaves frame (arity T n) hf hb (arity_ge_two k T n) F).length : ℝ) ≤
        (2 : ℝ) ^ (129 * Statement.runtimeScale n) := by
  filter_upwards [eventually_visits_target k T hk hT] with n hn
  intro frame hf hb F hF hanti
  exact (Nat.cast_le.mpr (ExecSparsifyWorklist.initial_run_leaves_length_le_visits
    (branching frame (arity T n) hf hb (arity_ge_two k T n)) F)).trans
      (hn frame hf hb F hF hanti)

/-- The framing and all emitted literal bits are included in this bound. -/
theorem eventually_encoded_leaves_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame) (F : Formula n),
      Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((Encoding.encodeList encode
        (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).length : ℝ) ≤
        2 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  have hp := Asymptotic.eventually_variable_search_target
    (fun _n => 2 * k + 2) 0 (C := (2 * k + 2 : ℕ)) (by positivity)
    (Filter.Eventually.of_forall (fun n => by simp))
  filter_upwards [hp, eventually_leaves_target k T hk hT,
    eventually_ge_atTop (2 * (8 * k + 5) + 2)] with n hp hl hn
  intro frame hf hb F hF hanti
  have hpoly : 2 * ((8 * k + 5) * (n + 1) ^ (2 * k + 1)) + 2 ≤
      (n + 1) ^ (2 * k + 2) := by
    have hone : 1 ≤ (n + 1) ^ (2 * k + 1) := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ (2 * (8 * k + 5) + 2) * (n + 1) ^ (2 * k + 1) := by nlinarith
      _ ≤ (n + 1) * (n + 1) ^ (2 * k + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ]; ring
  have hs := leaves_encoding_length frame (arity T n) hf hb (arity_ge_two k T n) F hF
  have hv := hl frame hf hb F hF hanti
  have hp' : ((2 * ((8 * k + 5) * (n + 1) ^ (2 * k + 1)) + 2 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Statement.runtimeScale n := (Nat.cast_le.mpr hpoly).trans hp
  have hm := mul_le_mul hp' hv (Nat.cast_nonneg _) (by positivity)
  have hs' : ((Encoding.encodeList encode
      (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).length : ℝ) ≤
      1 + ((2 * ((8 * k + 5) * (n + 1) ^ (2 * k + 1)) + 2 : ℕ) : ℝ) *
        ((leaves frame (arity T n) hf hb (arity_ge_two k T n) F).length : ℝ) := by
    exact_mod_cast hs
  have heq : (2 : ℝ) ^ Statement.runtimeScale n *
      (2 : ℝ) ^ (129 * Statement.runtimeScale n) =
      (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq] at hm
  have hone : 1 ≤ (2 : ℝ) ^ (130 * Statement.runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (by have := Statement.runtimeScale_nonneg n; positivity)
  linarith

end SubexponentialSAT.SqrtLog.SparsifyProgram

end OAI.Algorithms
