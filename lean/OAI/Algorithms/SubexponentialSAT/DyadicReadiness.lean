import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicSchedule
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval
import OAI.Algorithms.SubexponentialSAT.Subexp.SpectralRank

namespace OAI.Algorithms

/-!
# Readiness and layout inequalities for the implemented dyadic selector

All numerical schedules in this file are `DyadicSchedule` definitions.  The
fixed parameter `T` remains visible.  Readiness uses the proved polynomial
incidence bound for every fixed `k,T`; the separate `Control k T` certificate
is needed for the sparsification budget, not for these layout inequalities.
-/

namespace SubexponentialSAT.DyadicSchedule

open SubexpPackingParameters
open Filter

/-- The floor defining R always respects the degree budget. -/
theorem degree_budget (k T : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    delta k T n * k * (p n - 1) * R k T n < Q n := by
  let a := 8 * delta k T n * k * p n
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (delta_pos k T n))
      (by omega)) (p_prime n).pos
  have hsmall : delta k T n * k * (p n - 1) < a := by
    have hp : 0 < delta k T n * k * p n :=
      Nat.mul_pos (Nat.mul_pos (delta_pos k T n) (by omega)) (p_prime n).pos
    calc
      delta k T n * k * (p n - 1) ≤ delta k T n * k * p n :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < 8 * (delta k T n * k * p n) := by omega
      _ = a := by dsimp [a]; ring
  have hfloor : a * R k T n ≤ Q n := by
    exact Nat.mul_div_le (Q n) a
  by_cases hR : R k T n = 0
  · simp only [hR, Nat.mul_zero]
    exact Q_pos n
  · exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hsmall (Nat.pos_of_ne_zero hR)) hfloor

/-- The genuine multicolor parameter record for the dyadic schedule. -/
def parameters (k T : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : GoodInput n) :
    SubexpLayoutSpec.Parameters (p n) k (delta k T n) (r n) (tau n) where
  h := 4
  Q := Q n
  R := R k T n
  Dstar := Dstar k T n
  p_odd := p_odd n
  k_pos := by omega
  delta_pos := delta_pos k T n
  h_pos := by decide
  Q_eq := rfl
  degree_budget := degree_budget k T hk n
  r_ge_two := goodInput_r_ge_two hn
  tau_pos := tau_pos hn
  tau_le_half := tau_le_half hn

theorem block_threshold_eq (k T : ℕ) {n : ℕ} (hn : GoodInput n) :
    tau n ^ 2 * (Dstar k T n : ℚ) =
      (N k T n : ℚ) ^ 3 * (1 + (delta k T n * k : ℕ)) := by
  have hs : (s n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (goodInput_s_pos hn))
  unfold tau Dstar
  push_cast
  field_simp

theorem ready_goodInput {k T n : ℕ} (hn : Ready k T n) : GoodInput n :=
  hn.1

theorem ready_dimension {k T n : ℕ} (hn : Ready k T n) :
    Dstar k T n ≤ D n := hn.2.2

theorem ready_tail {k T n : ℕ} (hn : Ready k T n) :
    16 * Q n * delta k T n * s n ≤ R k T n ^ 2 := hn.2.1

theorem ready_radius {k T n : ℕ} (hn : Ready k T n) :
    32 ≤ R k T n :=
  SubexpSmallInputs.ready_radius hn
    (SubexpSmallInputs.actualChecks_points_ge_two k (delta k T) n)
    (delta_pos k T n)

theorem four_mul_R_le_Q (k T : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    4 * R k T n ≤ Q n :=
  SubexpParameters.four_mul_degreeR_le_Q
    (by have h := p_gt_two n; omega) (by omega) (delta_pos k T n)

/-- Both growing arithmetic checks hold eventually for every fixed k,T.
No tail or block-threshold assumption is supplied by the caller. -/
theorem eventually_ready (k T : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, Ready k T n := by
  obtain ⟨C, d, h⟩ := exists_incidence_bound k T
  exact SubexpSmallInputs.eventually_actual_ready_of_polynomial_bound
    k C d (by omega) (delta k T) (fun n _ => delta_pos k T n) h

theorem eventually_tail (k T : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, 16 * Q n * delta k T n * s n ≤ R k T n ^ 2 :=
  (eventually_ready k T hk).mono (fun _ hn => ready_tail hn)

theorem eventually_dimension (k T : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, Dstar k T n ≤ D n :=
  (eventually_ready k T hk).mono (fun _ hn => ready_dimension hn)

/-- Failed checks occur below one fixed input-size cutoff. -/
theorem exists_fallback_cutoff (k T : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n, ¬ Ready k T n → n < cutoff :=
  SubexpSmallInputs.fallback_bounded_of_eventually (eventually_ready k T hk)

@[simp] theorem not_ready_zero (k T : ℕ) : ¬ Ready k T 0 :=
  SubexpSmallInputs.not_ready_zero (checks k T)

@[simp] theorem not_ready_one (k T : ℕ) : ¬ Ready k T 1 :=
  SubexpSmallInputs.not_ready_one (checks k T)

/-- The exact universal-type threshold needed by the layout constructor. -/
theorem parameter_threshold (k T : ℕ) (hk : 2 ≤ k) {n : ℕ} (hn : GoodInput n) :
    (Fintype.card (MulticolorTypes.UniversalType (r n)
      (parameters k T hk n hn).Q (delta k T n)) : ℚ) ^ 3 *
        (1 + (delta k T n * k : ℕ)) ≤
      tau n ^ 2 * (parameters k T hk n hn).Dstar := by
  change (Fintype.card (MulticolorTypes.UniversalType (r n) (Q n)
    (delta k T n)) : ℚ) ^ 3 * (1 + (delta k T n * k : ℕ)) ≤
      tau n ^ 2 * (Dstar k T n : ℚ)
  rw [block_threshold_eq k T hn]
  have hc : Fintype.card (MulticolorTypes.UniversalType (r n) (Q n)
      (delta k T n)) = N k T n := by
    simpa only [N, Q, SubexpParameters.blockSize, r] using
      MulticolorTypes.card_universalType (r n) (Q n) (delta k T n)
  rw [hc]

/-- The integer readiness guard implies the degree-cleared tensor tail bound
used by the actual multicolor layout constructor. -/
theorem weighted_tail {k T n : ℕ} (hk : 2 ≤ k) (hn : Ready k T n) :
    (delta k T n : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (Q n - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity (r n))
        (SubexpSwapMultiplicity.negativeMultiplicity (r n))
        (intervalStart k T n) (R k T n) : ℚ) ≤
      tau n * (((SubexpSwapMultiplicity.positiveMultiplicity (r n) +
        SubexpSwapMultiplicity.negativeMultiplicity (r n)) ^ (Q n - 1) : ℕ) : ℚ) := by
  have hr := goodInput_r_ge_two (ready_goodInput hn)
  apply (Subexp.SpectralRank.normalizedTail_le_iff (r n) (Q n - 1)
    (intervalStart k T n) (R k T n) (delta k T n) (tau n)
    (by omega) (delta_pos k T n)).mp
  have ht := Subexp.TailInterval.interval_tail_bound hr (ready_radius hn)
    (four_mul_R_le_Q k T hk n) (delta_pos k T n)
    (goodInput_s_pos (ready_goodInput hn)) (ready_tail hn)
  convert ht using 1
  · rfl
  · simp [tau, div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- A single finite fallback machine handles every failed dyadic guard.
This does not claim that the guard or the large-input solver is compiled. -/
theorem fallback_machine (k T : ℕ) (hk : 2 ≤ k) {A : ℝ} (hA : 0 ≤ A) :
    ∃ cutoff : ℕ, ∀ (n : ℕ) (F : SAT.CNF (Fin n)),
      ¬ Ready k T n →
      ∃ (answer : Bool) (time : ℕ),
        (FixedParameters.smallSolver cutoff).OutputsInTime (Encoding.encodeCNF F) answer time ∧
        (answer = true ↔ SAT.Satisfiable F) ∧
        (time : ℝ) ≤ SubexpComputation.runtimeBound 1 A 1 (Encoding.formulaBitLength F) n :=
  SubexpSmallInputs.exists_machine_for_fallback (eventually_ready k T hk) hA

end SubexponentialSAT.DyadicSchedule

end OAI.Algorithms
