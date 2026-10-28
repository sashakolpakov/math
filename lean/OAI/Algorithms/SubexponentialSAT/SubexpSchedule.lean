import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpParameters
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget
import OAI.Algorithms.SubexponentialSAT.SubexpSmallInputs
import OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval
import OAI.Algorithms.SubexponentialSAT.Subexp.SpectralRank

namespace OAI.Algorithms

/-!
# The actual input-dependent parameter schedule

The width `k` is fixed before the input is supplied. All other displayed
parameters are computed from the prepared variable count. The reciprocal
sparsification budget is tested by exact natural-number arithmetic, and the
prime comes from the bounded search in `SubexpPackingParameters`.
-/

namespace SubexponentialSAT.SubexpSchedule

open SubexpPackingParameters
open Filter

/-- Threshold parameter for the exact reciprocal budget `1 / s n`. -/
def M (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  SparsificationBudget.chooseM k hk (s n)

theorem M_ge_two (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : 2 ≤ M k hk n :=
  SparsificationBudget.chooseM_ge_two k hk (s n)

/-- Occurrence bound of the actual quantitative sparsification leaves. -/
def B (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  SparsificationConstants.occurrenceCap (M k hk n) k

/-- The extra one is the unary validity factor at each packed coordinate. -/
def delta (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  1 + ell n * B k hk n

theorem delta_pos (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : 0 < delta k hk n := by
  simp only [delta]
  omega

def tau (n : ℕ) : ℚ := 1 / (s n : ℚ)

def Q (n : ℕ) : ℕ := SubexpParameters.sizeQ (p n)

def R (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  SubexpParameters.degreeR (p n) k (delta k hk n)

def N (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  SubexpParameters.blockSize (s n) (p n) (delta k hk n)

/-- No ceiling is needed: `tau⁻² = s²` and the remaining factors are integers. -/
def Dstar (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  s n ^ 2 * N k hk n ^ 3 * (1 + delta k hk n * k)

theorem tau_pos {n : ℕ} (hn : GoodInput n) : 0 < tau n := by
  unfold tau
  exact one_div_pos.mpr (Nat.cast_pos.mpr (goodInput_s_pos hn))

theorem tau_le_half {n : ℕ} (hn : GoodInput n) : tau n ≤ 1 / 2 := by
  have hs : (2 : ℚ) ≤ s n := by
    exact_mod_cast (show 2 ≤ s n by have h := hn; unfold GoodInput at h; omega)
  exact one_div_le_one_div_of_le (by norm_num) hs

theorem Q_pos (n : ℕ) : 0 < Q n := by
  have hp : 2 ≤ p n := le_of_lt (p_gt_two n)
  have hh := Nat.pow_le_pow_left hp 4
  change 0 < p n ^ 4 - 1
  norm_num at hh
  omega

/-- The degree budget holds even when the floor gives zero. Readiness tests
separately ensure that the interpolation interval is large enough. -/
theorem degree_budget (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    delta k hk n * k * (p n - 1) * R k hk n < Q n := by
  let a := 8 * delta k hk n * k * p n
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (delta_pos k hk n))
      (by omega)) (p_prime n).pos
  have hsmall : delta k hk n * k * (p n - 1) < a := by
    have hp : 0 < delta k hk n * k * p n :=
      Nat.mul_pos (Nat.mul_pos (delta_pos k hk n) (by omega)) (p_prime n).pos
    calc
      delta k hk n * k * (p n - 1) ≤ delta k hk n * k * p n :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < 8 * (delta k hk n * k * p n) := by omega
      _ = a := by dsimp [a]; ring
  have hfloor : a * R k hk n ≤ Q n := by
    exact Nat.mul_div_le (Q n) a
  by_cases hR : R k hk n = 0
  · simp only [hR, Nat.mul_zero]
    exact Q_pos n
  · exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hsmall (Nat.pos_of_ne_zero hR)) hfloor

/-- The actual multicolor parameter record, before a factor pattern is given. -/
def parameters (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : GoodInput n) :
    SubexpLayoutSpec.Parameters (p n) k (delta k hk n) (r n) (tau n) where
  h := 4
  Q := Q n
  R := R k hk n
  Dstar := Dstar k hk n
  p_odd := p_odd n
  k_pos := by omega
  delta_pos := delta_pos k hk n
  h_pos := by decide
  Q_eq := rfl
  degree_budget := degree_budget k hk n
  r_ge_two := goodInput_r_ge_two hn
  tau_pos := tau_pos hn
  tau_le_half := tau_le_half hn

theorem block_threshold_eq (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hn : GoodInput n) :
    tau n ^ 2 * (Dstar k hk n : ℚ) =
      (N k hk n : ℚ) ^ 3 * (1 + (delta k hk n * k : ℕ)) := by
  have hs : (s n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (goodInput_s_pos hn))
  unfold tau Dstar
  push_cast
  field_simp

/-- The occurrence polynomial's constants are selected for `k` before `n`. -/
theorem exists_occurrence_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, ∀ n, GoodInput n → B k hk n ≤ C * (s n + 1) ^ d := by
  obtain ⟨C, d, h⟩ := SparsificationBudget.chosenOccurrenceCap_polynomialBound k hk
  refine ⟨C, d, ?_⟩
  intro n hn
  have hs : 2 ≤ s n := by unfold GoodInput at hn; omega
  exact (h (s n) hs).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_succ _) d))

/-- Packing increases the fixed polynomial degree by at most one. -/
theorem exists_incidence_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, ∀ n, GoodInput n → delta k hk n ≤ C * (s n + 1) ^ d := by
  obtain ⟨C, d, h⟩ := exists_occurrence_bound k hk
  refine ⟨C + 1, d + 1, ?_⟩
  intro n hn
  have hell : ell n ≤ s n + 1 := (u_le_s n).trans (Nat.le_succ _)
  have hp : 1 ≤ (s n + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  calc
    delta k hk n = 1 + ell n * B k hk n := rfl
    _ ≤ 1 + (s n + 1) * (C * (s n + 1) ^ d) := by
      gcongr
      exact h n hn
    _ = 1 + C * (s n + 1) ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ (C + 1) * (s n + 1) ^ (d + 1) := by nlinarith

/-- These are exactly the natural-valued checks implemented by the source's
main-branch guard. The parameter record itself requires no tail assumption. -/
def checks (k : ℕ) (hk : 2 ≤ k) : SubexpSmallInputs.CheckData :=
  SubexpSmallInputs.actualChecks k (delta k hk)

def Ready (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : Prop :=
  SubexpSmallInputs.Ready (checks k hk) n

instance (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : Decidable (Ready k hk n) :=
  inferInstanceAs (Decidable (SubexpSmallInputs.Ready (checks k hk) n))

theorem ready_goodInput {k n : ℕ} {hk : 2 ≤ k} (hn : Ready k hk n) : GoodInput n :=
  hn.1

theorem ready_dimension {k n : ℕ} {hk : 2 ≤ k} (hn : Ready k hk n) :
    Dstar k hk n ≤ D n := hn.2.2

theorem ready_tail {k n : ℕ} {hk : 2 ≤ k} (hn : Ready k hk n) :
    16 * Q n * delta k hk n * s n ≤ R k hk n ^ 2 := hn.2.1

theorem ready_radius {k n : ℕ} {hk : 2 ≤ k} (hn : Ready k hk n) :
    32 ≤ R k hk n :=
  SubexpSmallInputs.ready_radius hn
    (SubexpSmallInputs.actualChecks_points_ge_two k (delta k hk) n)
    (delta_pos k hk n)

theorem four_mul_R_le_Q (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : 4 * R k hk n ≤ Q n :=
  SubexpParameters.four_mul_degreeR_le_Q
    (by have h := p_gt_two n; omega) (by omega) (delta_pos k hk n)

/-- Both substantive numerical checks eventually pass for the selected prime
and the selected sparsification threshold. No tail or block-growth assumption
remains in this theorem. -/
theorem eventually_ready (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, Ready k hk n := by
  obtain ⟨C, d, h⟩ := exists_incidence_bound k hk
  have he : ∀ᶠ n in atTop, delta k hk n ≤ C * (s n + 1) ^ d := by
    filter_upwards [SubexpPackingParameters.eventually_goodInput] with n hn
    exact h n hn
  exact SubexpSmallInputs.eventually_actual_ready k C d (by omega)
    (delta k hk) (fun n _ => delta_pos k hk n) h
    (SubexpParameters.blockThreshold_eventually_le_D C d k (delta k hk) he)

/-- One fixed cutoff suffices for every failure of the growing-parameter guard. -/
theorem exists_fallback_cutoff (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n, ¬ Ready k hk n → n < cutoff :=
  SubexpSmallInputs.fallback_bounded_of_eventually (eventually_ready k hk)

@[simp] theorem not_ready_zero (k : ℕ) (hk : 2 ≤ k) : ¬ Ready k hk 0 :=
  SubexpSmallInputs.not_ready_zero (checks k hk)

@[simp] theorem not_ready_one (k : ℕ) (hk : 2 ≤ k) : ¬ Ready k hk 1 :=
  SubexpSmallInputs.not_ready_one (checks k hk)

/-- The interpolation interval is computed from the actual swap mean. -/
def intervalStart (k : ℕ) (hk : 2 ≤ k) (n : ℕ) : ℕ :=
  Subexp.TailInterval.intervalStart (r n) (Q n) (R k hk n)

theorem parameter_threshold (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hn : GoodInput n) :
    (Fintype.card (MulticolorTypes.UniversalType (r n)
      (parameters k hk n hn).Q (delta k hk n)) : ℚ) ^ 3 *
        (1 + (delta k hk n * k : ℕ)) ≤
      tau n ^ 2 * (parameters k hk n hn).Dstar := by
  change (Fintype.card (MulticolorTypes.UniversalType (r n) (Q n)
    (delta k hk n)) : ℚ) ^ 3 * (1 + (delta k hk n * k : ℕ)) ≤
      tau n ^ 2 * (Dstar k hk n : ℚ)
  rw [block_threshold_eq k hk hn]
  have hc : Fintype.card (MulticolorTypes.UniversalType (r n) (Q n)
      (delta k hk n)) = N k hk n := by
    simpa only [N, Q, SubexpParameters.blockSize, r] using
      MulticolorTypes.card_universalType (r n) (Q n) (delta k hk n)
  rw [hc]

/-- The exact degree-cleared tensor-multiplicity tail used by the actual
multicolor layout constructor follows from the source's numerical guard. -/
theorem weighted_tail {k n : ℕ} {hk : 2 ≤ k} (hn : Ready k hk n) :
    (delta k hk n : ℚ) *
      (Subexp.TensorSpectrum.weightedTail (Q n - 1)
        (SubexpSwapMultiplicity.positiveMultiplicity (r n))
        (SubexpSwapMultiplicity.negativeMultiplicity (r n))
        (intervalStart k hk n) (R k hk n) : ℚ) ≤
      tau n * (((SubexpSwapMultiplicity.positiveMultiplicity (r n) +
        SubexpSwapMultiplicity.negativeMultiplicity (r n)) ^ (Q n - 1) : ℕ) : ℚ) := by
  have hr := goodInput_r_ge_two (ready_goodInput hn)
  apply (Subexp.SpectralRank.normalizedTail_le_iff (r n) (Q n - 1)
    (intervalStart k hk n) (R k hk n) (delta k hk n) (tau n)
    (by omega) (delta_pos k hk n)).mp
  have ht := Subexp.TailInterval.interval_tail_bound hr (ready_radius hn)
    (four_mul_R_le_Q k hk n) (delta_pos k hk n)
    (goodInput_s_pos (ready_goodInput hn)) (ready_tail hn)
  convert ht using 1
  · rfl
  · simp [tau, div_eq_mul_inv, mul_inv_rev, mul_comm]

end SubexponentialSAT.SubexpSchedule

end OAI.Algorithms
