import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientScheduleBounds

namespace OAI.Algorithms

/-!
# Polynomial cost of the actual coefficient program on the dyadic schedule

The finite estimate below bounds the published, measured program budget.
Its only exponential factor is the actual coefficient search count `p^R`.
The scheduled degree makes that factor at most the universal block size,
which is eventually at most the input size. Incoming words may be padded:
their actual length bound is retained as the independent argument `B`.
-/

namespace SubexponentialSAT.SubexpCoefficientBounds

open Filter Subexp SubexpPackingParameters

theorem afterInitBound_le (B : ℕ) :
    SubexpCoefficientProgram.afterInitBound B + 1 ≤ 100000 * (B + 1)^2 := by
  unfold SubexpCoefficientProgram.afterInitBound SubexpCoefficientProgram.initializerBound
  nlinarith

theorem innerBound_le (B A R : ℕ) :
    SubexpCoefficientInputs.innerBound B A R ≤ 100 * (A + R + 1) * (B + 1) := by
  unfold SubexpCoefficientInputs.innerBound
  nlinarith

/-- This includes the binary initializer, unary conversions, all stage
copies, and final output cleanup already charged by the program budget. -/
theorem overhead_le (A R B : ℕ) :
    SubexpCoefficientProgram.overhead A R B ≤
      20000000000 * (A + R + 1) * (B + 1)^2 := by
  let C := SubexpCoefficientProgram.afterInitBound B
  have hi := innerBound_le C A R
  have hc : C + 1 ≤ (A + R + 1) * (C + 1) := by nlinarith
  have hfirst : SubexpCoefficientProgram.overhead A R B ≤
      200000 * (A + R + 1) * (C + 1) := by
    change 2138 * C + 1738 * SubexpCoefficientInputs.innerBound C A R + 2239 ≤ _
    nlinarith
  calc
    SubexpCoefficientProgram.overhead A R B ≤
        200000 * (A + R + 1) * (C + 1) := hfirst
    _ ≤ 200000 * (A + R + 1) * (100000 * (B + 1)^2) :=
      Nat.mul_le_mul_left _ (afterInitBound_le B)
    _ = 20000000000 * (A + R + 1) * (B + 1)^2 := by ring

/-- A finite bound for the full actual program, including preparation.
No running-time premise is assumed: `budget_eq` and the proved coefficient
service estimate account for every charged instruction. -/
theorem budget_le_polynomial_times_power (p r Q R B : ℕ) [Fact p.Prime] :
    SubexpCoefficientProgram.budget p r Q R B ≤
      22000000000 * (B + p + Q + R + MatrixWordEncoding.width p + 2)^7 * p^R := by
  generalize hHdef : B + p + Q + R + MatrixWordEncoding.width p + 2 = H
  let A := SubexpIntervalStart.value r Q R
  have haQ : A ≤ Q := intervalStart_le r Q R
  have hA : A + R + 1 ≤ H := by omega
  have hB : B + 1 ≤ H := by omega
  have hpH : p + 1 ≤ H := by omega
  have hR : R + 1 ≤ H := by omega
  have hw : MatrixWordEncoding.width p + 1 ≤ H := by omega
  have hH : 1 ≤ H := by omega
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpow : 1 ≤ p^R := Nat.one_le_pow _ _ hp
  have hprep : SubexpCoefficientProgram.overhead A R B ≤
      20000000000 * H^7 * p^R := by
    calc
      SubexpCoefficientProgram.overhead A R B ≤
          20000000000 * (A + R + 1) * (B + 1)^2 := overhead_le A R B
      _ ≤ 20000000000 * H * H^2 := by gcongr
      _ = 20000000000 * H^3 := by ring
      _ ≤ 20000000000 * H^7 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hH (by decide : 3 ≤ 7))
      _ = (20000000000 * H^7) * 1 := by ring
      _ ≤ 20000000000 * H^7 * p^R := Nat.mul_le_mul_left _ hpow
  have hsearch : CoefficientSearchService.budget p A R ≤ 2000000 * H^7 * p^R := by
    calc
      CoefficientSearchService.budget p A R ≤
          2000000 * (p + 1) * (A + R + 1) * (R + 1) *
            (MatrixWordEncoding.width p + 1)^2 * p^R :=
        CoefficientSearchService.budget_le p A R
      _ ≤ 2000000 * H * H * H * H^2 * p^R := by gcongr
      _ = 2000000 * H^5 * p^R := by ring
      _ ≤ 2000000 * H^7 * p^R := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hH (by decide : 5 ≤ 7)))
  calc
    SubexpCoefficientProgram.budget p r Q R B =
        SubexpCoefficientProgram.overhead A R B + 538 * CoefficientSearchService.budget p A R :=
      SubexpCoefficientProgram.budget_eq p r Q R B
    _ ≤ 20000000000 * H^7 * p^R + 538 * (2000000 * H^7 * p^R) :=
      Nat.add_le_add hprep (Nat.mul_le_mul_left _ hsearch)
    _ = (20000000000 + 538 * 2000000) * (H^7 * p^R) := by ring
    _ ≤ 22000000000 * (H^7 * p^R) := Nat.mul_le_mul_right _ (by decide)
    _ = 22000000000 * H^7 * p^R := by ring

/-- The program's proved output-word bound is already included in its
budget, so the same polynomial also controls the next phase's input words. -/
theorem wordBound_le_budget (p r Q R B : ℕ) [Fact p.Prime] :
    SubexpCoefficientProgram.wordBound p r Q R B ≤
      SubexpCoefficientProgram.budget p r Q R B := by
  unfold SubexpCoefficientProgram.budget
  omega

attribute [local instance] scheduledPrime

theorem budget_le_of_blockSize_le (k T n B L C0 d0 : ℕ) (hk : 2 ≤ k)
    (hn : GoodInput n) (hblock : DyadicSchedule.N k T n ≤ n)
    (hL : n ≤ L) (hB : B ≤ C0 * (L + 1)^d0) :
    SubexpCoefficientProgram.budget (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.R k T n) B ≤
      (22000000000 * (C0 + 6)^7) * (L + 1)^((d0 + 4) * 7 + 1) := by
  have hsum := scheduled_parameterSum_le_input k T n B L C0 d0 hn hL hB
  have hpower : p n ^ DyadicSchedule.R k T n ≤ L + 1 :=
    (scheduled_coefficientPower_le_blockSize k T n hk hn).trans
      (hblock.trans (hL.trans (Nat.le_succ _)))
  calc
    SubexpCoefficientProgram.budget (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.R k T n) B ≤
      22000000000 * (B + p n + DyadicSchedule.Q n + DyadicSchedule.R k T n +
        MatrixWordEncoding.width (p n) + 2)^7 * p n ^ DyadicSchedule.R k T n :=
      budget_le_polynomial_times_power _ _ _ _ _
    _ ≤ 22000000000 * ((C0 + 6) * (L + 1)^(d0 + 4))^7 * (L + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 7)) hpower
    _ = (22000000000 * (C0 + 6)^7) * ((L + 1)^((d0 + 4) * 7) * (L + 1)) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ = (22000000000 * (C0 + 6)^7) * (L + 1)^((d0 + 4) * 7 + 1) := by
      rw [← pow_succ]

/-- An explicit uniform polynomial for the actual coefficient phase. -/
theorem eventually_budget_explicit (k T : ℕ) (hk : 2 ≤ k) (C0 d0 : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ L B : ℕ, n ≤ L → B ≤ C0 * (L + 1)^d0 →
      SubexpCoefficientProgram.budget (p n) (r n) (DyadicSchedule.Q n)
          (DyadicSchedule.R k T n) B ≤
        (22000000000 * (C0 + 6)^7) * (L + 1)^((d0 + 4) * 7 + 1) := by
  filter_upwards [eventually_goodInput, eventually_blockSize_le k T] with n hn hblock
  intro L B hL hB
  exact budget_le_of_blockSize_le k T n B L C0 d0 hk hn hblock hL hB

/-- The input-polynomial interface for callers with any already proved
polynomial bound on the incoming raw words. -/
theorem eventually_budget_polynomial (k T : ℕ) (hk : 2 ≤ k) (C0 d0 : ℕ) :
    ∃ C d : ℕ, ∀ᶠ n : ℕ in atTop, ∀ L B : ℕ, n ≤ L → B ≤ C0 * (L + 1)^d0 →
      SubexpCoefficientProgram.budget (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.R k T n) B ≤ C * (L + 1)^d :=
  ⟨22000000000 * (C0 + 6)^7, (d0 + 4) * 7 + 1,
    eventually_budget_explicit k T hk C0 d0⟩

/-- The returned raw-word bound is polynomial on the very same inputs. -/
theorem eventually_wordBound_polynomial (k T : ℕ) (hk : 2 ≤ k) (C0 d0 : ℕ) :
    ∃ C d : ℕ, ∀ᶠ n : ℕ in atTop, ∀ L B : ℕ, n ≤ L → B ≤ C0 * (L + 1)^d0 →
      SubexpCoefficientProgram.wordBound (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.R k T n) B ≤ C * (L + 1)^d := by
  obtain ⟨C, d, hevent⟩ := eventually_budget_polynomial k T hk C0 d0
  refine ⟨C, d, ?_⟩
  filter_upwards [hevent] with n hn
  intro L B hL hB
  exact (wordBound_le_budget _ _ _ _ _).trans (hn L B hL hB)

end SubexponentialSAT.SubexpCoefficientBounds

end OAI.Algorithms
