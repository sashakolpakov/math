import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

namespace OAI.Algorithms

/-! A shared local exponential envelope for the actual dyadic layout.
Fixed powers and fixed multipliers fit the scale. An arbitrary input-length
polynomial stays outside that exponential, uniformly in the input length. -/

namespace SubexponentialSAT.SubexpMainLayoutScheduleBounds

open Filter SubexpPackingParameters
open Subexp

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def envelope (k T n : ℕ) : ℕ :=
  LocalBasisBatchBounds.executionBound (LocalBasisBatchScheduleBounds.localSize k T n)

theorem envelope_eq_two_pow (k T n : ℕ) :
    envelope k T n = 2 ^ (2000000000000000000000000000 * (DyadicSchedule.N k T n + 2)^10) := by
  simp only [envelope, LocalBasisBatchBounds.executionBound,
    LocalBasisBatchScheduleBounds.localSize, Nat.add_assoc]

theorem envelope_pos (k T n : ℕ) : 0 < envelope k T n :=
  pow_pos (by decide) _

theorem one_le_envelope (k T n : ℕ) : 1 ≤ envelope k T n := envelope_pos k T n

theorem self_le_executionBound (U : ℕ) : U ≤ LocalBasisBatchBounds.executionBound U := by
  have hu : U ≤ (U + 1)^10 :=
    (Nat.le_succ U).trans (Nat.le_self_pow (by decide) (U + 1))
  have hc : (U + 1)^10 ≤ 2000000000000000000000000000 * (U + 1)^10 := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right ((U + 1)^10) (show 1 ≤ 2000000000000000000000000000 by decide)
  exact Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (hu.trans hc))

theorem localSize_le_envelope (k T n : ℕ) :
    LocalBasisBatchScheduleBounds.localSize k T n ≤ envelope k T n :=
  self_le_executionBound _

theorem N_le_envelope (k T n : ℕ) : DyadicSchedule.N k T n ≤ envelope k T n :=
  (Nat.le_succ _).trans (localSize_le_envelope k T n)

theorem r_pow_universal_eq_N (k T n : ℕ) :
    r n ^ (DyadicSchedule.Q n * (DyadicSchedule.delta k T n + 1)) = DyadicSchedule.N k T n :=
  rfl

theorem r_pow_universal_le_envelope (k T n : ℕ) :
    r n ^ (DyadicSchedule.Q n * (DyadicSchedule.delta k T n + 1)) ≤ envelope k T n :=
  N_le_envelope k T n

theorem parameters_le_envelope (k T n : ℕ) (hn : GoodInput n) :
    r n ≤ envelope k T n ∧ DyadicSchedule.Q n ≤ envelope k T n ∧
    DyadicSchedule.delta k T n ≤ envelope k T n ∧
    DyadicSchedule.R k T n ≤ envelope k T n ∧ p n ≤ envelope k T n ∧
    Subexp.MatrixWordEncoding.width (p n) ≤ envelope k T n := by
  obtain ⟨hr, hQ, hd, hR, hp, hw, _⟩ := LocalBasisBatchScheduleBounds.parameters_le k T n hn
  have he := localSize_le_envelope k T n
  exact ⟨hr.trans he, hQ.trans he, hd.trans he, hR.trans he, hp.trans he, hw.trans he⟩

theorem bounded_pow_le_executionBound {a b U : ℕ} (ha : a ≤ U) (hb : b ≤ U) :
    a^b ≤ LocalBasisBatchBounds.executionBound U := by
  have he : U * b ≤ 2000000000000000000000000000 * (U + 1)^10 := by
    calc
      U * b ≤ U * U := Nat.mul_le_mul_left U hb
      _ ≤ (U + 1)^2 := by nlinarith
      _ ≤ (U + 1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ _ := by
        simpa only [one_mul] using Nat.mul_le_mul_right ((U + 1)^10)
          (show 1 ≤ 2000000000000000000000000000 by decide)
  exact (SubexpBlockSizeBounds.alphabet_pow_le ha).trans
    (Nat.pow_le_pow_right (by decide) he)

theorem p_pow_R_le_envelope (k T n : ℕ) (hn : GoodInput n) :
    p n ^ DyadicSchedule.R k T n ≤ envelope k T n := by
  obtain ⟨_, _, _, hR, hp, _, _⟩ := LocalBasisBatchScheduleBounds.parameters_le k T n hn
  exact bounded_pow_le_executionBound hp hR

theorem Q_pow_r_le_envelope (k T n : ℕ) (hn : GoodInput n) :
    DyadicSchedule.Q n ^ r n ≤ envelope k T n := by
  obtain ⟨hr, hQ, _, _, _, _, _⟩ := LocalBasisBatchScheduleBounds.parameters_le k T n hn
  exact bounded_pow_le_executionBound hQ hr

theorem r_pow_Q_le_envelope (k T n : ℕ) (hn : GoodInput n) :
    r n ^ DyadicSchedule.Q n ≤ envelope k T n := by
  obtain ⟨hr, hQ, _, _, _, _, _⟩ := LocalBasisBatchScheduleBounds.parameters_le k T n hn
  exact bounded_pow_le_executionBound hr hQ

theorem sourceBudget_le_envelope (k T n : ℕ) (hn : GoodInput n)
    (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
    (coefficients alphabet : List (ZMod (p n)))
    (hR : coefficients.length = DyadicSchedule.R k T n) (hcard : alphabet.length = p n) :
    Subexp.LocalBasisBatchProgram.sourceBudget (Δ := DyadicSchedule.delta k T n)
      (p n) hr hQ coefficients alphabet ≤ envelope k T n :=
  LocalBasisBatchScheduleBounds.sourceBudget_le k T n hn hr hQ coefficients alphabet hR hcard

/-- The exponent coefficient depends only on the fixed multiplier and power. -/
theorem mul_succ_pow_executionBound_le (factor q U : ℕ) :
    factor * (LocalBasisBatchBounds.executionBound U + 1)^q ≤
      2 ^ ((factor + q * (2000000000000000000000000000 + 1)) * (U + 1)^10) := by
  let A := (U + 1)^10
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hX : 1 ≤ LocalBasisBatchBounds.executionBound U := Nat.one_le_pow _ _ (by decide)
  have hsucc : LocalBasisBatchBounds.executionBound U + 1 ≤
      2 ^ (2000000000000000000000000000 * A + 1) := by
    rw [pow_succ]
    change LocalBasisBatchBounds.executionBound U + 1 ≤
      LocalBasisBatchBounds.executionBound U * 2
    omega
  have hf : factor ≤ factor * A := by simpa only [mul_one] using Nat.mul_le_mul_left factor hA
  have hq : q ≤ q * A := by simpa only [mul_one] using Nat.mul_le_mul_left q hA
  have he : factor + (2000000000000000000000000000 * A + 1) * q ≤
      (factor + q * (2000000000000000000000000000 + 1)) * A := by
    nlinarith only [hf, hq]
  calc
    _ ≤ 2^factor * (2 ^ (2000000000000000000000000000 * A + 1))^q :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hsucc q)
    _ = 2 ^ (factor + (2000000000000000000000000000 * A + 1) * q) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem eventually_mul_succ_pow_envelope_le_scale (k T factor q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((factor * (envelope k T n + 1)^q : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [LocalBasisBatchScheduleBounds.eventually_two_pow_polynomial_le_scale k T
    (factor + q * (2000000000000000000000000000 + 1)) 10] with n hn
  exact (Nat.cast_le.mpr
    (mul_succ_pow_executionBound_le factor q (LocalBasisBatchScheduleBounds.localSize k T n))).trans hn

/-- No restriction on the input length L is used. Its polynomial remains
an external factor; only the local exponential term is later absorbed. -/
theorem polynomial_envelope_le (C C0 d0 q L E : ℕ) :
    C * (C0 * (L + 1)^d0 + L + E + 1)^q ≤
      (L + 1)^((d0 + 1) * q) * ((C * (C0 + 2)^q) * (E + 1)^q) := by
  let A := (L + 1)^(d0 + 1)
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hd : (L + 1)^d0 ≤ A := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : L ≤ A := (Nat.le_succ L).trans (Nat.le_self_pow (by omega) (L + 1))
  have hAB : A ≤ A * (E + 1) := by
    simpa only [mul_one] using Nat.mul_le_mul_left A (show 1 ≤ E + 1 by omega)
  have hBA : E + 1 ≤ A * (E + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (E + 1) hA
  have hterm := Nat.mul_le_mul_left C0 (hd.trans hAB)
  have hL' := hL.trans hAB
  have hsum : C0 * (L + 1)^d0 + L + E + 1 ≤ (C0 + 2) * A * (E + 1) := by
    nlinarith only [hterm, hL', hBA]
  calc
    _ ≤ C * ((C0 + 2) * A * (E + 1))^q := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsum q)
    _ = _ := by simp only [A, mul_pow, ← pow_mul]; ring

/-- All constants are fixed before n and the universally quantified L.
The polynomial in L is deliberately not absorbed into the n-dependent scale. -/
theorem eventually_polynomial_envelope (k T C C0 d0 q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ L : ℕ,
      ((C * (C0 * (L + 1)^d0 + L + envelope k T n + 1)^q : ℕ) : ℝ) ≤
        ((L : ℝ) + 1)^((d0 + 1) * q) * (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_mul_succ_pow_envelope_le_scale k T (C * (C0 + 2)^q) q]
    with n hn
  intro L
  calc
    _ ≤ ((L : ℝ) + 1)^((d0 + 1) * q) *
        (((C * (C0 + 2)^q) * (envelope k T n + 1)^q : ℕ) : ℝ) := by
      exact_mod_cast polynomial_envelope_le C C0 d0 q L (envelope k T n)
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

end SubexponentialSAT.SubexpMainLayoutScheduleBounds

end OAI.Algorithms
