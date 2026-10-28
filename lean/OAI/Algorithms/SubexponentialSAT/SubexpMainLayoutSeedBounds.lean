import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutScheduleBounds

namespace OAI.Algorithms

/-! The numerical seed used by the actual layout aggregation. Fixed powers
of the scheduled parameters are retained explicitly and absorbed into an
input-length polynomial. Only the local search envelope enters the scale. -/

namespace SubexponentialSAT.SubexpMainLayoutSeedBounds

open Filter SubexpPackingParameters SubexpMainLayoutScheduleBounds

def seed (k T n W D : ℕ) : ℕ :=
  W + n + k + p n + (p n)^k + r n + DyadicSchedule.Q n +
    DyadicSchedule.delta k T n + DyadicSchedule.R k T n + D + envelope k T n + 1

def degree (k d0 q : ℕ) : ℕ := (d0 + 2 * k + 2) * q

theorem seed_succ_le_polynomial_envelope
    (k T n C0 d0 L D W : ℕ) (hn : GoodInput n)
    (hN : DyadicSchedule.N k T n ≤ n)
    (hnL : n ≤ L) (hD : D ≤ n)
    (hW : W ≤ C0 * (L + 1)^d0 + (8 * k + 5) * (L + 1)^(2 * k + 1)) :
    seed k T n W D + 1 ≤
      (C0 + 9 * k + 20) * (L + 1)^(d0 + 2 * k + 1) + L + envelope k T n + 1 := by
  let a := d0 + 2 * k + 1
  let A := (L + 1)^a
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hLa : L ≤ A :=
    (Nat.le_succ L).trans (Nat.le_self_pow (by dsimp [a]; omega) (L + 1))
  have hpow (j : ℕ) (hj : j ≤ a) : (L + 1)^j ≤ A :=
    Nat.pow_le_pow_right (by omega) hj
  have hW' : W ≤ (C0 + 8 * k + 5) * A := by
    calc
      W ≤ C0 * (L + 1)^d0 + (8 * k + 5) * (L + 1)^(2 * k + 1) := hW
      _ ≤ C0 * A + (8 * k + 5) * A :=
        Nat.add_le_add (Nat.mul_le_mul_left C0 (hpow d0 (by dsimp [a]; omega)))
          (Nat.mul_le_mul_left (8 * k + 5) (hpow (2 * k + 1) (by dsimp [a]; omega)))
      _ = (C0 + 8 * k + 5) * A := by ring
  have hb := Subexp.LocalBasisBatchScheduleBounds.block_bounds k T n hn
  have hnA : n ≤ A := hnL.trans hLa
  have hpA : p n ≤ A := hb.prime_le.trans (hN.trans hnA)
  have hrA : r n ≤ A := hb.color_le.trans (hN.trans hnA)
  have hQA : DyadicSchedule.Q n ≤ A := hb.position_le.trans (hN.trans hnA)
  have hdeltaA : DyadicSchedule.delta k T n ≤ A := hb.slot_le.trans (hN.trans hnA)
  have hRA : DyadicSchedule.R k T n ≤ A := hb.degree_le.trans (hN.trans hnA)
  have hDA : D ≤ A := hD.trans hnA
  have hkA : k ≤ k * A := by simpa only [mul_one] using Nat.mul_le_mul_left k hA
  have hpL : p n ≤ L + 1 := hb.prime_le.trans (hN.trans (hnL.trans (Nat.le_succ L)))
  have hpk : (p n)^k ≤ A :=
    (Nat.pow_le_pow_left hpL k).trans (hpow k (by dsimp [a]; omega))
  change W + n + k + p n + (p n)^k + r n + DyadicSchedule.Q n +
    DyadicSchedule.delta k T n + DyadicSchedule.R k T n + D + envelope k T n + 1 + 1 ≤
      (C0 + 9 * k + 20) * A + L + envelope k T n + 1
  nlinarith only [hW', hnA, hpA, hrA, hQA, hdeltaA, hRA, hDA, hkA, hpk, hA]

/-- The constants and degree are chosen before n, L, D and W. The input
length is arbitrary above n; its polynomial factor is not absorbed into the
subexponential term. In particular the p^k term in seed is fully charged. -/
theorem eventually_seed_pow_le_runtimeBound (k T C q C0 d0 : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ L D W : ℕ,
      n ≤ L → D ≤ n →
      W ≤ C0 * (L + 1)^d0 + (8 * k + 5) * (L + 1)^(2 * k + 1) →
      ((C * (seed k T n W D + 1)^q : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound 1 1 (degree k d0 q) L n := by
  filter_upwards [eventually_goodInput,
    Subexp.LocalBasisBatchScheduleBounds.block_powers k T 1,
    eventually_polynomial_envelope k T C (C0 + 9 * k + 20) (d0 + 2 * k + 1) q]
    with n hn hN hpoly
  intro L D W hnL hD hW
  have hN' : DyadicSchedule.N k T n ≤ n := by simpa only [pow_one] using hN
  have hseed := seed_succ_le_polynomial_envelope k T n C0 d0 L D W hn hN' hnL hD hW
  have hcost := (Nat.cast_le (α := ℝ)).mpr
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hseed q))
  apply hcost.trans
  simpa only [SubexpComputation.runtimeBound, one_mul, degree, Nat.add_assoc] using hpoly L

end SubexponentialSAT.SubexpMainLayoutSeedBounds

end OAI.Algorithms
