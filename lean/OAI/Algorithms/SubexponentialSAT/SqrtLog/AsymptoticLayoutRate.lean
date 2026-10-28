import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_w_sq_le_s : ∀ᶠ n : ℕ in atTop, w n ^ 2 ≤ s n := by
  filter_upwards [eventually_w_power_le_L 8 (show (0 : ℝ) < 1 by norm_num)] with n hn
  apply (le_s_iff n (w n ^ 2)).2
  simp only [one_mul] at hn
  have hnat : w n ^ 8 ≤ L n := by exact_mod_cast hn
  convert hnat using 1 ; ring

theorem eventually_w_le_log_r :
    ∀ᶠ n : ℕ in atTop, w n ≤ 7 * (Nat.log2 (layoutR n) + 1) := by
  filter_upwards [eventually_w_sq_le_s] with n hn
  have hr : s n ≤ layoutR n := le_max_right _ _
  have hr2 := layoutR_ge_two n
  have hw : w n ^ 2 ≤ layoutR n := hn.trans hr
  have hw4 : w n ^ 4 ≤ layoutR n ^ 2 := by
    have h := Nat.pow_le_pow_left hw 2
    convert h using 1 ; ring
  have hsp : s n + 1 ≤ 2 * layoutR n := by omega
  have hL : L n ≤ 4 * layoutR n ^ 4 := by
    calc
      L n ≤ (s n + 1) ^ 2 * w n ^ 4 := (schedule_maximal n).le
      _ ≤ (2 * layoutR n) ^ 2 * layoutR n ^ 2 := by gcongr
      _ = _ := by ring
  have hpow : L n ≤ 2 ^ (2 + 4 * (Nat.log2 (layoutR n) + 1)) := by
    calc
      L n ≤ 4 * layoutR n ^ 4 := hL
      _ ≤ 4 * (2 ^ (Nat.log2 (layoutR n) + 1)) ^ 4 := by
        exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left Nat.lt_log2_self.le 4)
      _ = _ := by rw [← pow_mul]; norm_num [pow_add, Nat.mul_comm]
  have hlog := Nat.log_mono_right (b := 2) hpow
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  unfold w
  rw [Nat.log2_eq_log_two]
  nlinarith

theorem eventually_layoutCutoff_sq_le (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, layoutCutoff n (b n) ^ 2 ≤ (28 * q + 312) * L n := by
  filter_upwards [hb, eventually_w_le_log_r] with n hn hw
  have he := layoutEnergy_le n (b n) q hn
  have hbudget : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n :=
    Nat.mul_div_le (L n) (layoutDen n)
  have hQE : 64 * layoutQ n * layoutEnergy n (b n) ≤ 7 * (q + 10) * L n := by
    calc
      64 * layoutQ n * layoutEnergy n (b n) ≤ 64 * layoutQ n * ((q + 10) * w n) := by gcongr
      _ ≤ 64 * layoutQ n * ((q + 10) * (7 * (Nat.log2 (layoutR n) + 1))) := by gcongr
      _ = 7 * (q + 10) * (64 * (Nat.log2 (layoutR n) + 1) * layoutQ n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hbudget
  have hroot := Nat.sqrt_le' (128 * layoutQ n * layoutEnergy n (b n))
  have hL := L_pos n
  have hsmall (x : ℕ) : (x + 4) ^ 2 ≤ 2 * x ^ 2 + 32 := by
    have hi : ((x : ℤ) + 4) ^ 2 ≤ 2 * (x : ℤ) ^ 2 + 32 := by
      nlinarith [sq_nonneg ((x : ℤ) - 4)]
    exact_mod_cast hi
  unfold layoutCutoff
  calc
    _ ≤ 2 * Nat.sqrt (128 * layoutQ n * layoutEnergy n (b n)) ^ 2 + 32 := hsmall _
    _ ≤ 256 * layoutQ n * layoutEnergy n (b n) + 32 := by nlinarith
    _ ≤ (28 * q + 312) * L n := by nlinarith

theorem eventually_layoutQ_comparison :
    ∀ᶠ n : ℕ in atTop,
      L n ≤ 128 * layoutQ n * w n ∧ 64 * layoutQ n * w n ≤ 7 * L n := by
  filter_upwards [eventually_layoutQ_ge 1, eventually_w_le_log_r] with n hQ hw
  have hb : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n :=
    Nat.mul_div_le (L n) (layoutDen n)
  have hd := layoutDen_le n
  have hdiv := Nat.div_add_mod (L n) (layoutDen n)
  have hmod := Nat.mod_lt (L n) (layoutDen_pos n)
  change layoutDen n * layoutQ n + L n % layoutDen n = L n at hdiv
  constructor
  · have hm := Nat.mul_le_mul_left (layoutQ n + 1) hd
    nlinarith
  · have hm := Nat.mul_le_mul_left (64 * layoutQ n) hw
    nlinarith

theorem eventually_L_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ L n := by
  filter_upwards [eventually_le_s a] with n hn
  exact hn.trans (s_le_L n)

theorem eventually_absorb_L_coefficient (b : ℕ → ℕ) (C q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ C * L n ^ q) :
    ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ (q + 1) := by
  filter_upwards [hb, eventually_L_ge C] with n hn hC
  exact hn.trans (by simpa [pow_succ, mul_comm] using Nat.mul_le_mul_right (L n ^ q) hC)

theorem polynomial_schedule_has_L_power (b : ℕ → ℕ)
    (hb : SparsificationConstants.PolynomialBound b) :
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop, b (s n) ≤ L n ^ q := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power hb
  refine ⟨q + 1, eventually_absorb_L_coefficient (fun n => b (s n)) (3 ^ q) q ?_⟩
  apply Filter.Eventually.of_forall
  intro n
  have hs : s n + 2 ≤ 3 * L n := by have := s_le_L n; have := L_pos n; omega
  calc
    b (s n) ≤ (s n + 2) ^ q := hq (s n)
    _ ≤ (3 * L n) ^ q := Nat.pow_le_pow_left hs q
    _ = 3 ^ q * L n ^ q := mul_pow _ _ _

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
