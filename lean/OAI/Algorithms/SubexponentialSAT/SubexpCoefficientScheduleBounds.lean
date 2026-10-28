import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicParameterBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalStart

namespace OAI.Algorithms

/-!
# Scheduled coefficient enumeration and parameter size

The actual degree gives `R*p ≤ Q`, so the coefficient enumeration count
is at most the universal block size. Its subpolynomial growth and the raw
parameter bounds are independent of the implementation of the search.
-/

namespace SubexponentialSAT.SubexpCoefficientBounds

open Filter Subexp SubexpPackingParameters

/-- Saturation and the final division cannot increase the interval start
beyond the number of positions. This includes the zero cases. -/
theorem intervalStart_le (r Q R : ℕ) :
    SubexpIntervalStart.value r Q R ≤ Q := by
  unfold SubexpIntervalStart.value
  apply Nat.div_le_of_le_mul
  calc
    (Q - 1) * (r - 1) - R * r ≤ (Q - 1) * (r - 1) := Nat.sub_le _ _
    _ ≤ Q * r := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ ≤ (2 * r) * Q := by nlinarith

/-- The denominator of the scheduled degree contains the prime factor.
This estimate does not require the number denoted by `p` to be prime. -/
theorem degreeR_mul_prime_le (p k δ : ℕ) (hk : 0 < k) (hδ : 0 < δ) :
    SubexpParameters.degreeR p k δ * p ≤ SubexpParameters.sizeQ p := by
  have hfactor : 1 ≤ 8 * δ * k := Nat.mul_pos (Nat.mul_pos (by decide) hδ) hk
  have hden : p ≤ 8 * δ * k * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p hfactor
  change (SubexpParameters.sizeQ p / (8 * δ * k * p)) * p ≤ _
  calc
    (SubexpParameters.sizeQ p / (8 * δ * k * p)) * p ≤
        (SubexpParameters.sizeQ p / (8 * δ * k * p)) * (8 * δ * k * p) :=
      Nat.mul_le_mul_left _ hden
    _ = (8 * δ * k * p) * (SubexpParameters.sizeQ p / (8 * δ * k * p)) := by ring
    _ ≤ SubexpParameters.sizeQ p := Nat.mul_div_le _ _

theorem coefficientPower_le_colorPower (p r Q R : ℕ) (hr : 2 ≤ r) (hRQ : R * p ≤ Q) :
    p^R ≤ r^Q := by
  have hp : p ≤ r^p :=
    (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left hr p)
  calc
    p^R ≤ (r^p)^R := Nat.pow_le_pow_left hp R
    _ = r^(R * p) := by rw [← pow_mul, Nat.mul_comm p R]
    _ ≤ r^Q := Nat.pow_le_pow_right (by omega) hRQ

/-- The actual search enumeration is no larger than the universal block. -/
theorem scheduled_coefficientPower_le_blockSize (k T n : ℕ) (hk : 2 ≤ k)
    (hn : GoodInput n) :
    p n ^ DyadicSchedule.R k T n ≤ DyadicSchedule.N k T n := by
  have hRQ : DyadicSchedule.R k T n * p n ≤ DyadicSchedule.Q n :=
    degreeR_mul_prime_le (p n) k (DyadicSchedule.delta k T n)
      (by omega) (DyadicSchedule.delta_pos k T n)
  have hr : 2 ≤ r n := goodInput_r_ge_two hn
  calc
    p n ^ DyadicSchedule.R k T n ≤ r n ^ DyadicSchedule.Q n :=
      coefficientPower_le_colorPower _ _ _ _ hr hRQ
    _ ≤ r n ^ (DyadicSchedule.Q n * (DyadicSchedule.delta k T n + 1)) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ = DyadicSchedule.N k T n := rfl

theorem eventually_blockSize_le (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, DyadicSchedule.N k T n ≤ n := by
  obtain ⟨C, d, hdelta⟩ := DyadicSchedule.exists_incidence_bound k T
  have hd : ∀ᶠ n : ℕ in atTop,
      DyadicSchedule.delta k T n ≤ C * (s n + 1)^d := by
    filter_upwards [eventually_goodInput] with n hn
    exact hdelta n hn
  simpa only [DyadicSchedule.N, pow_one] using
    SubexpParameters.blockSize_subpolynomial C d 1 (DyadicSchedule.delta k T) hd

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

theorem scheduled_parameterSum_le (k T n B : ℕ) (hn : GoodInput n) :
    B + p n + DyadicSchedule.Q n + DyadicSchedule.R k T n +
        MatrixWordEncoding.width (p n) + 2 ≤ B + 6 * (n + 1)^4 := by
  have hp := DyadicParameterBounds.p_le_n hn
  have hbase : n + 1 ≤ (n + 1)^4 := Nat.le_self_pow (by decide) _
  have hp4 : p n ≤ (n + 1)^4 := hp.trans ((Nat.le_succ _).trans hbase)
  have hQ : DyadicSchedule.Q n ≤ (n + 1)^4 :=
    (DyadicParameterBounds.Q_le_p_pow_four n).trans
      (Nat.pow_le_pow_left (hp.trans (Nat.le_succ _)) 4)
  have hR : DyadicSchedule.R k T n ≤ (n + 1)^4 :=
    (DyadicParameterBounds.R_le_Q k (DyadicSchedule.delta k T) n).trans hQ
  have hw : MatrixWordEncoding.width (p n) ≤ (n + 1)^4 := by
    apply le_trans (b := n + 1) _ hbase
    simp only [MatrixWordEncoding.width, SubexpLiftRing.baseWidth, one_mul]
    exact Nat.add_le_add_right ((Nat.log_le_self 2 (p n)).trans hp) 1
  have hone : 1 ≤ (n + 1)^4 := Nat.one_le_pow _ _ (by omega)
  omega

/-- Substitution uses actual incoming word lengths, with no canonical-word
assumption. All exponents and coefficients are independent of `n` and `L`. -/
theorem scheduled_parameterSum_le_input (k T n B L C0 d0 : ℕ)
    (hn : GoodInput n) (hL : n ≤ L) (hB : B ≤ C0 * (L + 1)^d0) :
    B + p n + DyadicSchedule.Q n + DyadicSchedule.R k T n +
        MatrixWordEncoding.width (p n) + 2 ≤
      (C0 + 6) * (L + 1)^(d0 + 4) := by
  calc
    B + p n + DyadicSchedule.Q n + DyadicSchedule.R k T n +
        MatrixWordEncoding.width (p n) + 2 ≤ B + 6 * (n + 1)^4 :=
      scheduled_parameterSum_le k T n B hn
    _ ≤ C0 * (L + 1)^d0 + 6 * (L + 1)^4 := by gcongr
    _ ≤ C0 * (L + 1)^(d0 + 4) + 6 * (L + 1)^(d0 + 4) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
    _ = (C0 + 6) * (L + 1)^(d0 + 4) := by ring

end SubexponentialSAT.SubexpCoefficientBounds

end OAI.Algorithms
