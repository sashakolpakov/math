import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComputation
import OAI.Algorithms.SubexponentialSAT.SubexpExponentArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpParameters

namespace OAI.Algorithms

/-!
# Exhaustive searches over subpolynomial auxiliary data

The size function below describes only the auxiliary universal-block data.
It must not include the global coordinate count `D`. A growth premise is
explicit; this file does not assert that arbitrary search data have that growth.
-/

namespace SubexponentialSAT.SubexpFiniteSearch

open Filter
open scoped Topology

noncomputable section

/-- The literal real-exponent formulation of `X(n) = n^{o(1)}`. -/
def Subpolynomial (X : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, X n ≤ ((n : ℝ) + 16) ^ ε

/-- A convenient equivalent-strength input for the natural block-size estimates:
every fixed positive integer power is eventually at most `n`. -/
def SubpolynomialPowers (X : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ᶠ n : ℕ in atTop, (X n) ^ t ≤ (n : ℝ)

theorem subpolynomial_powers {X : ℕ → ℝ} (hX0 : ∀ n, 0 ≤ X n)
    (hX : Subpolynomial X) : SubpolynomialPowers X := by
  intro t ht
  let ε : ℝ := 1 / (2 * (t : ℝ))
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [hX ε hε, eventually_ge_atTop (5 : ℕ)] with n hn hn5
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn5r : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hb : 0 ≤ (n : ℝ) + 16 := by positivity
  have hpow := pow_le_pow_left₀ (hX0 n) hn (2 * t)
  have hexp : ε * ((2 * t : ℕ) : ℝ) = 1 := by
    dsimp [ε]
    push_cast
    field_simp
  have heq : (((n : ℝ) + 16) ^ ε) ^ (2 * t) = (n : ℝ) + 16 := by
    rw [← Real.rpow_mul_natCast hb, hexp, Real.rpow_one]
  rw [heq] at hpow
  have hsq : ((X n) ^ t) ^ 2 ≤ (n : ℝ) + 16 := by
    simpa only [← pow_mul, Nat.mul_comm t 2] using hpow
  have hy0 : 0 ≤ (X n) ^ t := pow_nonneg (hX0 n) _
  nlinarith

/-- The squared iterated logarithm is eventually at most `n`. This uses the
already checked logarithm-growth lemmas and the actual target scale. -/
theorem eventually_logLog_sq_le :
    ∀ᶠ n : ℕ in atTop, (SubexpComputation.logLog n) ^ 2 ≤ (n : ℝ) := by
  have hs := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    SubexpExponentArithmetic.eventually_logb_sq_le
  have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    SubexpExponentArithmetic.eventually_shiftedLogLog_le_logb
  filter_upwards [hs, hi] with n hsq hiter
  have hiter' : SubexpComputation.logLog n ≤
      Real.logb 2 ((n : ℝ) + 16) := hiter
  exact (pow_le_pow_left₀ (SubexpComputation.logLog_pos n).le hiter' 2).trans hsq

/-- Any fixed polynomial in a nonnegative subpolynomial size has square at most
`n` eventually. The constant and polynomial degree precede the input size. -/
theorem eventually_searchExponent_sq_le {X : ℕ → ℝ}
    (hX0 : ∀ n, 0 ≤ X n) (hX : SubpolynomialPowers X)
    (C : ℝ) (hC : 0 ≤ C) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, (C * (X n + 1) ^ q) ^ 2 ≤ (n : ℝ) := by
  let B : ℝ := C * 2 ^ q
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hlarge2 : ∀ᶠ n : ℕ in atTop, B ^ 2 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (B ^ 2))
  have hlarge4 : ∀ᶠ n : ℕ in atTop, B ^ 4 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (B ^ 4))
  filter_upwards [hX (4 * (q + 1)) (by omega), hlarge2, hlarge4] with n hn hB2 hB4
  have hx0 : 0 ≤ X n := hX0 n
  have hT0 : 0 ≤ C * (X n + 1) ^ q := by positivity
  by_cases hx : X n ≤ 1
  · have hT : C * (X n + 1) ^ q ≤ B := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact pow_le_pow_left₀ (by positivity) (by linarith) q
    exact (pow_le_pow_left₀ hT0 hT 2).trans hB2
  · have hx1 : 1 ≤ X n := by linarith
    have hfour : ((X n) ^ q) ^ 4 ≤ (n : ℝ) := by
      calc
        ((X n) ^ q) ^ 4 = (X n) ^ (q * 4) := (pow_mul _ _ _).symm
        _ ≤ (X n) ^ (4 * (q + 1)) := pow_le_pow_right₀ hx1 (by omega)
        _ ≤ (n : ℝ) := hn
    have hT : C * (X n + 1) ^ q ≤ B * (X n) ^ q := by
      calc
        C * (X n + 1) ^ q ≤ C * (2 * X n) ^ q :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) q) hC
        _ = B * (X n) ^ q := by rw [mul_pow]; dsimp [B]; ring
    have hTsq := pow_le_pow_left₀ hT0 hT 2
    have hprod : B ^ 2 * ((X n) ^ q) ^ 2 ≤ (n : ℝ) := by
      nlinarith [sq_nonneg (B ^ 2 - ((X n) ^ q) ^ 2)]
    calc
      (C * (X n + 1) ^ q) ^ 2 ≤ (B * (X n) ^ q) ^ 2 := hTsq
      _ = B ^ 2 * ((X n) ^ q) ^ 2 := mul_pow _ _ _
      _ ≤ (n : ℝ) := hprod

/-- Exhaustive-search exponents over subpolynomial auxiliary data fit below
the target `n / log₂ log₂(n+16)` with constant exactly one eventually. -/
theorem eventually_searchExponent_le_scale {X : ℕ → ℝ}
    (hX0 : ∀ n, 0 ≤ X n) (hX : SubpolynomialPowers X)
    (C : ℝ) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (X n + 1) ^ q ≤ SubexpComputation.scale n := by
  by_cases hC : 0 ≤ C
  · filter_upwards [eventually_searchExponent_sq_le hX0 hX C hC q,
      eventually_logLog_sq_le] with n hpoly hlog
    apply (le_div_iff₀ (SubexpComputation.logLog_pos n)).2
    nlinarith [sq_nonneg (C * (X n + 1) ^ q - SubexpComputation.logLog n)]
  · exact Filter.Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (by linarith [hX0 n]) q)).trans
        (SubexpComputation.scale_nonneg n)

/-- The requested exhaustive finite-search bound, with `A = 1`. -/
theorem eventually_exp2_search_le {X : ℕ → ℝ}
    (hX0 : ∀ n, 0 ≤ X n) (hX : Subpolynomial X) (C : ℝ) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (C * (X n + 1) ^ q) ≤ (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_searchExponent_le_scale hX0 (subpolynomial_powers hX0 hX) C q]
    with n hn
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

/-- Direct interface for the integer-power growth estimates established for
the concrete universal-block sizes. -/
theorem eventually_exp2_search_le_of_nat_powers (X : ℕ → ℕ)
    (hX : ∀ t : ℕ, 0 < t → ∀ᶠ n : ℕ in atTop, X n ^ t ≤ n)
    (C : ℝ) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (C * ((X n : ℝ) + 1) ^ q) ≤ (2 : ℝ) ^ SubexpComputation.scale n := by
  have hreal : SubpolynomialPowers (fun n => (X n : ℝ)) := by
    intro t ht
    filter_upwards [hX t ht] with n hn
    exact_mod_cast hn
  filter_upwards [eventually_searchExponent_le_scale
    (fun n => Nat.cast_nonneg (X n)) hreal C q] with n hn
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

/-- Concrete application to the source's universal block size. Its growth is
discharged by the parameter theorem; the remaining incidence hypothesis is
the stated fixed-polynomial bound in the integer logarithmic parameter. -/
theorem eventually_block_search_le (A d : ℕ) (δ : ℕ → ℕ)
    (hδ : ∀ᶠ n : ℕ in atTop,
      δ n ≤ A * (SubexpPackingParameters.s n + 1) ^ d)
    (C : ℝ) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (C *
        ((SubexpParameters.blockSize (SubexpPackingParameters.s n)
          (SubexpPackingParameters.p n) (δ n) : ℝ) + 1) ^ q) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  exact eventually_exp2_search_le_of_nat_powers
    (fun n => SubexpParameters.blockSize (SubexpPackingParameters.s n)
      (SubexpPackingParameters.p n) (δ n))
    (fun t _ => SubexpParameters.blockSize_subpolynomial A d t δ hδ) C q

end

end SubexponentialSAT.SubexpFiniteSearch

end OAI.Algorithms
