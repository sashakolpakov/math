import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComputation
import OAI.Algorithms.SubexponentialSAT.SmallInputs
import OAI.Algorithms.SubexponentialSAT.FixedParameters
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters
import OAI.Algorithms.SubexponentialSAT.SubexpParameters

namespace OAI.Algorithms

/-!
# Finite fallback for size-dependent subexponential parameters

The relevant cutoff is a fixed bound on the *input size*, obtained only after
proving eventual success of every layout check. The growing block threshold
must not itself be treated as a constant.

Numerical finite-maximum bounds below are separate from machine execution.
The final section reuses the already proved finite-language primitive machine;
this supplies an actual bounded-input solver, not a cost assigned to a function.
-/

namespace SubexponentialSAT.SubexpSmallInputs

open Filter
open SubexpComputation

noncomputable section

/-- Exponential factor in the precise target, using its shifted double logarithm. -/
def factor (A : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (A * scale n)

theorem factor_pos (A : ℝ) (n : ℕ) : 0 < factor A n :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem one_le_factor {A : ℝ} (hA : 0 ≤ A) (n : ℕ) : 1 ≤ factor A n := by
  apply Real.one_le_rpow (by norm_num)
  exact mul_nonneg hA (scale_nonneg n)

@[simp] theorem factor_zero (A : ℝ) : factor A 0 = 1 := by
  simp [factor]

/-- No zero-denominator convention is needed at any input size. -/
theorem scale_eq_zero_iff (n : ℕ) : scale n = 0 ↔ n = 0 := by
  rw [scale, div_eq_zero_iff]
  simp only [ne_of_gt (logLog_pos n), or_false, Nat.cast_eq_zero]

/-- An eventual parameter estimate supplies one fixed input-size cutoff. -/
theorem fallback_bounded_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) : ∃ B : ℕ, ∀ n, ¬ P n → n < B := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp hP
  refine ⟨B, fun n hn => ?_⟩
  by_contra h
  exact hn (hB n (Nat.le_of_not_gt h))

/-- The set of exceptional sizes, rather than a growing layout threshold, is finite. -/
theorem fallback_finite_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) : {n | ¬ P n}.Finite := by
  obtain ⟨B, hB⟩ := fallback_bounded_of_eventually hP
  apply (Finset.range B).finite_toSet.subset
  intro n hn
  exact Finset.mem_range.mpr (hB n hn)

/-- The source's integer tail check already forces the required radius bound
when the point count and incidence count are nondegenerate. -/
theorem radius_ge_32_of_tail {Q Delta s R : ℕ}
    (hQ : 2 ≤ Q) (hDelta : 1 ≤ Delta) (hs : 32 ≤ s)
    (htail : 16 * Q * Delta * s ≤ R ^ 2) : 32 ≤ R := by
  have hprod : 2 ≤ Q * Delta := by
    have := Nat.mul_le_mul hQ hDelta
    simpa using this
  have hscaled : 64 ≤ Q * Delta * s := by
    have := Nat.mul_le_mul hprod hs
    simpa using this
  have hlarge : 1024 ≤ 16 * Q * Delta * s := by nlinarith
  nlinarith

/-- Explicit threshold for the source's first logarithmic-domain check. -/
private theorem logCutoff_exists : ∃ n : ℕ, n = 2 ^ (2 ^ 32) :=
  ⟨2 ^ (2 ^ 32), rfl⟩

noncomputable def logCutoff : ℕ := Classical.choose logCutoff_exists

theorem logCutoff_eq : logCutoff = 2 ^ (2 ^ 32) :=
  Classical.choose_spec logCutoff_exists

private theorem two_le_tower (a : ℕ) : 2 ≤ (2 : ℕ) ^ (2 ^ a) := by
  have ha : 1 ≤ (2 : ℕ) ^ a := one_le_pow₀ (by decide)
  simpa only [pow_one] using
    (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) ha)

/-- The source's domain test is exact even for n=0 and n=1. -/
theorem goodInput_iff_cutoff (n : ℕ) :
    SubexpPackingParameters.GoodInput n ↔ logCutoff ≤ n := by
  rw [logCutoff_eq]
  constructor
  · intro hn
    exact (SubexpPackingParameters.goodInput_iff
      (SubexpPackingParameters.goodInput_two_le hn)).mp hn
  · intro hn
    have hn2 : 2 ≤ n := (two_le_tower 32).trans hn
    exact (SubexpPackingParameters.goodInput_iff hn2).mpr hn

theorem small_log_iff (n : ℕ) :
    ¬ SubexpPackingParameters.GoodInput n ↔ n < logCutoff := by
  rw [goodInput_iff_cutoff, not_le]

theorem eventually_goodInput :
    ∀ᶠ n in atTop, SubexpPackingParameters.GoodInput n :=
  eventually_atTop.mpr ⟨logCutoff, fun n hn => (goodInput_iff_cutoff n).mpr hn⟩

@[simp] theorem not_goodInput_zero : ¬ SubexpPackingParameters.GoodInput 0 := by
  simp [SubexpPackingParameters.GoodInput]

@[simp] theorem not_goodInput_one : ¬ SubexpPackingParameters.GoodInput 1 := by
  simp [SubexpPackingParameters.GoodInput]

@[simp] theorem packing_ell_zero : SubexpPackingParameters.ell 0 = 0 := by
  simp [SubexpPackingParameters.ell, SubexpPackingParameters.u]

@[simp] theorem packing_D_zero : SubexpPackingParameters.D 0 = 0 := by
  simp [SubexpPackingParameters.D, ChunkPartition.count]

@[simp] theorem logLog_zero : logLog 0 = 2 := by
  have h16 : Real.logb 2 16 = 4 := by
    have h := Real.logb_pow 2 2 4
    norm_num at h ⊢
    exact h
  have h4 : Real.logb 2 4 = 2 := by
    have h := Real.logb_pow 2 2 2
    norm_num at h ⊢
    exact h
  simp only [logLog, Nat.cast_zero, zero_add, h16, h4]

/-- The four natural-valued schedules inspected by the source's layout guard.
Their definitions and growth estimates are supplied by parameter construction. -/
structure CheckData where
  points : ℕ → ℕ
  incidence : ℕ → ℕ
  radius : ℕ → ℕ
  blockThreshold : ℕ → ℕ

/-- Exact sufficient tail inequality checked by the uniform algorithm. -/
def TailPass (c : CheckData) (n : ℕ) : Prop :=
  16 * c.points n * c.incidence n * SubexpPackingParameters.s n ≤ (c.radius n) ^ 2

/-- Exact dimension check against the growing, input-dependent block threshold. -/
def BlockPass (c : CheckData) (n : ℕ) : Prop :=
  c.blockThreshold n ≤ SubexpPackingParameters.D n

/-- The source's three-part guard. Its arithmetic predicates are decidable. -/
def Ready (c : CheckData) (n : ℕ) : Prop :=
  SubexpPackingParameters.GoodInput n ∧ TailPass c n ∧ BlockPass c n

instance (c : CheckData) (n : ℕ) : Decidable (TailPass c n) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (c : CheckData) (n : ℕ) : Decidable (BlockPass c n) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (c : CheckData) (n : ℕ) : Decidable (Ready c n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[simp] theorem not_ready_zero (c : CheckData) : ¬ Ready c 0 := by
  simp [Ready]

@[simp] theorem not_ready_one (c : CheckData) : ¬ Ready c 1 := by
  simp [Ready]

/-- Every division and nonempty-dimensional counting operation is reached only
on a positive-capacity, positive-dimension input. -/
theorem ready_positive {c : CheckData} {n : ℕ} (hn : Ready c n) :
    0 < SubexpPackingParameters.ell n ∧ 0 < SubexpPackingParameters.D n :=
  ⟨SubexpPackingParameters.ell_pos hn.1, SubexpPackingParameters.D_pos hn.1⟩

/-- No additional R>=32 test is needed when the point and incidence counts have
been proved nondegenerate by the parameter construction. -/
theorem ready_radius {c : CheckData} {n : ℕ} (hn : Ready c n)
    (hQ : 2 ≤ c.points n) (hDelta : 1 ≤ c.incidence n) : 32 ≤ c.radius n :=
  radius_ge_32_of_tail hQ hDelta hn.1 hn.2.1

/-- Only the two substantive eventual growth estimates remain as hypotheses;
the logarithmic domain condition is proved outright. -/
theorem eventually_ready (c : CheckData)
    (htail : ∀ᶠ n in atTop, TailPass c n)
    (hblock : ∀ᶠ n in atTop, BlockPass c n) : ∀ᶠ n in atTop, Ready c n :=
  eventually_goodInput.and (htail.and hblock)

/-- A single input-size cutoff suffices even though every component of c may grow. -/
theorem exists_fallback_cutoff (c : CheckData)
    (htail : ∀ᶠ n in atTop, TailPass c n)
    (hblock : ∀ᶠ n in atTop, BlockPass c n) :
    ∃ B : ℕ, ∀ n, ¬ Ready c n → n < B :=
  fallback_bounded_of_eventually (eventually_ready c htail hblock)

/-- The cutoff may depend on the fixed width, but is selected before n varies. -/
theorem fixed_width_fallback_cutoff (c : ℕ → CheckData)
    (htail : ∀ k, ∀ᶠ n in atTop, TailPass (c k) n)
    (hblock : ∀ k, ∀ᶠ n in atTop, BlockPass (c k) n) :
    ∀ k, ∃ B : ℕ, ∀ n, ¬ Ready (c k) n → n < B :=
  fun k => exists_fallback_cutoff (c k) (htail k) (hblock k)

/-- Instantiate the exact checks using the selected quartic prime extension
and the source's integral expression for its block threshold. -/
def actualChecks (k : ℕ) (Delta : ℕ → ℕ) : CheckData where
  points n := SubexpParameters.sizeQ (SubexpPackingParameters.p n)
  incidence := Delta
  radius n := SubexpParameters.degreeR (SubexpPackingParameters.p n) k (Delta n)
  blockThreshold n := (SubexpPackingParameters.s n) ^ 2 *
    (SubexpParameters.blockSize (SubexpPackingParameters.s n)
      (SubexpPackingParameters.p n) (Delta n)) ^ 3 * (1 + Delta n * k)

theorem actualChecks_points_ge_two (k : ℕ) (Delta : ℕ → ℕ) (n : ℕ) :
    2 ≤ (actualChecks k Delta).points n := by
  change 2 ≤ (SubexpPackingParameters.p n) ^ 4 - 1
  have hp := SubexpPackingParameters.p_gt_two n
  have hpow := Nat.pow_le_pow_left (show 3 ≤ SubexpPackingParameters.p n by omega) 4
  norm_num at hpow
  omega

/-- A uniform polynomial estimate for the sufficient prime-size condition. -/
theorem prime_requirement_le_polynomial {s Delta C d : ℕ} (k : ℕ)
    (hDelta : Delta ≤ C * (s + 1) ^ d) :
    8192 * s * Delta ^ 3 * k ^ 2 ≤
      (8192 * C ^ 3 * k ^ 2) * (s + 1) ^ (d * 3 + 1) := by
  calc
    8192 * s * Delta ^ 3 * k ^ 2 ≤
        8192 * (s + 1) * (C * (s + 1) ^ d) ^ 3 * k ^ 2 := by
      gcongr
      omega
    _ = (8192 * C ^ 3 * k ^ 2) * (s + 1) ^ (d * 3 + 1) := by
      rw [mul_pow, ← pow_mul]
      rw [show (s + 1) ^ (d * 3 + 1) = (s + 1) ^ (d * 3) * (s + 1) by rw [pow_succ]]
      ring

/-- The actual prime chosen from its dyadic interval eventually dominates the
prime requirement, for every fixed polynomial incidence bound. -/
theorem eventually_actual_prime_requirement (k C d : ℕ) (Delta : ℕ → ℕ)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∀ᶠ n in atTop,
      8192 * SubexpPackingParameters.s n * (Delta n) ^ 3 * k ^ 2 ≤
        (SubexpPackingParameters.p n) ^ 2 := by
  have hdom := SubexpPackingParameters.tendsto_s_atTop.eventually
    (SubexpParameters.polynomial_le_two_pow_div_sixteen_eventually
      (8192 * C ^ 3 * k ^ 2) (d * 3 + 1))
  filter_upwards [eventually_goodInput, hdom] with n hgood hpoly
  have hprime := SubexpPackingParameters.p_lower hgood
  have hp := SubexpPackingParameters.p_gt_two n
  calc
    8192 * SubexpPackingParameters.s n * (Delta n) ^ 3 * k ^ 2 ≤
        (8192 * C ^ 3 * k ^ 2) * (SubexpPackingParameters.s n + 1) ^ (d * 3 + 1) :=
      prime_requirement_le_polynomial k (hDelta n hgood)
    _ ≤ 2 ^ (SubexpPackingParameters.s n / 16) := hpoly
    _ ≤ SubexpPackingParameters.p n := by
      simpa only [SubexpPackingParameters.u] using hprime.le
    _ ≤ (SubexpPackingParameters.p n) ^ 2 := by nlinarith

/-- Eventual validity of the actual tail guard is proved, not assumed, once the
incidence construction supplies its claimed fixed polynomial bound. -/
theorem eventually_actual_tail (k C d : ℕ) (hk : 0 < k) (Delta : ℕ → ℕ)
    (hpositive : ∀ n, SubexpPackingParameters.GoodInput n → 0 < Delta n)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∀ᶠ n in atTop, TailPass (actualChecks k Delta) n := by
  filter_upwards [eventually_goodInput,
    eventually_actual_prime_requirement k C d Delta hDelta] with n hgood hprime
  exact (SubexpParameters.quartic_feasible hgood
    (by have hp := SubexpPackingParameters.p_gt_two n; omega)
    hk (hpositive n hgood) hprime).2.1

/-- After the independent block-fit estimate, all checks succeed eventually
for the actual selected prime and every such incidence schedule. -/
theorem eventually_actual_ready (k C d : ℕ) (hk : 0 < k) (Delta : ℕ → ℕ)
    (hpositive : ∀ n, SubexpPackingParameters.GoodInput n → 0 < Delta n)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d)
    (hblock : ∀ᶠ n in atTop, BlockPass (actualChecks k Delta) n) :
    ∀ᶠ n in atTop, Ready (actualChecks k Delta) n :=
  eventually_ready _ (eventually_actual_tail k C d hk Delta hpositive hDelta) hblock

/-- All arithmetic checks hold eventually for the actual computed prime and
packing schedule. The only growth input is the independently required fixed
polynomial incidence bound, with positive incidence on the used domain. -/
theorem eventually_actual_ready_of_polynomial_bound (k C d : ℕ) (hk : 0 < k)
    (Delta : ℕ → ℕ)
    (hpositive : ∀ n, SubexpPackingParameters.GoodInput n → 0 < Delta n)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∀ᶠ n in atTop, Ready (actualChecks k Delta) n := by
  have hpoly : ∀ᶠ n in atTop,
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d :=
    eventually_goodInput.mono (fun n hn => hDelta n hn)
  have hblock : ∀ᶠ n in atTop, BlockPass (actualChecks k Delta) n := by
    simpa only [BlockPass, actualChecks, SubexpParameters.blockThreshold] using
      SubexpParameters.blockThreshold_eventually_le_D C d k Delta hpoly
  exact eventually_actual_ready k C d hk Delta hpositive hDelta hblock

/-- The fallback threshold is fixed once k and its incidence-bound constants
are fixed. It does not grow with the input size. -/
theorem actual_fallback_cutoff (k C d : ℕ) (hk : 0 < k) (Delta : ℕ → ℕ)
    (hpositive : ∀ n, SubexpPackingParameters.GoodInput n → 0 < Delta n)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∃ B : ℕ, ∀ n, ¬ Ready (actualChecks k Delta) n → n < B :=
  fallback_bounded_of_eventually
    (eventually_actual_ready_of_polynomial_bound k C d hk Delta hpositive hDelta)

/-- For a fixed exceptional-size bound, ordinary exhaustive search has a fixed
multiplicative loss relative to every target with nonnegative exponent constant. -/
theorem bruteForce_le_factor {A : ℝ} (hA : 0 ≤ A) {B n : ℕ} (hn : n ≤ B) :
    ((2 ^ n : ℕ) : ℝ) ≤ (2 : ℝ) ^ B * factor A n := by
  have hpow : ((2 ^ n : ℕ) : ℝ) ≤ (2 : ℝ) ^ B := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hn
  exact hpow.trans (le_mul_of_one_le_right (by positivity) (one_le_factor hA n))

/-- Input-length polynomial factors remain outside the finite maximum. -/
theorem polynomial_bruteForce_le_factor {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    {B n : ℕ} (hn : n ≤ B) (L d : ℕ) :
    a * SmallInputs.inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
      runtimeBound (a * (2 : ℝ) ^ B) A d L n := by
  have h := mul_le_mul_of_nonneg_left (bruteForce_le_factor hA hn)
    (mul_nonneg ha (SmallInputs.inputPolynomial_nonneg L d))
  simpa only [runtimeBound, factor, SmallInputs.inputPolynomial, mul_assoc,
    mul_left_comm, mul_comm] using h

/-- Exact finite maximum of normalized coefficients, including size zero. -/
def finiteCoefficient (B : ℕ) (A : ℝ) (c : ℕ → ℝ) : ℝ :=
  max 1 ((Finset.range (B + 1)).sup' (by simp) fun n => c n / factor A n)

theorem one_le_finiteCoefficient (B : ℕ) (A : ℝ) (c : ℕ → ℝ) :
    1 ≤ finiteCoefficient B A c := le_max_left _ _

theorem finiteCoefficient_pos (B : ℕ) (A : ℝ) (c : ℕ → ℝ) :
    0 < finiteCoefficient B A c :=
  lt_of_lt_of_le (by norm_num) (one_le_finiteCoefficient B A c)

@[simp] theorem finiteCoefficient_zero (A : ℝ) (c : ℕ → ℝ) :
    finiteCoefficient 0 A c = max 1 (c 0) := by
  simp [finiteCoefficient]

theorem coefficient_le_finiteCoefficient {B n : ℕ} (A : ℝ) (c : ℕ → ℝ)
    (hn : n ≤ B) : c n ≤ finiteCoefficient B A c * factor A n := by
  apply (div_le_iff₀ (factor_pos A n)).mp
  have hmem : n ∈ Finset.range (B + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  exact (Finset.le_sup' (fun m => c m / factor A m) hmem).trans (le_max_right _ _)

/-- Per-size coefficients and degrees are made uniform over the finite fallback
range; explicit input length remains arbitrary. No algorithmic bound is assumed. -/
theorem finite_polynomial_family_le_bound {B n L : ℕ} (A : ℝ)
    (c : ℕ → ℝ) (degree : ℕ → ℕ) (hn : n ≤ B) :
    c n * SmallInputs.inputPolynomial L (degree n) ≤
      runtimeBound (finiteCoefficient B A c) A (SmallInputs.finiteDegree B degree) L n := by
  calc
    c n * SmallInputs.inputPolynomial L (degree n) ≤
        (finiteCoefficient B A c * factor A n) *
          SmallInputs.inputPolynomial L (degree n) :=
      mul_le_mul_of_nonneg_right (coefficient_le_finiteCoefficient A c hn)
        (SmallInputs.inputPolynomial_nonneg L (degree n))
    _ ≤ (finiteCoefficient B A c * factor A n) *
        SmallInputs.inputPolynomial L (SmallInputs.finiteDegree B degree) :=
      mul_le_mul_of_nonneg_left
        (SmallInputs.inputPolynomial_mono_degree L (SmallInputs.degree_le_finiteDegree degree hn))
        (mul_nonneg (finiteCoefficient_pos B A c).le (factor_pos A n).le)
    _ = runtimeBound (finiteCoefficient B A c) A
        (SmallInputs.finiteDegree B degree) L n := by
      simp only [runtimeBound, factor, SmallInputs.inputPolynomial]
      ring

/-- Finite fallback absorption keeps the chosen exponent constant exactly fixed. -/
theorem exists_uniform_fallback_bound {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) (A : ℝ) (c : ℕ → ℝ) (degree : ℕ → ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ n, ¬ P n → ∀ L,
      c n * SmallInputs.inputPolynomial L (degree n) ≤ runtimeBound C A d L n := by
  obtain ⟨B, hB⟩ := fallback_bounded_of_eventually hP
  refine ⟨finiteCoefficient B A c, SmallInputs.finiteDegree B degree,
    finiteCoefficient_pos B A c, ?_⟩
  intro n hn L
  exact finite_polynomial_family_le_bound A c degree (hB n hn).le

/-- Additive parsing costs and exhaustive search can be absorbed together. -/
theorem parsing_plus_bruteForce_le_bound {A parsing search : ℝ}
    (hA : 0 ≤ A) (hp : 0 ≤ parsing) (hs : 0 ≤ search)
    {B n : ℕ} (hn : n ≤ B) (L d : ℕ) :
    parsing * SmallInputs.inputPolynomial L d +
        search * SmallInputs.inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
      runtimeBound (parsing + search * (2 : ℝ) ^ B) A d L n := by
  have hparse : parsing * SmallInputs.inputPolynomial L d ≤
      parsing * SmallInputs.inputPolynomial L d * factor A n :=
    le_mul_of_one_le_right (mul_nonneg hp (SmallInputs.inputPolynomial_nonneg L d))
      (one_le_factor hA n)
  have hsearch := polynomial_bruteForce_le_factor hA hs hn L d
  calc
    parsing * SmallInputs.inputPolynomial L d +
        search * SmallInputs.inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
      parsing * SmallInputs.inputPolynomial L d * factor A n +
        runtimeBound (search * (2 : ℝ) ^ B) A d L n := add_le_add hparse hsearch
    _ = runtimeBound (parsing + search * (2 : ℝ) ^ B) A d L n := by
      simp only [runtimeBound, factor, SmallInputs.inputPolynomial]
      ring

/-- Increasing a nonnegative target coefficient and polynomial degree enlarges
the target bound, while keeping its subexponential exponent constant. -/
theorem bound_mono_coefficient_degree {C C' A : ℝ} (hC' : 0 ≤ C')
    (hC : C ≤ C') {d d' : ℕ} (hd : d ≤ d') (L n : ℕ) :
    runtimeBound C A d L n ≤ runtimeBound C' A d' L n := by
  apply mul_le_mul_of_nonneg_right _ (factor_pos A n).le
  calc
    C * ((L : ℝ) + 1) ^ d ≤ C' * ((L : ℝ) + 1) ^ d :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ C' * ((L : ℝ) + 1) ^ d' :=
      mul_le_mul_of_nonneg_left (SmallInputs.inputPolynomial_mono_degree L hd) hC'

/-- Numerical gluing of an eventual valid-branch bound and finite exceptional
polynomial bounds. The result really uses one coefficient and one degree for
all input sizes, with the same chosen exponent constant `A`.

`T` is merely a real-valued quantity here. A caller must separately establish
that `T` bounds actual primitive execution steps. -/
theorem global_bound_of_finite_and_valid_bounds
    {P : ℕ → Prop} (hP : ∀ᶠ n in atTop, P n)
    (T : ℕ → ℕ → ℝ) (A C : ℝ) (d : ℕ)
    (c : ℕ → ℝ) (degree : ℕ → ℕ)
    (hvalid : ∀ n, P n → ∀ L, T n L ≤ runtimeBound C A d L n)
    (hsmall : ∀ n, ¬ P n → ∀ L,
      T n L ≤ c n * SmallInputs.inputPolynomial L (degree n)) :
    ∃ (C' : ℝ) (d' : ℕ), 0 < C' ∧
      ∀ n L, T n L ≤ runtimeBound C' A d' L n := by
  classical
  obtain ⟨B, hB⟩ := fallback_bounded_of_eventually hP
  let Cf := finiteCoefficient B A c
  let df := SmallInputs.finiteDegree B degree
  have hCf : 0 < Cf := finiteCoefficient_pos B A c
  have htarget : 0 < max C Cf := lt_of_lt_of_le hCf (le_max_right _ _)
  refine ⟨max C Cf, max d df, htarget, ?_⟩
  intro n L
  by_cases hn : P n
  · exact (hvalid n hn L).trans
      (bound_mono_coefficient_degree htarget.le (le_max_left _ _)
        (le_max_left _ _) L n)
  · have hf : T n L ≤ runtimeBound Cf A df L n :=
      (hsmall n hn L).trans
        (finite_polynomial_family_le_bound A c degree (hB n hn).le)
    exact hf.trans (bound_mono_coefficient_degree htarget.le (le_max_right _ _)
      (le_max_right _ _) L n)

/-- An actual primitive machine for every fixed bounded-variable range. Its
finite accepted-language table was built with the exhaustive Boolean evaluator
in `FixedParameters`, separately from all numerical cost absorption above. -/
theorem smallSolver_subexp_bound (B n : ℕ) (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ (answer : Bool) (time : ℕ),
      (FixedParameters.smallSolver B).OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound 1 A 1 (Encoding.formulaBitLength F) n := by
  obtain ⟨answer, hrun, hcorrect⟩ := FixedParameters.smallSolver_correct B n F hn
  refine ⟨answer, Encoding.formulaBitLength F + 1, hrun, hcorrect, ?_⟩
  simp only [runtimeBound, one_mul, pow_one, Nat.cast_add, Nat.cast_one]
  exact le_mul_of_one_le_right (by positivity) (one_le_factor hA n)

/-- The source's first fallback (small or zero logarithms) has an unconditional
fixed primitive solver, before any asymptotic layout estimate is invoked. -/
theorem small_log_solver_subexp_bound (n : ℕ) (F : SAT.CNF (Fin n))
    (hn : ¬ SubexpPackingParameters.GoodInput n) {A : ℝ} (hA : 0 ≤ A) :
    ∃ (answer : Bool) (time : ℕ),
      (FixedParameters.smallSolver logCutoff).OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound 1 A 1 (Encoding.formulaBitLength F) n :=
  smallSolver_subexp_bound logCutoff n F ((small_log_iff n).mp hn).le hA

/-- Once the parameter checks are proved eventually, one fixed primitive
machine handles all remaining sizes. This does not compile the guard or the
large-input branch into a complete solver. -/
theorem exists_machine_for_fallback {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℕ, ∀ (n : ℕ) (F : SAT.CNF (Fin n)), ¬ P n →
      ∃ (answer : Bool) (time : ℕ),
        (FixedParameters.smallSolver B).OutputsInTime (Encoding.encodeCNF F) answer time ∧
        (answer = true ↔ SAT.Satisfiable F) ∧
        (time : ℝ) ≤ runtimeBound 1 A 1 (Encoding.formulaBitLength F) n := by
  obtain ⟨B, hB⟩ := fallback_bounded_of_eventually hP
  exact ⟨B, fun n F hn => smallSolver_subexp_bound B n F (hB n hn).le hA⟩

/-- A proved primitive small-input branch for the actual parameter schedule,
with a fixed finite machine chosen before the formula or its size. This is
separate from compiling the complete guarded large/small algorithm. -/
theorem actual_fallback_machine (k C d : ℕ) (hk : 0 < k) (Delta : ℕ → ℕ)
    (hpositive : ∀ n, SubexpPackingParameters.GoodInput n → 0 < Delta n)
    (hDelta : ∀ n, SubexpPackingParameters.GoodInput n →
      Delta n ≤ C * (SubexpPackingParameters.s n + 1) ^ d)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℕ, ∀ (n : ℕ) (F : SAT.CNF (Fin n)),
      ¬ Ready (actualChecks k Delta) n →
      ∃ (answer : Bool) (time : ℕ),
        (FixedParameters.smallSolver B).OutputsInTime (Encoding.encodeCNF F) answer time ∧
        (answer = true ↔ SAT.Satisfiable F) ∧
        (time : ℝ) ≤ runtimeBound 1 A 1 (Encoding.formulaBitLength F) n :=
  exists_machine_for_fallback
    (eventually_actual_ready_of_polynomial_bound k C d hk Delta hpositive hDelta) hA

end

end SubexponentialSAT.SubexpSmallInputs

end OAI.Algorithms
