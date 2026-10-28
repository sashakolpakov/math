import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ChunkPartition
import OAI.Algorithms.SubexponentialSAT.ParameterOrder

namespace OAI.Algorithms

/-!
# Computable packing parameters for the subexponential argument

All schedules are total functions of the input size. The main construction is
used only on `GoodInput`; smaller inputs are handled by exhaustive search.
The logarithms are computed by natural-number binary logarithms, with exact
dyadic characterizations recording their rounding behavior.
-/

namespace SubexponentialSAT.SubexpPackingParameters

open scoped BigOperators

/-- The integer part of the iterated binary logarithm on the intended domain. -/
def s (n : ℕ) : ℕ := Nat.log2 (Nat.log2 n)

/-- The slowly growing number of bits per field coordinate. -/
def u (n : ℕ) : ℕ := s n / 16

def ell (n : ℕ) : ℕ := u n

/-- Number of actual Boolean chunks, with the ceiling computed in integers. -/
def D (n : ℕ) : ℕ := ChunkPartition.count n (ell n)

/-- Number of interpolation colors. -/
def r (n : ℕ) : ℕ := s n

/-- Domain on which the growing-parameter branch is used. -/
def GoodInput (n : ℕ) : Prop := 32 ≤ s n

instance (n : ℕ) : Decidable (GoodInput n) := inferInstanceAs (Decidable (32 ≤ s n))

@[simp] theorem s_zero : s 0 = 0 := by simp [s]
@[simp] theorem s_one : s 1 = 0 := by simp [s, Nat.log2_eq_log_two]

theorem log2_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Nat.log2 n := by
  have h : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).mpr (by simpa using hn)
  omega

theorem s_eq_natLog (n : ℕ) : s n = Nat.log 2 (Nat.log 2 n) := by
  simp only [s, Nat.log2_eq_log_two]

theorem le_s_iff {n : ℕ} (hn : 2 ≤ n) (a : ℕ) :
    a ≤ s n ↔ 2 ^ (2 ^ a) ≤ n := by
  unfold s
  exact (Nat.le_log2 (Nat.ne_of_gt (log2_pos hn))).trans (Nat.le_log2 (by omega))

theorem s_lt_iff {n : ℕ} (hn : 2 ≤ n) (a : ℕ) :
    s n < a ↔ n < 2 ^ (2 ^ a) := by
  have h := le_s_iff hn a
  omega

theorem pow_s_le_log2 {n : ℕ} (hn : 2 ≤ n) : 2 ^ s n ≤ Nat.log2 n :=
  Nat.log2_self_le (Nat.ne_of_gt (log2_pos hn))

theorem log2_lt_pow_succ_s (n : ℕ) : Nat.log2 n < 2 ^ (s n + 1) :=
  Nat.lt_log2_self

theorem pow_pow_s_le {n : ℕ} (hn : 2 ≤ n) : 2 ^ (2 ^ s n) ≤ n :=
  (le_s_iff hn (s n)).mp le_rfl

theorem n_lt_pow_pow_succ_s {n : ℕ} (hn : 2 ≤ n) :
    n < 2 ^ (2 ^ (s n + 1)) :=
  (s_lt_iff hn (s n + 1)).mp (Nat.lt_succ_self _)

theorem s_le_log2 (n : ℕ) : s n ≤ Nat.log2 n := Nat.log2_le_self _

theorem s_le_n (n : ℕ) : s n ≤ n := (s_le_log2 n).trans (Nat.log2_le_self n)

theorem goodInput_two_le {n : ℕ} (hn : GoodInput n) : 2 ≤ n := by
  have h := s_le_n n
  unfold GoodInput at hn
  omega

theorem goodInput_s_pos {n : ℕ} (hn : GoodInput n) : 0 < s n := by
  unfold GoodInput at hn
  omega

theorem goodInput_iff {n : ℕ} (hn : 2 ≤ n) :
    GoodInput n ↔ 2 ^ (2 ^ 32) ≤ n := le_s_iff hn 32

theorem goodInput_r_ge_two {n : ℕ} (hn : GoodInput n) : 2 ≤ r n := by
  unfold GoodInput at hn
  unfold r
  omega

theorem u_ge_two {n : ℕ} (hn : GoodInput n) : 2 ≤ u n := by
  change 2 ≤ s n / 16
  exact (Nat.le_div_iff_mul_le (by decide)).mpr hn

theorem ell_pos {n : ℕ} (hn : GoodInput n) : 0 < ell n := by
  have h := u_ge_two hn
  unfold ell
  omega

theorem sixteen_mul_u_le (n : ℕ) : 16 * u n ≤ s n := Nat.mul_div_le _ _

theorem s_lt_sixteen_mul_u_add_one (n : ℕ) : s n < 16 * (u n + 1) := by
  change s n < 16 * (s n / 16 + 1)
  have hdiv := Nat.div_add_mod (s n) 16
  have hmod := Nat.mod_lt (s n) (by decide : 0 < 16)
  omega

theorem s_le_thirtytwo_mul_u {n : ℕ} (hn : GoodInput n) : s n ≤ 32 * u n := by
  have hu := u_ge_two hn
  have hs := s_lt_sixteen_mul_u_add_one n
  omega

theorem u_le_s (n : ℕ) : u n ≤ s n := Nat.div_le_self _ _

theorem D_eq_div (n : ℕ) : D n = (n + ell n - 1) / ell n := rfl

theorem D_le_iff {n d : ℕ} (hn : GoodInput n) : D n ≤ d ↔ n ≤ d * ell n :=
  ChunkPartition.count_le_iff (ell_pos hn)

theorem n_le_D_mul_ell {n : ℕ} (hn : GoodInput n) : n ≤ D n * ell n :=
  ChunkPartition.le_count_mul (ell_pos hn)

theorem D_le_div_add_one {n : ℕ} (hn : GoodInput n) : D n ≤ n / ell n + 1 :=
  ChunkPartition.count_le_div_add_one (ell_pos hn)

theorem D_pos {n : ℕ} (hn : GoodInput n) : 0 < D n :=
  (ChunkPartition.count_pos_iff (ell_pos hn)).mpr (by have h := goodInput_two_le hn; omega)

/-- Sizes of the actual chunks for this input-dependent schedule. -/
def chunkSize (n : ℕ) (i : Fin (D n)) : ℕ := ChunkPartition.size n (ell n) i

theorem chunkSize_le (n : ℕ) (i : Fin (D n)) : chunkSize n i ≤ ell n :=
  ChunkPartition.size_le n (ell n) i

theorem sum_chunkSize {n : ℕ} (hn : GoodInput n) :
    (∑ i : Fin (D n), chunkSize n i) = n :=
  ChunkPartition.sum_size n (ell n) (ell_pos hn)

def indexEquiv (n : ℕ) (hn : GoodInput n) :
    Fin n ≃ Σ i : Fin (D n), Fin (chunkSize n i) :=
  ChunkPartition.indexEquiv n (ell n) (ell_pos hn)

theorem tendsto_s_atTop : Filter.Tendsto s Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro a
  refine ⟨max 2 (2 ^ (2 ^ a)), ?_⟩
  intro n hn
  apply (le_s_iff (le_trans (le_max_left _ _) hn) a).mpr
  exact le_trans (le_max_right _ _) hn

theorem eventually_goodInput : ∀ᶠ n in Filter.atTop, GoodInput n := by
  exact (Filter.tendsto_atTop.mp tendsto_s_atTop) 32

/-- Executable primality test; its range of candidate inputs is bounded below. -/
def primeTest (m : ℕ) : Bool := decide (Nat.Prime m)

/-- Scan exactly the integers strictly between `2^u` and `2^(u+1)`.
The second component records the number of primality tests. -/
def primeScan (n : ℕ) : Option ℕ × ℕ :=
  ParameterOrder.scanFrom primeTest (2 ^ u n + 1) (2 ^ u n - 1)

/-- Total input-dependent prime selection. The small-input branch explicitly
returns 3. On `GoodInput`, Bertrand's theorem proves that the finite scan
succeeds, so its fallback value is not used. -/
def p (n : ℕ) : ℕ :=
  if GoodInput n then (primeScan n).1.getD 3 else 3

@[simp] theorem p_of_not_goodInput {n : ℕ} (hn : ¬GoodInput n) : p n = 3 := by
  simp [p, hn]

theorem four_le_two_pow_u {n : ℕ} (hn : GoodInput n) : 4 ≤ 2 ^ u n := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (u_ge_two hn)

theorem exists_interval_prime {n : ℕ} (hn : GoodInput n) :
    ∃ q, Nat.Prime q ∧ 2 ^ u n < q ∧ q < 2 ^ (u n + 1) := by
  have hL := four_le_two_pow_u hn
  obtain ⟨q, hq, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 ^ u n) (by omega)
  have hne : q ≠ 2 * 2 ^ u n := by
    intro heq
    apply Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1) (by omega : 2 ^ u n ≠ 1)
    exact heq ▸ hq
  have hstrict : q < 2 * 2 ^ u n := by omega
  refine ⟨q, hq, hlo, ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using hstrict

theorem primeScan_success {n : ℕ} (hn : GoodInput n) :
    ∃ q, (primeScan n).1 = some q := by
  obtain ⟨q, hq, hlo, hhi⟩ := exists_interval_prime hn
  have hL := four_le_two_pow_u hn
  rw [pow_succ] at hhi
  exact ParameterOrder.scanFrom_complete primeTest (start := 2 ^ u n + 1)
    (fuel := 2 ^ u n - 1) (witness := q) (by omega) (by omega)
    (by simpa [primeTest] using hq)

theorem p_spec {n : ℕ} (hn : GoodInput n) :
    Nat.Prime (p n) ∧ 2 ^ u n < p n ∧ p n < 2 ^ (u n + 1) := by
  obtain ⟨q, hq⟩ := primeScan_success hn
  have hpq : p n = q := by simp [p, hn, hq]
  have hs := ParameterOrder.scanFrom_sound primeTest (show
    (ParameterOrder.scanFrom primeTest (2 ^ u n + 1) (2 ^ u n - 1)).1 = some q from hq)
  have hL := four_le_two_pow_u hn
  rw [hpq]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [primeTest, decide_eq_true_eq] using hs.1
  · have h := hs.2.1
    omega
  · have h := hs.2.2
    rw [pow_succ]
    omega

theorem p_prime (n : ℕ) : Nat.Prime (p n) := by
  by_cases hn : GoodInput n
  · exact (p_spec hn).1
  · rw [p_of_not_goodInput hn]
    decide

theorem p_gt_two (n : ℕ) : 2 < p n := by
  by_cases hn : GoodInput n
  · have h := (p_spec hn).2.1
    have hL := four_le_two_pow_u hn
    omega
  · rw [p_of_not_goodInput hn]
    decide

theorem p_odd (n : ℕ) : Odd (p n) :=
  (p_prime n).eq_two_or_odd'.resolve_left (by have h := p_gt_two n; omega)

theorem p_lower {n : ℕ} (hn : GoodInput n) : 2 ^ u n < p n := (p_spec hn).2.1

theorem p_upper {n : ℕ} (hn : GoodInput n) : p n < 2 ^ (u n + 1) := (p_spec hn).2.2

theorem log2_p {n : ℕ} (hn : GoodInput n) : Nat.log2 (p n) = u n := by
  have hp : p n ≠ 0 := by have h := p_gt_two n; omega
  apply Nat.le_antisymm
  · have h := (Nat.log2_lt hp).mpr (p_upper hn)
    omega
  · exact (Nat.le_log2 hp).mpr (p_lower hn).le

theorem log_p_eq_ell {n : ℕ} (hn : GoodInput n) : Nat.log 2 (p n) = ell n := by
  rw [← Nat.log2_eq_log_two]
  exact log2_p hn

theorem chunk_capacity {n : ℕ} (hn : GoodInput n) (i : Fin (D n)) :
    2 ^ chunkSize n i ≤ p n := by
  have hpow : 2 ^ chunkSize n i ≤ 2 ^ u n :=
    Nat.pow_le_pow_right (by decide) (chunkSize_le n i)
  exact hpow.trans (p_lower hn).le

/-- A bound on the number of primality tests, not a claim of unit bit cost. -/
theorem primeScan_calls_le (n : ℕ) : (primeScan n).2 ≤ 2 ^ u n - 1 :=
  ParameterOrder.scanFrom_calls_le primeTest _ _

end SubexponentialSAT.SubexpPackingParameters

end OAI.Algorithms
