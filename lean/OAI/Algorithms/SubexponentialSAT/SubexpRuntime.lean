import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComputation
import OAI.Algorithms.SubexponentialSAT.SubexpExponentArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters
import OAI.Algorithms.SubexponentialSAT.RuntimeAssembly
import OAI.Algorithms.SubexponentialSAT.QuantitativeBranchTree
import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify

namespace OAI.Algorithms

/-!
# Uniform runtime assembly with growing layout parameters

Unlike the older fixed-width-exponent accounting, all layout parameters are
input-dependent here. `GrowingParameters.entries` exposes every argument of
the polynomial costs in Proposition 4.2 and the layout construction. The
analytic lemmas also pay for the variable-degree sunflower search.

Only the purely numerical work/trace infrastructure from `RuntimeAssembly`
is reused; none of its fixed-prime or exponent-0.9 estimates is used.
-/

namespace SubexponentialSAT.SubexpRuntime

open Filter
open scoped Topology

noncomputable section

/-- Every growing argument in the construction and counting costs. The table
size `p^k` is included explicitly, even when the clause width is fixed. -/
structure GrowingParameters where
  D : ℕ
  Q : ℕ
  R : ℕ
  h : ℕ
  m : ℕ
  r : ℕ
  p : ℕ
  k : ℕ
  incidence : ℕ
  blockSize : ℕ

def GrowingParameters.entries (a : GrowingParameters) : List ℕ :=
  [a.D, a.Q, a.R, a.h, a.m, a.r, a.p ^ a.k, a.k,
    Nat.log2 a.p, a.incidence, a.blockSize]

def GrowingParameters.size (a : GrowingParameters) : ℕ := 1 + a.entries.sum

@[simp] theorem GrowingParameters.entries_length (a : GrowingParameters) :
    a.entries.length = 11 := by simp [GrowingParameters.entries]

theorem GrowingParameters.one_le_size (a : GrowingParameters) : 1 ≤ a.size := by
  unfold GrowingParameters.size
  omega

/-- A simultaneous polynomial bound is derived from bounds on the explicitly
listed parameters, not from an input-dependent hidden polynomial degree. -/
theorem GrowingParameters.size_le {a : GrowingParameters} {B : ℕ}
    (hB : 1 ≤ B) (h : ∀ x ∈ a.entries, x ≤ B) : a.size ≤ 12 * B := by
  have hs := List.sum_le_length_nsmul a.entries B h
  simp only [GrowingParameters.entries_length, nsmul_eq_mul] at hs
  unfold GrowingParameters.size
  omega

theorem GrowingParameters.polynomial_size_le {a : GrowingParameters} {B : ℕ}
    (hB : 1 ≤ B) (h : ∀ x ∈ a.entries, x ≤ B) (q : ℕ) :
    a.size ^ q ≤ 12 ^ q * B ^ q := by
  simpa only [mul_pow] using Nat.pow_le_pow_left (a.size_le hB h) q

/-- The full bit cost of a fixed-degree polynomial in the growing parameters
is bounded by one fixed-degree input polynomial, once each parameter is. -/
theorem uniform_parameter_polynomial_bound {a : GrowingParameters}
    {B : ℕ} (hB : 1 ≤ B) (h : ∀ x ∈ a.entries, x ≤ B)
    (q : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    C * (a.size : ℝ) ^ q ≤ (C * (12 : ℝ) ^ q) * (B : ℝ) ^ q := by
  have hs : (a.size : ℝ) ^ q ≤ (12 : ℝ) ^ q * (B : ℝ) ^ q := by
    exact_mod_cast a.polynomial_size_le hB h q
  calc
    C * (a.size : ℝ) ^ q ≤ C * ((12 : ℝ) ^ q * (B : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left hs hC
    _ = (C * (12 : ℝ) ^ q) * (B : ℝ) ^ q := by ring

/-- Any fixed power of log is eventually dominated by the input size, with
an arbitrary fixed positive coefficient and the source's shift by sixteen. -/
theorem eventually_logb_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℝ in atTop, C * (Real.logb 2 (n + 16)) ^ q ≤ n := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (Real.log (2 : ℝ)) ^ q := pow_pos hl q
  have ht : Tendsto (fun n : ℝ => n + 16) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := q)).bound
    (show 0 < (Real.log (2 : ℝ)) ^ q / (2 * C) by positivity)
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (16 : ℝ)] with n hb hn
  have hn0 : 0 ≤ n + 16 := by linarith
  have hlog0 : 0 ≤ Real.log (n + 16) := Real.log_nonneg (by linarith)
  have hb' : (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16) := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 q), abs_of_nonneg hn0] using hb
  have hmul : C * (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
    calc
      C * (Real.log (n + 16)) ^ q ≤
          C * ((Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16)) :=
        mul_le_mul_of_nonneg_left hb' hC.le
      _ = (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
        field_simp
  calc
    C * (Real.logb 2 (n + 16)) ^ q =
        (C * (Real.log (n + 16)) ^ q) / (Real.log (2 : ℝ)) ^ q := by
      unfold Real.logb
      rw [div_pow]
      ring
    _ ≤ (n + 16) / 2 := (div_le_iff₀ hp).mpr (by nlinarith [hmul])
    _ ≤ n := by linarith

/-- The exponent of the exhaustive per-node sunflower search is negligible
on the claimed scale, for every fixed degree. The degree is not allowed to
depend on n. This is stronger than merely assuming the search is polynomial. -/
theorem eventually_loglog_polynomial_search (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℝ in atTop,
      C * (SubexpExponentArithmetic.shiftedLogLog n + 2) ^ q *
          Real.logb 2 (n + 16) ≤ SubexpExponentArithmetic.scale n := by
  have hsmall := eventually_logb_power_le (q + 2)
    (show 0 < C * (2 : ℝ) ^ q by positivity)
  filter_upwards [hsmall, SubexpExponentArithmetic.eventually_shiftedLogLog_le_logb,
    eventually_ge_atTop (0 : ℝ)] with n hb hiter hn
  let S := SubexpExponentArithmetic.shiftedLogLog n
  let t := Real.logb 2 (n + 16)
  have hS : 0 < S := SubexpExponentArithmetic.shiftedLogLog_pos hn
  have ht : 2 ≤ t := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
      (by linarith : 0 < n + 16)).mpr
    norm_num
    linarith
  have hSt : S ≤ t := hiter
  have hbase : S + 2 ≤ 2 * t := by linarith
  have hpow : (S + 2) ^ q ≤ (2 * t) ^ q :=
    pow_le_pow_left₀ (by linarith) hbase q
  have hproduct : C * (S + 2) ^ q * t * S ≤ n := by
    calc
      C * (S + 2) ^ q * t * S ≤ C * (2 * t) ^ q * t * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
            (by linarith)) hS.le
      _ ≤ C * (2 * t) ^ q * t * t :=
        mul_le_mul_of_nonneg_left hSt (by positivity)
      _ = (C * (2 : ℝ) ^ q) * t ^ (q + 2) := by
        rw [mul_pow, pow_add]
        ring
      _ ≤ n := hb
  exact (le_div_iff₀ hS).mpr hproduct

theorem eventually_natural_search_exponent (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q *
        Real.logb 2 ((n : ℝ) + 1) ≤ SubexpComputation.scale n := by
  have hmain := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_loglog_polynomial_search q hC)
  filter_upwards [hmain, eventually_ge_atTop (2 : ℕ)] with n hn htwo
  have hs : (SubexpPackingParameters.s n : ℝ) ≤
      SubexpExponentArithmetic.shiftedLogLog (n : ℝ) :=
    SubexpExponentArithmetic.natLog2_le_shiftedLogLog htwo
  have hp := pow_le_pow_left₀
    (show (0 : ℝ) ≤ (SubexpPackingParameters.s n : ℝ) + 2 by positivity)
    (by linarith [hs] : (SubexpPackingParameters.s n : ℝ) + 2 ≤
      SubexpExponentArithmetic.shiftedLogLog (n : ℝ) + 2) q
  have hl : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 16) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hSpos : 0 < SubexpExponentArithmetic.shiftedLogLog (n : ℝ) :=
    SubexpExponentArithmetic.shiftedLogLog_pos (Nat.cast_nonneg n)
  calc
    C * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤
        C * (SubexpExponentArithmetic.shiftedLogLog (n : ℝ) + 2) ^ q *
          Real.logb 2 ((n : ℝ) + 16) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hl hl0 (by positivity)
    _ ≤ SubexpComputation.scale n := hn

/-- Actual natural-power operation count for a variable-degree exhaustive
search. A fixed polynomial bound on that degree suffices; no fixed-degree
polynomial-time claim is made for the search itself. -/
theorem eventually_variable_degree_search (degree : ℕ → ℕ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hdegree : ∀ᶠ n : ℕ in atTop,
      (degree n : ℝ) ≤ C * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1) ^ degree n : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [hdegree, eventually_natural_search_exponent q hC] with n hd hn
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hexp : (degree n : ℝ) * Real.logb 2 ((n : ℝ) + 1) ≤
      SubexpComputation.scale n :=
    (mul_le_mul_of_nonneg_right hd hl0).trans hn
  have heq : (((n + 1) ^ degree n : ℕ) : ℝ) =
      (2 : ℝ) ^ ((degree n : ℝ) * Real.logb 2 ((n : ℝ) + 1)) := by
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_natCast]
    exact SubexpExponentArithmetic.rpow_eq_two_rpow_logb (by positivity) _
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- The actual deterministic tree selected at inverse budget `s n`. -/
def selectedTree {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) :=
  Sparsify.treeFor (SparsificationBudget.chooseM k hk (SubexpPackingParameters.s n)) k
    (SparsificationBudget.chooseM_ge_two k hk (SubexpPackingParameters.s n)) F

/-- The all-node count of the actual selected tree, with constants chosen
before the input size and with the polynomial transferred to encoding length. -/
theorem selected_tree_node_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, 0 < C ∧ ∀ (n : ℕ), SubexpPackingParameters.GoodInput n →
      ∀ F : SAT.CNF (Fin n),
        ((selectedTree k hk F).shape.nodeCount : ℝ) ≤
          SubexpComputation.runtimeBound (C : ℝ) 2 d (Encoding.formulaBitLength F) n := by
  obtain ⟨A, d, hnodes⟩ := QuantitativeBranchTree.exists_selected_node_polynomial k hk
  refine ⟨A + 1, d + 2, by omega, ?_⟩
  intro n hn F
  have hbound := hnodes (SubexpPackingParameters.s n)
    (SubexpPackingParameters.goodInput_s_pos hn) F
  have hs : (SubexpPackingParameters.s n : ℝ) ≤
      (Encoding.formulaBitLength F : ℝ) + 1 := by
    have hnat := (SubexpPackingParameters.s_le_n n).trans
      (Encoding.numVariables_le_formulaBitLength F)
    have hreal : (SubexpPackingParameters.s n : ℝ) ≤ Encoding.formulaBitLength F := by
      exact_mod_cast hnat
    linarith
  have hnL : (n : ℝ) + 1 ≤ (Encoding.formulaBitLength F : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Encoding.numVariables_le_formulaBitLength F) 1
  have hpoly : (A : ℝ) * (SubexpPackingParameters.s n : ℝ) ^ d * ((n : ℝ) + 1) ^ 2 ≤
      (A + 1 : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (d + 2) := by
    have h₁ := pow_le_pow_left₀ (Nat.cast_nonneg (SubexpPackingParameters.s n)) hs d
    have h₂ := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hnL 2
    calc
      (A : ℝ) * (SubexpPackingParameters.s n : ℝ) ^ d * ((n : ℝ) + 1) ^ 2 ≤
          (A : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ d *
            ((Encoding.formulaBitLength F : ℝ) + 1) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg A)) h₂
          (by positivity) (by positivity)
      _ = (A : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (d + 2) := by rw [pow_add]; ring
      _ ≤ (A + 1 : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (d + 2) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hn16 : 16 ≤ n := by
    have hsn := SubexpPackingParameters.s_le_n n
    unfold SubexpPackingParameters.GoodInput at hn
    omega
  have hratio : (n : ℝ) / (SubexpPackingParameters.s n : ℝ) ≤
      2 * SubexpComputation.scale n :=
    SubexpExponentArithmetic.natLog2_ratio_le_twice_scale hn16
  have hexp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hratio
  change ((selectedTree k hk F).shape.nodeCount : ℝ) ≤ _ at hbound
  unfold SubexpComputation.runtimeBound
  push_cast
  exact hbound.trans (mul_le_mul hpoly hexp (Real.rpow_nonneg (by norm_num) _) (by positivity))

/-- Multiplying all visited nodes by the explicit exhaustive-search count
still has the required rate. This is a counting theorem; primitive simulation
cost is charged separately by the compiler/runtime layer. -/
theorem selected_tree_search_bound (k : ℕ) (hk : 2 ≤ k)
    (degree : ℕ → ℕ) (q : ℕ) {A : ℝ} (hA : 0 < A)
    (hdegree : ∀ᶠ n : ℕ in atTop,
      (degree n : ℝ) ≤ A * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q) :
    ∃ C d : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ F : SAT.CNF (Fin n), SubexpPackingParameters.GoodInput n →
        ((selectedTree k hk F).shape.nodeCount : ℝ) * (((n + 1) ^ degree n : ℕ) : ℝ) ≤
          SubexpComputation.runtimeBound (C : ℝ) 3 d (Encoding.formulaBitLength F) n := by
  obtain ⟨C, d, hC, hnodes⟩ := selected_tree_node_bound k hk
  refine ⟨C, d, hC, ?_⟩
  filter_upwards [eventually_variable_degree_search degree q hA hdegree] with n hsearch
  intro F hn
  have ht := hnodes n hn F
  calc
    ((selectedTree k hk F).shape.nodeCount : ℝ) * (((n + 1) ^ degree n : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound (C : ℝ) 2 d (Encoding.formulaBitLength F) n *
          (2 : ℝ) ^ SubexpComputation.scale n :=
      mul_le_mul ht hsearch (Nat.cast_nonneg _)
        (SubexpComputation.runtimeBound_nonneg (Nat.cast_nonneg C) _ _ _ _)
    _ = SubexpComputation.runtimeBound (C : ℝ) 3 d (Encoding.formulaBitLength F) n := by
      unfold SubexpComputation.runtimeBound
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- The actual candidate lists selected by the quantitative sparsifier have
subexponential length. The operation cost of checking/generating an entry is
not silently identified with one bit step. -/
theorem eventually_chosen_candidate_bound (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ), j ≤ k → ∀ F : SAT.CNF (Fin n),
      SAT.WidthAtMost k F → 0 < n →
      ((Sparsify.candidates F (SparsificationConstants.z
        (SparsificationBudget.chooseM k hk (SubexpPackingParameters.s n))) j).length : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.chosen_candidate_count_power k hk
  have hdegree : ∀ᶠ n : ℕ in atTop,
      (((SubexpPackingParameters.s n + 2) ^ q : ℕ) : ℝ) ≤
        (1 : ℝ) * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q := by
    exact Eventually.of_forall (fun n => by simp)
  have hsearch := eventually_variable_degree_search
    (fun n => (SubexpPackingParameters.s n + 2) ^ q) q (by norm_num : (0 : ℝ) < 1) hdegree
  filter_upwards [hsearch] with n hn
  intro j hj F hF hpos
  have hnat := hq (SubexpPackingParameters.s n) j hj F hF hpos
  have hreal : ((Sparsify.candidates F (SparsificationConstants.z
      (SparsificationBudget.chooseM k hk (SubexpPackingParameters.s n))) j).length : ℝ) ≤
      (((n + 1) ^ ((SubexpPackingParameters.s n + 2) ^ q) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hn

/-- The node-visit counter returned by the executable list worklist, not an
unrelated abstract tree, obeys one uniform subexponential envelope. -/
theorem executable_visits_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, 0 < C ∧ ∀ (n : ℕ), SubexpPackingParameters.GoodInput n →
      ∀ F : SAT.CNF (Fin n),
        ((ExecQuantitativeSparsify.chosenExecute k hk (SubexpPackingParameters.s n)
          (ExecQuantitativeSparsify.formulaList F)).visits : ℝ) ≤
          SubexpComputation.runtimeBound (C : ℝ) 2 d (Encoding.formulaBitLength F) n := by
  obtain ⟨A, q, hnodes⟩ := ExecQuantitativeSparsify.chosenExecute_visits_polynomial k hk
  refine ⟨(A + 1) * 2 ^ q, q + 2, by positivity, ?_⟩
  intro n hn F
  have hbound := hnodes (SubexpPackingParameters.s n)
    (SubexpPackingParameters.goodInput_s_pos hn) (ExecQuantitativeSparsify.formulaList F)
  have hsL : (SubexpPackingParameters.s n : ℝ) ≤ Encoding.formulaBitLength F := by
    exact_mod_cast (SubexpPackingParameters.s_le_n n).trans
      (Encoding.numVariables_le_formulaBitLength F)
  have hs : (SubexpPackingParameters.s n : ℝ) + 2 ≤
      2 * ((Encoding.formulaBitLength F : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) (Encoding.formulaBitLength F)
    linarith
  have hnL : (n : ℝ) + 1 ≤ (Encoding.formulaBitLength F : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Encoding.numVariables_le_formulaBitLength F) 1
  have hp := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ (SubexpPackingParameters.s n : ℝ) + 2) hs q
  have hq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hnL 2
  have hpoly : (A : ℝ) * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 ≤
      ((A + 1) * 2 ^ q : ℕ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (q + 2) := by
    calc
      (A : ℝ) * ((SubexpPackingParameters.s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 ≤
          (A : ℝ) * (2 * ((Encoding.formulaBitLength F : ℝ) + 1)) ^ q *
            ((Encoding.formulaBitLength F : ℝ) + 1) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg A)) hq
          (by positivity) (by positivity)
      _ = (A : ℝ) * (2 : ℝ) ^ q * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (q + 2) := by
        rw [mul_pow, pow_add]
        ring
      _ ≤ ((A + 1) * 2 ^ q : ℕ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ (q + 2) := by
        push_cast
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  have hn16 : 16 ≤ n := by
    have hsn := SubexpPackingParameters.s_le_n n
    unfold SubexpPackingParameters.GoodInput at hn
    omega
  have hratio : (n : ℝ) / (SubexpPackingParameters.s n : ℝ) ≤
      2 * SubexpComputation.scale n :=
    SubexpExponentArithmetic.natLog2_ratio_le_twice_scale hn16
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hratio
  exact hbound.trans (mul_le_mul hpoly he (Real.rpow_nonneg (by norm_num) _) (by positivity))

/-- Generic envelope composition for the actual phase-cost sum. The three
exponent constants respectively charge per-event work, tree cardinality,
and leaf enumeration. All remain fixed before n. -/
theorem total_bound_from_envelopes
    {P E W C a b c : ℝ} {d L n : ℕ} {work : RuntimeAssembly.Work}
    (hwork : RuntimeAssembly.WorkBounds P E W work)
    (hP1 : 1 ≤ P) (hE1 : 1 ≤ E) (hW1 : 1 ≤ W)
    (_hC : 0 ≤ C)
    (hP : P ≤ SubexpComputation.runtimeBound C a d L n)
    (hE : E ≤ (2 : ℝ) ^ (b * SubexpComputation.scale n))
    (hW : W ≤ (2 : ℝ) ^ (c * SubexpComputation.scale n)) :
    (work.total : ℝ) ≤ SubexpComputation.runtimeBound
      (8 * C ^ 2) (2 * a + b + c) (2 * d) L n := by
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP1
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW1
  have hEW := mul_le_mul hE hW hW0 (Real.rpow_nonneg (by norm_num) _)
  have hP2 := pow_le_pow_left₀ hP0 hP 2
  calc
    (work.total : ℝ) ≤ 8 * P ^ 2 * E * W :=
      RuntimeAssembly.total_le_eight_polynomial_sq hwork hP1 hE1 hW1
    _ = (8 * P ^ 2) * (E * W) := by ring
    _ ≤ (8 * SubexpComputation.runtimeBound C a d L n ^ 2) *
        ((2 : ℝ) ^ (b * SubexpComputation.scale n) *
          (2 : ℝ) ^ (c * SubexpComputation.scale n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP2 (by norm_num)) hEW
        (mul_nonneg (le_trans (by norm_num) hE1) hW0) (by positivity)
    _ = SubexpComputation.runtimeBound (8 * C ^ 2) (2 * a + b + c) (2 * d) L n := by
      unfold SubexpComputation.runtimeBound
      rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show d * 2 = 2 * d by omega]
      have he : a * SubexpComputation.scale n * (2 : ℕ) +
          (b * SubexpComputation.scale n + c * SubexpComputation.scale n) =
          (2 * a + b + c) * SubexpComputation.scale n := by ring
      calc
        8 * (C ^ 2 * ((L : ℝ) + 1) ^ (2 * d) *
            (2 : ℝ) ^ (a * SubexpComputation.scale n * (2 : ℕ))) *
            (2 : ℝ) ^ (b * SubexpComputation.scale n + c * SubexpComputation.scale n) =
          (8 * C ^ 2) * ((L : ℝ) + 1) ^ (2 * d) *
            ((2 : ℝ) ^ (a * SubexpComputation.scale n * (2 : ℕ)) *
             (2 : ℝ) ^ (b * SubexpComputation.scale n + c * SubexpComputation.scale n)) := by ring
        _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he]

/-- Once all phase executions and local quantitative bounds are supplied,
the same concrete primitive run has the assembled subexponential bound. -/
theorem pipeline_output_bound
    {machine : Computation.PrimitiveMachine} {n : ℕ} {F : SAT.CNF (Fin n)}
    {answer : Bool} {work : RuntimeAssembly.Work} {P E W C a b c : ℝ} {d : ℕ}
    (execution : RuntimeAssembly.PipelineExecution machine F answer work)
    (reduction : RuntimeAssembly.ReductionCertificate F answer work)
    (hwork : RuntimeAssembly.WorkBounds P E W work)
    (hP1 : 1 ≤ P) (hE1 : 1 ≤ E) (hW1 : 1 ≤ W) (hC : 0 ≤ C)
    (hP : P ≤ SubexpComputation.runtimeBound C a d (Encoding.formulaBitLength F) n)
    (hE : E ≤ (2 : ℝ) ^ (b * SubexpComputation.scale n))
    (hW : W ≤ (2 : ℝ) ^ (c * SubexpComputation.scale n)) :
    machine.OutputsInTime (Encoding.encodeCNF F) answer work.total ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (work.total : ℝ) ≤ SubexpComputation.runtimeBound
        (8 * C ^ 2) (2 * a + b + c) (2 * d) (Encoding.formulaBitLength F) n :=
  ⟨execution.outputs, reduction.correct,
    total_bound_from_envelopes hwork hP1 hE1 hW1 hC hP hE hW⟩

end
end SubexponentialSAT.SubexpRuntime

end OAI.Algorithms
