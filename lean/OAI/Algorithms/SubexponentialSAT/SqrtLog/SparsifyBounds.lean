import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyDyadic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticTarget

namespace OAI.Algorithms

/-!
# Dyadic splitter bounds at the square-root-logarithmic schedule

Every exponent and threshold constant is fixed before the ambient size.
The candidate-count bound is not a primitive runtime theorem: it prices the
finite search space, while the instruction implementation is separate.
-/

namespace SubexponentialSAT.SqrtLog.SparsifyBounds

open SAT Filter
open scoped Topology
open Asymptotic

theorem occurrence_le_log_power (k T : ℕ) :
    ∃ q : ℕ, ∀ n,
      SparsifyDyadic.occurrenceBound k T (s n) ≤ (L n + 2) ^ q := by
  obtain ⟨q, hq⟩ := SparsifyDyadic.occurrenceBound_power k T
  exact ⟨q, fun n => (hq (s n)).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (s_le_L n) 2) q)⟩

theorem eventually_candidate_count_target (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ), d ≤ k → ∀ F : CNF (Fin n),
      WidthAtMost k F →
      (((SubexponentialSAT.Sparsify.candidates F
        (SparsificationConstants.z (SparsificationBudgetProgram.dyadicM T (s n)))
          d).length : ℕ) : ℝ) ≤ (2 : ℝ) ^ Statement.runtimeScale n := by
  obtain ⟨q, hq⟩ := SparsifyDyadic.candidate_count_power k T
  have hb := eventually_variable_search_target (fun n => (s n + 2) ^ q) q
    (C := 1) (by norm_num) (Filter.Eventually.of_forall (fun n => by
      simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, one_mul]
      exact le_rfl))
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  intro d hd F hF
  exact (Nat.cast_le.mpr (hq (s n) d hd F hF (by omega))).trans hn

private theorem schedule_add_two_le (n : ℕ) (hn : 17 ≤ n) :
    s n + 2 ≤ 2 * (n + 1) := by
  have hs := s_le_L n
  have hl : Nat.log 2 (n + 16) ≤ n + 16 := Nat.log_le_self _ _
  simp only [L, Nat.log2_eq_log_two] at hs
  omega

/-- The fixed polynomial prefactor in the worklist bound is negligible. -/
theorem eventually_prefactor_target (A q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * ((s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 ≤
        (2 : ℝ) ^ Statement.runtimeScale n := by
  have hb := eventually_variable_search_target (fun _n => q + 3) 0
    (C := (q : ℝ) + 3) (by positivity)
    (Filter.Eventually.of_forall (fun n => by simp))
  filter_upwards [hb, eventually_ge_atTop (17 : ℕ),
    eventually_ge_atTop (A * 2 ^ q)] with n hbound hn hA
  have hs := schedule_add_two_le n hn
  have hnat : A * (s n + 2) ^ q * (n + 1) ^ 2 ≤ (n + 1) ^ (q + 3) := by
    calc
      _ ≤ A * (2 * (n + 1)) ^ q * (n + 1) ^ 2 := by gcongr
      _ = (A * 2 ^ q) * (n + 1) ^ (q + 2) := by rw [mul_pow, pow_add]; ring
      _ ≤ (n + 1) * (n + 1) ^ (q + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (n + 1) ^ (q + 3) := by rw [show q + 3 = (q + 2) + 1 by omega, pow_succ]; ring
  have hreal : (A : ℝ) * ((s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 ≤
      (((n + 1) ^ (q + 3) : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hreal.trans hbound

/-- All worklist visits fit the desired exponent. Internal search instructions
are deliberately not identified with these visits. -/
theorem eventually_visits_target (k T : ℕ) (hk : 2 ≤ k)
    (hT : SparsificationBudgetProgram.Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ F : ExecQuantitativeSparsify.Formula n,
      ((SparsifyDyadic.execute k T (s n) F).visits : ℝ) ≤
        (2 : ℝ) ^ (129 * Statement.runtimeScale n) := by
  obtain ⟨A, q, hq⟩ := SparsifyDyadic.visits_polynomial k T hk hT
  filter_upwards [eventually_prefactor_target A q, eventually_le_s 1,
    eventually_inverse_schedule_target] with n hp hs hi
  intro F
  have he : (2 : ℝ) ^ ((n : ℝ) / s n) ≤
      (2 : ℝ) ^ (128 * Statement.runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hi
  calc
    _ ≤ (A : ℝ) * ((s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s n) := hq (s n) (by omega) F
    _ ≤ (2 : ℝ) ^ Statement.runtimeScale n *
        (2 : ℝ) ^ (128 * Statement.runtimeScale n) :=
      mul_le_mul hp he (Real.rpow_nonneg (by norm_num) _) (by positivity)
    _ = (2 : ℝ) ^ (129 * Statement.runtimeScale n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem eventually_liveLeaves_length_target (k T : ℕ) (hk : 2 ≤ k)
    (hT : SparsificationBudgetProgram.Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ F : CNF (Fin n),
      ((SparsifyDyadic.liveLeaves k T (s n) F).length : ℝ) ≤
        (2 : ℝ) ^ (129 * Statement.runtimeScale n) := by
  filter_upwards [eventually_visits_target k T hk hT] with n hn
  intro F
  exact (Nat.cast_le.mpr ((SparsifyDyadic.liveLeaves_length_le k T (s n) F).trans
    (SparsifyDyadic.leaves_length_le_visits k T (s n) F))).trans
      (hn (ExecQuantitativeSparsify.formulaList F))

/-- A sparse leaf can be passed to the new counting algorithm with the
original ambient variable count, including all unused variables. -/
theorem scheduled_leaf_spec (k T : ℕ) :
    ∃ q : ℕ, ∀ {n : ℕ} (F : CNF (Fin n)), WidthAtMost k F →
      ∀ G ∈ SparsifyDyadic.liveLeaves k T (s n) F,
        WidthAtMost k G ∧ OccurrenceAtMost ((L n + 2) ^ q) G ∧
          G.card ≤ n * (L n + 2) ^ q := by
  obtain ⟨q, hq⟩ := occurrence_le_log_power k T
  refine ⟨q, ?_⟩
  intro n F hF G hG
  obtain ⟨hw, hocc, hcard⟩ := SparsifyDyadic.liveLeaves_spec k T (s n) F hF G hG
  exact ⟨hw, fun v => (hocc v).trans (hq n),
    hcard.trans (Nat.mul_le_mul_left n (hq n))⟩

/-- The complete output-side interface. Primitive implementation of the
splitter and of the leaf solver are separate, explicitly retained obligations. -/
theorem exists_scheduled_cover (k : ℕ) (hk : 2 ≤ k) :
    ∃ T q : ℕ, SparsificationBudgetProgram.Control k T ∧
      (∀ {n : ℕ} (F : CNF (Fin n)), WidthAtMost k F →
        (Satisfiable F ↔
          ∃ G ∈ SparsifyDyadic.liveLeaves k T (s n) F, Satisfiable G) ∧
        (∀ G ∈ SparsifyDyadic.liveLeaves k T (s n) F,
          WidthAtMost k G ∧ OccurrenceAtMost ((L n + 2) ^ q) G ∧
            G.card ≤ n * (L n + 2) ^ q)) ∧
      (∀ᶠ n : ℕ in atTop, ∀ F : CNF (Fin n),
        ((SparsifyDyadic.liveLeaves k T (s n) F).length : ℝ) ≤
          (2 : ℝ) ^ (129 * Statement.runtimeScale n)) := by
  obtain ⟨T, hT⟩ := SparsificationBudgetProgram.exists_control k
  obtain ⟨q, hq⟩ := scheduled_leaf_spec k T
  refine ⟨T, q, hT, ?_, eventually_liveLeaves_length_target k T hk hT⟩
  intro n F hF
  exact ⟨SparsifyDyadic.liveLeaves_sat_iff k T (s n) F, hq F hF⟩

end SubexponentialSAT.SqrtLog.SparsifyBounds

end OAI.Algorithms
