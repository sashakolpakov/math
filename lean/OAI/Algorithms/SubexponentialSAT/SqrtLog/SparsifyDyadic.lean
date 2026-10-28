import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Sparsify
import OAI.Algorithms.SubexponentialSAT.SparsificationBudgetProgram

namespace OAI.Algorithms

/-!
# Explicit dyadic splitter at an arbitrary reciprocal budget

Unlike the least-passing `chosenLeaves` parameter, this parameter is emitted
by the existing fixed primitive arithmetic program.  Its width-dependent
control constant is chosen once, before the input size or reciprocal budget.
No old double-logarithmic schedule is built into these statements.
-/

namespace SubexponentialSAT.SqrtLog.SparsifyDyadic

open SAT SparsificationBudgetProgram

variable {n : ℕ}

abbrev execute (k T s : ℕ) (F : ExecQuantitativeSparsify.Formula n) :=
  ExecQuantitativeSparsify.executeFor (dyadicM T s) k (dyadicM_ge_two T s) F

abbrev leaves (k T s : ℕ) (F : CNF (Fin n)) :=
  ExecQuantitativeSparsify.leavesFor (dyadicM T s) k (dyadicM_ge_two T s) F

def occurrenceBound (k T s : ℕ) : ℕ :=
  SparsificationConstants.occurrenceCap (dyadicM T s) k

theorem leaves_eval_iff (k T s : ℕ) (F : CNF (Fin n)) (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ leaves k T s F, G.eval a = true :=
  ExecQuantitativeSparsify.leavesFor_eval_iff _ _ _ F a

theorem leaves_sat_iff (k T s : ℕ) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ leaves k T s F, Satisfiable G :=
  ExecQuantitativeSparsify.leavesFor_correct _ _ _ F

theorem leaves_spec (k T s : ℕ) (F : CNF (Fin n)) (hF : WidthAtMost k F) :
    ∀ G ∈ leaves k T s F,
      WidthAtMost k G ∧ OccurrenceAtMost (occurrenceBound k T s) G := by
  intro G hG
  exact ⟨ExecQuantitativeSparsify.leavesFor_width _ _ _ F hF G hG,
    ExecQuantitativeSparsify.leavesFor_occurrence _ _ _ F hF G hG⟩

theorem occurrenceBound_power (k T : ℕ) :
    ∃ q : ℕ, ∀ s, occurrenceBound k T s ≤ (s + 2) ^ q :=
  QuantitativeSparsify.polynomialBound_shift_power
    (dyadicOccurrenceCap_polynomialBound T k)

/-- Exact worklist visits, not primitive instructions inside each visit. -/
theorem visits_polynomial (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A q : ℕ, ∀ (s : ℕ), 0 < s → ∀ {n : ℕ}
      (F : ExecQuantitativeSparsify.Formula n),
      ((execute k T s F).visits : ℝ) ≤
        (A : ℝ) * ((s : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / s) := by
  have hp : SparsificationConstants.PolynomialBound (fun s =>
      (SparsificationConstants.C (dyadicM T s) (k - 1) + 1) * (k + 1)) :=
    ((dyadicC_polynomialBound T (k - 1)).add
      (SparsificationConstants.polynomialBound_const 1)).mul
        (SparsificationConstants.polynomialBound_const (k + 1))
  obtain ⟨A, q, hpoly⟩ := QuantitativeSparsify.polynomialBound_shift hp
  refine ⟨A, q, ?_⟩
  intro s hs n F
  have h := ExecSparsifyWorklist.execute_visits_quantitative (dyadicM T s) k
    (dyadicM_ge_two T s) (by omega) ((1 : ℝ) / s) F
      (hT.ratio_le hk s hs) (hT.logb_budget hk s hs)
  have hc : ((SparsificationConstants.C (dyadicM T s) (k - 1) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ≤ (A : ℝ) * ((s : ℝ) + 2) ^ q := by
    exact_mod_cast hpoly s
  have h' := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num) _))
  simpa only [execute, ExecQuantitativeSparsify.executeFor, one_div,
    inv_mul_eq_div] using h'

theorem leaves_length_le_visits (k T s : ℕ) (F : CNF (Fin n)) :
    (leaves k T s F).length ≤
      (execute k T s (ExecQuantitativeSparsify.formulaList F)).visits := by
  have h := ExecSparsifyWorklist.initial_run_leaves_length_le_visits
    (ExecSparsifyWorklist.executableBranching
      (SparsificationConstants.z (dyadicM T s)) k
      (fun d hd => SparsificationConstants.threshold_ge_two _ d
        (dyadicM_ge_two T s) hd))
    (ExecSparsifyWorklist.normalizedInput (ExecQuantitativeSparsify.formulaList F))
  simpa only [leaves, execute, ExecQuantitativeSparsify.leavesFor,
    ExecQuantitativeSparsify.executeFor, ExecSparsifyWorklist.execute,
    List.length_map] using h

theorem leaves_length_polynomial (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A q : ℕ, ∀ (s : ℕ), 0 < s → ∀ {n : ℕ} (F : CNF (Fin n)),
      ((leaves k T s F).length : ℝ) ≤
        (A : ℝ) * ((s : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / s) := by
  obtain ⟨A, q, h⟩ := visits_polynomial k T hk hT
  refine ⟨A, q, ?_⟩
  intro s hs n F
  exact (Nat.cast_le.mpr (leaves_length_le_visits k T s F)).trans
    (h s hs (ExecQuantitativeSparsify.formulaList F))

def candidateExponent (k T s : ℕ) : ℕ :=
  2 * k * (SparsificationBudget.thresholdCap (dyadicM T s) k + 1) + k

theorem candidateExponent_polynomialBound (k T : ℕ) :
    SparsificationConstants.PolynomialBound (candidateExponent k T) :=
  ((SparsificationConstants.polynomialBound_const (2 * k)).mul
    ((dyadicThresholdCap_polynomialBound T k).add
      (SparsificationConstants.polynomialBound_const 1))).add
        (SparsificationConstants.polynomialBound_const k)

theorem candidate_count_le (k T s d : ℕ) (hd : d ≤ k)
    (F : CNF (Fin n)) (hF : WidthAtMost k F) (hn : 0 < n) :
    (SubexponentialSAT.Sparsify.candidates F (SparsificationConstants.z (dyadicM T s)) d).length ≤
      (n + 1) ^ candidateExponent k T s := by
  have hz := SparsificationBudget.z_le_thresholdCap (dyadicM T s) k d hd
  have hbase : 2 * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have htwo : 2 ≤ n + 1 := by omega
  calc
    _ ≤ (2 * n + 1) ^ (k * (SparsificationConstants.z (dyadicM T s) d + 1)) *
        2 ^ k := QuantitativeSparsify.candidate_count_le F _ d k hF
    _ ≤ ((n + 1) ^ 2) ^ (k * (SparsificationConstants.z (dyadicM T s) d + 1)) *
        (n + 1) ^ k :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left htwo _)
    _ = (n + 1) ^ (2 * k * (SparsificationConstants.z (dyadicM T s) d + 1) + k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ (n + 1) ^ candidateExponent k T s := by
      apply Nat.pow_le_pow_right (by omega)
      unfold candidateExponent
      nlinarith

theorem candidate_count_power (k T : ℕ) :
    ∃ q : ℕ, ∀ (s d : ℕ), d ≤ k → ∀ {n : ℕ} (F : CNF (Fin n)),
      WidthAtMost k F → 0 < n →
      (SubexponentialSAT.Sparsify.candidates F (SparsificationConstants.z (dyadicM T s)) d).length ≤
        (n + 1) ^ ((s + 2) ^ q) := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power
    (candidateExponent_polynomialBound k T)
  refine ⟨q, ?_⟩
  intro s d hd n F hF hn
  exact (candidate_count_le k T s d hd F hF hn).trans
    (Nat.pow_le_pow_right (by omega) (hq s))

def liveLeaves (k T s : ℕ) (F : CNF (Fin n)) : List (CNF (Fin n)) :=
  (leaves k T s F).filter (fun G => decide ((∅ : Clause (Fin n)) ∉ G))

theorem mem_liveLeaves (k T s : ℕ) (F G : CNF (Fin n)) :
    G ∈ liveLeaves k T s F ↔
      G ∈ leaves k T s F ∧ (∅ : Clause (Fin n)) ∉ G := by
  simp [liveLeaves]

theorem liveLeaves_sat_iff (k T s : ℕ) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ liveLeaves k T s F, Satisfiable G := by
  rw [leaves_sat_iff k T s F]
  constructor
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, (mem_liveLeaves k T s F G).mpr
      ⟨hG, Sparsify.empty_clause_not_mem_of_sat G hsat⟩, hsat⟩
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, ((mem_liveLeaves k T s F G).mp hG).1, hsat⟩

theorem liveLeaves_spec (k T s : ℕ) (F : CNF (Fin n)) (hF : WidthAtMost k F) :
    ∀ G ∈ liveLeaves k T s F,
      WidthAtMost k G ∧ OccurrenceAtMost (occurrenceBound k T s) G ∧
        G.card ≤ n * occurrenceBound k T s := by
  intro G hG
  obtain ⟨hleaf, hempty⟩ := (mem_liveLeaves k T s F G).mp hG
  obtain ⟨hw, hb⟩ := leaves_spec k T s F hF G hleaf
  exact ⟨hw, hb, Sparsify.clause_count_le_of_occurrence G _ hb hempty⟩

theorem liveLeaves_length_le (k T s : ℕ) (F : CNF (Fin n)) :
    (liveLeaves k T s F).length ≤ (leaves k T s F).length :=
  List.length_filter_le _ _

def decideByLeaves (k T s : ℕ) (decideLeaf : CNF (Fin n) → Bool)
    (F : CNF (Fin n)) : Bool :=
  (liveLeaves k T s F).any decideLeaf

theorem decideByLeaves_correct (k T s : ℕ) (decideLeaf : CNF (Fin n) → Bool)
    (F : CNF (Fin n))
    (hdecide : ∀ G ∈ liveLeaves k T s F,
      decideLeaf G = true ↔ Satisfiable G) :
    decideByLeaves k T s decideLeaf F = true ↔ Satisfiable F := by
  rw [liveLeaves_sat_iff k T s F]
  simp only [decideByLeaves, List.any_eq_true]
  constructor
  · rintro ⟨G, hG, hyes⟩
    exact ⟨G, hG, (hdecide G hG).mp hyes⟩
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, hG, (hdecide G hG).mpr hsat⟩

end SubexponentialSAT.SqrtLog.SparsifyDyadic

end OAI.Algorithms
