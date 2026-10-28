import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuantitativeBranchTree
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget

namespace OAI.Algorithms

/-!
# Sparsification with a variable budget

The threshold parameter is an explicit input to this interface.  In particular,
none of these definitions uses the fixed `1/32` selector from the earlier
manuscript.  The returned list is the output of the terminating syntactic
sunflower algorithm.  Its pointwise semantics is a union of satisfying sets;
the leaves need not be disjoint.
-/

namespace SubexponentialSAT.QuantitativeSparsify

open SAT

variable {n : ℕ}

private def paddingCode : Option ℕ → ℕ
  | none => 0
  | some a => a + 1

private theorem paddingCode_injective : Function.Injective paddingCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [paddingCode]

/-- Sorted literal codes padded with zero to a fixed width.  Real literal codes
are shifted by one, so padding cannot collide with a literal. -/
def clauseVector (k : ℕ) (C : Clause (Fin n)) (i : Fin k) : Fin (2 * n + 1) :=
  ⟨paddingCode ((Encoding.clauseNumbers C)[i.val]?), by
    cases hs : (Encoding.clauseNumbers C)[i.val]? with
    | none => simp [paddingCode]
    | some a =>
        have ha := Encoding.mem_clauseNumbers_lt (List.mem_of_getElem? hs)
        simp only [paddingCode]
        omega⟩

theorem clauseVector_injective_of_width (k : ℕ) {C D : Clause (Fin n)}
    (hC : C.card ≤ k) (hD : D.card ≤ k)
    (h : clauseVector k C = clauseVector k D) : C = D := by
  apply Encoding.clauseNumbers_injective
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have he := congrArg (fun f => (f ⟨i, hi⟩).val) h
    exact paddingCode_injective he
  · have hCi : (Encoding.clauseNumbers C).length ≤ i := by
      rw [Encoding.length_clauseNumbers]
      omega
    have hDi : (Encoding.clauseNumbers D).length ≤ i := by
      rw [Encoding.length_clauseNumbers]
      omega
    rw [List.getElem?_eq_none hCi, List.getElem?_eq_none hDi]

/-- There are at most (2n+1)^k different clauses of width at most k, including
the empty clause.  No normalization or semantic assumption is needed. -/
theorem clause_count_le (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    F.card ≤ (2 * n + 1) ^ k := by
  have h : F.card ≤ (Finset.univ : Finset (Fin k → Fin (2 * n + 1))).card := by
    apply Finset.card_le_card_of_injOn (clauseVector k) (fun _ _ => Finset.mem_univ _)
    intro C hC D hD he
    exact clauseVector_injective_of_width k (hF C hC) (hF D hD) he
  simpa using h

/-- A bound on enumerated candidate pairs in terms of variable count.  This
counts candidates; testing and generating a candidate still require work. -/
theorem candidate_count_le (F : CNF (Fin n)) (z : ℕ → ℕ) (d k : ℕ)
    (hF : WidthAtMost k F) :
    (Sparsify.candidates F z d).length ≤ (2 * n + 1) ^ (k * (z d + 1)) * 2 ^ k := by
  calc
    (Sparsify.candidates F z d).length ≤ F.card ^ (z d + 1) * 2 ^ k :=
      Sparsify.candidates_length_le F z d k hF
    _ ≤ ((2 * n + 1) ^ k) ^ (z d + 1) * 2 ^ k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (clause_count_le F k hF) _)
    _ = (2 * n + 1) ^ (k * (z d + 1)) * 2 ^ k := by rw [pow_mul]

/-- The actual deterministic leaf list for the explicit threshold parameter. -/
def leavesFor (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) : List (CNF (Fin n)) :=
  (Sparsify.treeFor M k hM F).leaves

/-- Every individual assignment is preserved by the union of leaves. -/
theorem decomposition_eval_iff {z : ℕ → ℕ} {k : ℕ} {F : CNF (Fin n)}
    (tree : Sparsify.Decomposition z k F) (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ tree.leaves, G.eval a = true := by
  induction tree with
  | leaf F ht => simp [Sparsify.Decomposition.leaves]
  | @branch F c left right ihL ihR =>
      simp only [Sparsify.Decomposition.leaves, List.mem_append, or_and_right, exists_or]
      rw [← ihL, ← ihR]
      exact SunflowerBranch.eval_children_iff a F c.flower.core c.flower.petals c.present

theorem leavesFor_eval_iff (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ leavesFor M k hM F, G.eval a = true := by
  have h := decomposition_eval_iff (Sparsify.treeFor M k hM F) a
  simpa only [eval_normalize, leavesFor] using h

theorem leavesFor_correct (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ leavesFor M k hM F, Satisfiable G :=
  (satisfiable_normalize F).symm.trans (Sparsify.treeFor M k hM F).covers

/-- A finite-set version of the pointwise statement.  This is a union, not a
sum of leaf counts: an assignment may satisfy several leaves. -/
theorem leavesFor_satisfyingAssignments (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    satisfyingAssignments F =
      (leavesFor M k hM F).toFinset.biUnion satisfyingAssignments := by
  ext a
  simp only [mem_satisfyingAssignments, Finset.mem_biUnion, List.mem_toFinset]
  exact leavesFor_eval_iff M k hM F a

theorem leavesFor_width (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ leavesFor M k hM F, WidthAtMost k G :=
  (Sparsify.treeFor M k hM F).leaf_width
    (widthAtMost_of_subset (normalize_subset F) hF)

theorem leavesFor_terminal (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    ∀ G ∈ leavesFor M k hM F, ∀ d, 2 ≤ d → d ≤ k →
      Sparsify.FreeAt G (SparsificationConstants.z M) d :=
  (Sparsify.treeFor M k hM F).leaf_terminal

theorem leavesFor_occurrence (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ leavesFor M k hM F,
      OccurrenceAtMost (SparsificationConstants.occurrenceCap M k) G := by
  intro G hG
  exact Sunflower.terminal_occurrenceAtMost G M k hM
    (leavesFor_width M k hM F hF G hG) (leavesFor_terminal M k hM F G hG)

theorem decomposition_leaves_antichain {z : ℕ → ℕ} {k : ℕ} {F : CNF (Fin n)}
    (tree : Sparsify.Decomposition z k F) (hF : SunflowerBranch.Antichain F) :
    ∀ G ∈ tree.leaves, SunflowerBranch.Antichain G := by
  induction tree with
  | leaf F ht => simpa [Sparsify.Decomposition.leaves] using hF
  | @branch F c left right ihL ihR =>
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact ihL (c.flower.childA_antichain F) G hG
      · exact ihR (c.flower.childB_antichain F) G hG

theorem leavesFor_antichain (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    ∀ G ∈ leavesFor M k hM F, SunflowerBranch.Antichain G :=
  decomposition_leaves_antichain (Sparsify.treeFor M k hM F)
    (SunflowerBranch.antichain_normalize F)

/-- The quantitative node bound for arbitrary real exponential budget.  The
two parameter inequalities are discharged by the separate arithmetic selector;
no property of an input-dependent branch path is an assumption here. -/
theorem treeFor_nodeCount_le (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : CNF (Fin n))
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) :=
  QuantitativeBranchTree.treeFor_nodeCount_le M k hM hk σ F hDim hbudget

theorem leavesFor_length_le (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : CNF (Fin n))
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((leavesFor M k hM F).length : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply le_trans ?_ (treeFor_nodeCount_le M k hM hk σ F hDim hbudget)
  exact_mod_cast (Sparsify.treeFor M k hM F).leaves_length_le_nodes

/-- A polynomial bound above index two extends to all indices after shifting
the base. The coefficient and degree are chosen before the index varies. -/
theorem polynomialBound_shift {f : ℕ → ℕ}
    (hf : SparsificationConstants.PolynomialBound f) :
    ∃ A q : ℕ, ∀ s, f s ≤ A * (s + 2) ^ q := by
  obtain ⟨a, q, h⟩ := hf
  refine ⟨a + f 0 + f 1, q, ?_⟩
  intro s
  have hp : 1 ≤ (s + 2) ^ q := Nat.one_le_pow q (s + 2) (by omega)
  by_cases hs : 2 ≤ s
  · exact (h s hs).trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_left (by omega) q))
  · have hsmall : f s ≤ a + f 0 + f 1 := by
      have he : s = 0 ∨ s = 1 := by omega
      rcases he with rfl | rfl <;> omega
    exact hsmall.trans (by simpa using Nat.mul_le_mul_left (a + f 0 + f 1) hp)

/-- The shifted base also absorbs the fixed coefficient. -/
theorem polynomialBound_shift_power {f : ℕ → ℕ}
    (hf : SparsificationConstants.PolynomialBound f) :
    ∃ q : ℕ, ∀ s, f s ≤ (s + 2) ^ q := by
  obtain ⟨A, q, h⟩ := polynomialBound_shift hf
  refine ⟨A + q, ?_⟩
  intro s
  have hA : A ≤ (s + 2) ^ A :=
    (Nat.lt_pow_self (by omega : 1 < s + 2)).le
  calc
    f s ≤ A * (s + 2) ^ q := h s
    _ ≤ (s + 2) ^ A * (s + 2) ^ q := Nat.mul_le_mul_right _ hA
    _ = (s + 2) ^ (A + q) := (pow_add _ _ _).symm

/-- Reciprocal-budget output. The same fixed program selects all parameters
from k and s before it processes the formula. -/
def chosenLeaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :
    List (CNF (Fin n)) :=
  leavesFor (SparsificationBudget.chooseM k hk s) k
    (SparsificationBudget.chooseM_ge_two k hk s) F

def chosenOccurrenceBound (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : ℕ :=
  SparsificationConstants.occurrenceCap (SparsificationBudget.chooseM k hk s) k

theorem chosenLeaves_eval_iff (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ chosenLeaves k hk s F, G.eval a = true :=
  leavesFor_eval_iff _ _ _ F a

theorem chosenLeaves_correct (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ chosenLeaves k hk s F, Satisfiable G :=
  leavesFor_correct _ _ _ F

theorem chosenLeaves_width (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ chosenLeaves k hk s F, WidthAtMost k G :=
  leavesFor_width _ _ _ F hF

theorem chosenLeaves_occurrence (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ chosenLeaves k hk s F,
      OccurrenceAtMost (chosenOccurrenceBound k hk s) G :=
  leavesFor_occurrence _ _ _ F hF

theorem chosenOccurrenceBound_power (k : ℕ) (hk : 2 ≤ k) :
    ∃ q : ℕ, ∀ s, chosenOccurrenceBound k hk s ≤ (s + 2) ^ q :=
  polynomialBound_shift_power (SparsificationBudget.chosenOccurrenceCap_polynomialBound k hk)

theorem chosenLeaves_length_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (s : ℕ) (_hs : 0 < s) {n : ℕ} (F : CNF (Fin n)),
      ((chosenLeaves k hk s F).length : ℝ) ≤
        (A : ℝ) * (s : ℝ) ^ q * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) :=
  QuantitativeBranchTree.exists_selected_leaves_polynomial k hk

/-- The exponent in the finite candidate-count bound, with every dependence
on the chosen threshold still visible. -/
def candidateExponent (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : ℕ :=
  2 * k * (SparsificationBudget.thresholdCap (SparsificationBudget.chooseM k hk s) k + 1) + k

theorem candidateExponent_polynomialBound (k : ℕ) (hk : 2 ≤ k) :
    SparsificationConstants.PolynomialBound (candidateExponent k hk) := by
  exact ((SparsificationConstants.polynomialBound_const (2 * k)).mul
    ((SparsificationBudget.chosenThresholdCap_polynomialBound k hk).add
      (SparsificationConstants.polynomialBound_const 1))).add
        (SparsificationConstants.polynomialBound_const k)

theorem chosen_candidate_count_le (k : ℕ) (hk : 2 ≤ k) (s d : ℕ) (hd : d ≤ k)
    (F : CNF (Fin n)) (hF : WidthAtMost k F) (hn : 0 < n) :
    (Sparsify.candidates F (SparsificationConstants.z
      (SparsificationBudget.chooseM k hk s)) d).length ≤
        (n + 1) ^ candidateExponent k hk s := by
  let M := SparsificationBudget.chooseM k hk s
  have hz := SparsificationBudget.z_le_thresholdCap M k d hd
  have hbase : 2 * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have htwo : 2 ≤ n + 1 := by omega
  calc
    (Sparsify.candidates F (SparsificationConstants.z M) d).length ≤
        (2 * n + 1) ^ (k * (SparsificationConstants.z M d + 1)) * 2 ^ k :=
      candidate_count_le F _ d k hF
    _ ≤ ((n + 1) ^ 2) ^ (k * (SparsificationConstants.z M d + 1)) * (n + 1) ^ k :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left htwo _)
    _ = (n + 1) ^ (2 * k * (SparsificationConstants.z M d + 1) + k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ (n + 1) ^ candidateExponent k hk s := by
      apply Nat.pow_le_pow_right (by omega)
      unfold candidateExponent
      nlinarith

theorem chosen_candidate_count_power (k : ℕ) (hk : 2 ≤ k) :
    ∃ q : ℕ, ∀ (s d : ℕ), d ≤ k → ∀ {n : ℕ} (F : CNF (Fin n)),
      WidthAtMost k F → 0 < n →
      (Sparsify.candidates F (SparsificationConstants.z
        (SparsificationBudget.chooseM k hk s)) d).length ≤ (n + 1) ^ ((s + 2) ^ q) := by
  obtain ⟨q, hq⟩ := polynomialBound_shift_power (candidateExponent_polynomialBound k hk)
  refine ⟨q, ?_⟩
  intro s d hd n F hF hn
  exact (chosen_candidate_count_le k hk s d hd F hF hn).trans
    (Nat.pow_le_pow_right (by omega) (hq s))

end SubexponentialSAT.QuantitativeSparsify

end OAI.Algorithms
