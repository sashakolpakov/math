import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerSearch
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyWorklist
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget

namespace OAI.Algorithms

/-!
# Integrity guards for quantitative sparsification

The rational-budget examples explain why an executable threshold search must
not charge denominator-sized exponentiation merely as a polynomial in the
inverse numerical budget. The list examples isolate the duplicate-removal
obligation before clause counts can be used as sunflower sizes.
-/

namespace SubexponentialSAT.SparsifyIntegrity

/-- Reduced rational budgets can approach one while their representation
denominators grow without bound. -/
def nearOne (N : ℕ) : ℚ := ((N : ℚ) + 1) / ((N : ℚ) + 2)

theorem nearOne_pos (N : ℕ) : 0 < nearOne N := by
  unfold nearOne
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  exact div_pos (by linarith) (by linarith)

theorem nearOne_lt_one (N : ℕ) : nearOne N < 1 := by
  unfold nearOne
  apply (div_lt_iff₀ (by positivity : (0 : ℚ) < (N : ℚ) + 2)).mpr
  linarith

theorem half_le_nearOne (N : ℕ) : (1 / 2 : ℚ) ≤ nearOne N := by
  unfold nearOne
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < (N : ℚ) + 2)).mpr
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  linarith

theorem inverse_nearOne_le_two (N : ℕ) : 1 / nearOne N ≤ 2 := by
  apply (div_le_iff₀ (nearOne_pos N)).mpr
  have h := half_le_nearOne N
  linarith

theorem consecutive_coprime (N : ℕ) : Nat.Coprime (N + 1) (N + 2) := by
  rw [show N + 2 = (N + 1) + 1 by omega]
  simp

theorem nearOne_den (N : ℕ) : (nearOne N).den = N + 2 := by
  have h := Rat.den_div_eq_of_coprime
    (a := ((N + 1 : ℕ) : ℤ)) (b := ((N + 2 : ℕ) : ℤ))
    (by omega) (by
      rw [show (↑(N + 1) : ℤ).natAbs = N + 1 by omega,
        show (↑(N + 2) : ℤ).natAbs = N + 2 by omega]
      exact consecutive_coprime N)
  have h' : ((nearOne N).den : ℤ) = (N + 2 : ℕ) := by
    simpa [nearOne] using h
  exact_mod_cast h'

theorem nearOne_num (N : ℕ) : (nearOne N).num = (N + 1 : ℕ) := by
  have h := Rat.num_div_eq_of_coprime
    (a := ((N + 1 : ℕ) : ℤ)) (b := ((N + 2 : ℕ) : ℤ))
    (by omega) (by
      rw [show (↑(N + 1) : ℤ).natAbs = N + 1 by omega,
        show (↑(N + 2) : ℤ).natAbs = N + 2 by omega]
      exact consecutive_coprime N)
  simpa [nearOne] using h

/-- The numerical inverse budget does not bound its reduced denominator. -/
theorem bounded_inverse_unbounded_denominator (B : ℕ) :
    ∃ sigma : ℚ, 0 < sigma ∧ sigma ≤ 1 ∧ 1 / sigma ≤ 2 ∧ B < sigma.den := by
  refine ⟨nearOne B, nearOne_pos B, (nearOne_lt_one B).le,
    inverse_nearOne_le_two B, ?_⟩
  rw [nearOne_den]
  omega

/-- Materializing the power occurring after clearing a rational budget's
denominator really creates this many binary digits. This is a size assertion,
not a claim that an unimplemented arithmetic operation has constant cost. -/
theorem cleared_rhs_binary_size (M N : ℕ) :
    Nat.size (2 ^ (M * (N + 1))) = M * (N + 1) + 1 :=
  Nat.size_pow

/-- A constant inverse numerical budget still permits arbitrarily large
materialized right-hand powers in the naive exact comparison. -/
theorem bounded_inverse_unbounded_cleared_power (B : ℕ) :
    ∃ N : ℕ, 1 / nearOne N ≤ 2 ∧ B < Nat.size (2 ^ (2 * (N + 1))) := by
  refine ⟨B, inverse_nearOne_le_two B, ?_⟩
  rw [cleared_rhs_binary_size]
  omega

/-- The implemented reciprocal rounding collapses this entire hostile family
to index two, so its doubling search never uses the huge original denominator
as an exponent. Computing the rounding still has its input-bit cost. -/
theorem nearOne_reciprocalIndex (N : ℕ) :
    SparsificationBudget.reciprocalIndex (nearOne N).num.natAbs (nearOne N).den = 2 := by
  rw [nearOne_num, nearOne_den]
  simp only [Int.natAbs_natCast, SparsificationBudget.reciprocalIndex]
  rw [show N + 2 - 1 = N + 1 by omega, Nat.div_self (by omega)]
  rfl

theorem nearOne_uses_fixed_search (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    SparsificationBudget.chooseForSigma k hk (nearOne N) =
      SparsificationBudget.chooseM k hk 2 := by
  simp only [SparsificationBudget.chooseForSigma, SparsificationBudget.chooseRationalM,
    nearOne_reciprocalIndex]

/-- Two list entries need not represent two different clauses. -/
theorem duplicate_list_card_guard {α : Type*} [DecidableEq α] (clause : α) :
    ([clause, clause] : List α).length = 2 ∧
      ([clause, clause] : List α).toFinset.card = 1 := by
  simp

/-- Exact transfer of list length to set cardinality requires the no-duplicate
invariant. This is the appropriate guard at a list-to-set sunflower interface. -/
theorem distinct_count_transfer {α : Type*} [DecidableEq α]
    (clauses : List α) (h : clauses.Nodup) :
    clauses.toFinset.card = clauses.length :=
  List.toFinset_card_of_nodup h

/-- The actual executable literal deduplication discharges that invariant. -/
theorem deduplicated_literal_count {α : Type*} [DecidableEq α]
    (clause : ExecCNF.Clause α) :
    (ExecCNF.dedupLiterals clause).length = (ExecCNF.clauseSet clause).card := by
  have h : (ExecCNF.clauseSet (ExecCNF.dedupLiterals clause)).card =
      (ExecCNF.dedupLiterals clause).length :=
    List.toFinset_card_of_nodup (ExecCNF.dedupLiterals_nodup clause)
  rw [ExecCNF.clauseSet_dedupLiterals] at h
  exact h.symm

/-- Clause deduplication uses equality of represented sets, not equality of
literal-list order. Its output length is exactly the semantic clause count. -/
theorem deduplicated_clause_count {α : Type*} [DecidableEq α]
    (formula : ExecCNF.Formula α) :
    (ExecCNF.dedupClauses formula).length = (ExecCNF.formulaSet formula).card := by
  have h : (ExecCNF.formulaSet (ExecCNF.dedupClauses formula)).card =
      (ExecCNF.dedupClauses formula).length := by
    simpa [ExecCNF.formulaSet] using
      List.toFinset_card_of_nodup (ExecCNF.dedupClauses_map_nodup formula)
  rw [ExecCNF.formulaSet_dedupClauses] at h
  exact h.symm

/-- Concrete regression: reordered and internally duplicated copies of one
clause contribute only one distinct clause. -/
theorem permuted_duplicate_clauses :
    (ExecCNF.dedupClauses ([[0, 1], [1, 0], [0, 0, 1]] : List (List ℕ))).length = 1 := by
  decide

/-- Repeating one selected clause cannot pass the executable sunflower
checker as a family of two or more distinct clauses. -/
theorem duplicate_selected_rejected {α : Type*} [DecidableEq α]
    (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) (hz : 2 ≤ z d)
    (C H : ExecCNF.Clause α) :
    ExecSunflowerSearch.check F z d ([C, C], H) = false := by
  cases h : ExecSunflowerSearch.check F z d ([C, C], H) with
  | false => rfl
  | true =>
      have hc := ((ExecSunflowerSearch.check_true_iff F z d ([C, C], H)).mp h).2.1
      have hcard : 1 = z d := by simpa [ExecCNF.formulaSet] using hc
      omega

/-- Semantic width one does not bound the cost of generating sublists of an
unnormalized literal list: repetitions still produce exponentially many list
entries. Literal deduplication is needed before using a 2^k bound. -/
theorem repeated_literals_sublist_guard {α : Type*} [DecidableEq α]
    (literal : α) (N : ℕ) :
    (ExecCNF.clauseSet (List.replicate (N + 1) literal)).card = 1 ∧
      ((List.replicate (N + 1) literal).sublists).length = 2 ^ (N + 1) := by
  have h : (List.replicate (N + 1) literal).toFinset = {literal} := by
    ext x
    simp
  simp [ExecCNF.clauseSet, h]

/-- Requesting too many elements returns no candidates but still traverses
the complete include/exclude recursion. The explicit generator counts this
work; an output-length-only estimate would miss it. -/
theorem oversized_selection_calls {α : Type*} (xs : List α) (r : ℕ)
    (hr : xs.length < r) :
    (ExecSunflowerSearch.enumerateFixed r xs).calls + 1 = 2 ^ (xs.length + 1) := by
  induction xs generalizing r with
  | nil =>
      cases r with
      | zero => simp at hr
      | succ r => rfl
  | cons x xs ih =>
      cases r with
      | zero => simp at hr
      | succ r =>
          have hsmall : xs.length < r := by simpa using hr
          have hleft := ih (r + 1) (by omega)
          have hright := ih r hsmall
          simp only [ExecSunflowerSearch.enumerateFixed, List.length_cons]
          rw [pow_succ (2 : ℕ) (xs.length + 1)]
          omega

theorem empty_generation_has_work {α : Type*} (xs : List α) :
    (ExecSunflowerSearch.enumerateFixed (xs.length + 1) xs).values = [] ∧
      (ExecSunflowerSearch.enumerateFixed (xs.length + 1) xs).calls + 1 =
        2 ^ (xs.length + 1) := by
  refine ⟨?_, oversized_selection_calls xs (xs.length + 1) (by omega)⟩
  rw [ExecSunflowerSearch.enumerateFixed_values]
  exact List.sublistsLen_of_length_lt (by omega)

/-- The measured equality event is not a bit-machine cost: even comparing
arbitrarily long whole words is one equality event at this generic interface.
The Boolean-stack comparator must supply the missing bit-level refinement. -/
theorem measured_whole_word_equality (N : ℕ) :
    (ExecClauseCost.containsM (List.replicate N true) [List.replicate N true]).2 = 2 ∧
      (List.replicate N true).length = N := by
  simp [ExecClauseCost.containsM]

/-- Scanning k-1 widths beginning at two includes width k and proves every
smaller relevant width failed. This guards the minimum-width premise used by
the cumulative-insertion proof. -/
theorem minimum_width_scan {α : Type*} (find : ℕ → Option α × ℕ)
    (k : ℕ) {d : ℕ} {witness : α}
    (h : (ExecSunflowerSearch.scanWidths find 2 (k - 1)).1 = some (d, witness)) :
    2 ≤ d ∧ d ≤ k ∧ (find d).1 = some witness ∧
      ∀ j, 2 ≤ j → j < d → (find j).1 = none := by
  obtain ⟨hd, hdk, hfind, hmin⟩ := ExecSunflowerSearch.scanWidths_some find 2 (k - 1) h
  exact ⟨hd, by omega, hfind, hmin⟩

theorem terminal_width_scan {α : Type*} (find : ℕ → Option α × ℕ)
    (k : ℕ) (hk : 2 ≤ k) :
    (ExecSunflowerSearch.scanWidths find 2 (k - 1)).1 = none ↔
      ∀ d, 2 ≤ d → d ≤ k → (find d).1 = none := by
  rw [ExecSunflowerSearch.scanWidths_none_iff]
  constructor
  · intro h d hd hdk
    exact h d hd (by omega)
  · intro h d hd hdk
    exact h d hd (by omega)

/-- The reported counter sums only callback reports. Even arbitrarily many
failed width iterations can report zero; the counter is not a bit-step cost. -/
theorem zero_callback_reports (start fuel : ℕ) :
    (ExecSunflowerSearch.scanWidths (fun _ => ((none, 0) : Option Unit × ℕ))
      start fuel).2 = 0 := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih => simpa [ExecSunflowerSearch.scanWidths] using ih (start + 1)

section WorklistGuards

variable {n : ℕ}

/-- The actual post-branch literal cleanup preserves the entire list of
represented clause sets, including its order and multiplicities. -/
theorem cleanup_clause_sets (F : ExecSparsifyWorklist.Formula n) :
    (ExecSparsifyWorklist.cleanLiterals F).map ExecCNF.clauseSet =
      F.map ExecCNF.clauseSet := by
  simp [ExecSparsifyWorklist.cleanLiterals, List.map_map, Function.comp_def]

/-- Clause multiplicity is controlled in both executable children, before
using a finite-set bound to estimate the actual list length. -/
theorem children_distinct_clause_sets (F : ExecSparsifyWorklist.Formula n)
    (c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))) :
    ((ExecSparsifyWorklist.children F c).1.map ExecCNF.clauseSet).Nodup ∧
      ((ExecSparsifyWorklist.children F c).2.map ExecCNF.clauseSet).Nodup := by
  simp only [ExecSparsifyWorklist.children, cleanup_clause_sets]
  exact ⟨ExecCNF.absorb_map_nodup _, ExecCNF.absorb_map_nodup _⟩

theorem initial_distinct_clause_sets (F : ExecSparsifyWorklist.Formula n) :
    ((ExecSparsifyWorklist.normalizedInput F).map ExecCNF.clauseSet).Nodup := by
  rw [ExecSparsifyWorklist.normalizedInput, cleanup_clause_sets]
  exact ExecCNF.normalize_map_nodup _ _

theorem distinct_clause_sets_closed (z : ℕ → ℕ) (k : ℕ) :
    ExecSparsifyWorklist.SplitClosed
      (ExecSparsifyWorklist.splitFormula (n := n) z k)
      (fun F => (F.map ExecCNF.clauseSet).Nodup) := by
  intro F A B _ hsplit
  obtain ⟨d, c, _, rfl, rfl⟩ :=
    ExecSparsifyWorklist.splitFormula_some z k F A B hsplit
  exact children_distinct_clause_sets F c

/-- Every intermediate worklist state has extensionally distinct clause
lists, not merely the final leaves. No bound on the input multiplicity is
assumed: the actual input normalization establishes the invariant. -/
theorem intermediate_distinct_clause_sets (z : ℕ → ℕ) (k fuel : ℕ)
    (F : ExecSparsifyWorklist.Formula n) :
    ExecSparsifyWorklist.Invariant (fun G => (G.map ExecCNF.clauseSet).Nodup)
      (ExecSparsifyWorklist.runFuel (ExecSparsifyWorklist.splitFormula z k) fuel
        (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F))) := by
  apply ExecSparsifyWorklist.runFuel_invariant _ _ (distinct_clause_sets_closed z k)
  simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using
    initial_distinct_clause_sets F

theorem initial_raw_width (F : ExecSparsifyWorklist.Formula n) (k : ℕ)
    (hF : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ExecSunflowerSearch.RawWidthAtMost k (ExecSparsifyWorklist.normalizedInput F) := by
  apply ExecSparsifyWorklist.cleanLiterals_raw_width
  rw [ExecCNF.normalize_set]
  exact SAT.widthAtMost_of_subset (SAT.normalize_subset _) hF

/-- The raw-list width needed by the explicit core generator holds at every
intermediate state, even when the input initially repeats literals. -/
theorem intermediate_raw_width (z : ℕ → ℕ) (k fuel : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : ExecSparsifyWorklist.Formula n)
    (hF : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ExecSparsifyWorklist.Invariant (ExecSunflowerSearch.RawWidthAtMost k)
      (ExecSparsifyWorklist.runFuel (ExecSparsifyWorklist.splitFormula z k) fuel
        (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F))) := by
  apply ExecSparsifyWorklist.runFuel_invariant _ _
    (ExecSparsifyWorklist.executable_raw_width_closed z k hz)
  simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using
    initial_raw_width F k hF

theorem actual_list_length_eq_semantic_card (F : ExecSparsifyWorklist.Formula n)
    (hF : (F.map ExecCNF.clauseSet).Nodup) :
    F.length = (ExecCNF.formulaSet F).card := by
  simpa [ExecCNF.formulaSet] using (List.toFinset_card_of_nodup hF).symm

theorem execute_leaf_length_eq_semantic_card (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : ExecSparsifyWorklist.Formula n) :
    ∀ G ∈ (ExecSparsifyWorklist.execute z k hz F).leaves,
      G.length = (ExecCNF.formulaSet G).card := by
  intro G hG
  apply actual_list_length_eq_semantic_card
  exact ExecSparsifyWorklist.initial_run_leaves_invariant
    (ExecSparsifyWorklist.executableBranching z k hz)
    (fun G => (G.map ExecCNF.clauseSet).Nodup)
    (distinct_clause_sets_closed z k) _ (initial_distinct_clause_sets F) G hG

end WorklistGuards

section RecordLocalityGuards

/-- The encoding of a prepended record adds only that record's frame. A stack
implementation can leave the previously accumulated tail untouched. This is
an exact representation identity, not a claim about an unspecified copier. -/
theorem encoded_prepend_local {α : Type*} (encode : α → List Bool)
    (x : α) (xs : List α) :
    ∃ segment : List Bool,
      Encoding.encodeList encode (x :: xs) = segment ++ Encoding.encodeList encode xs ∧
      segment.length = 2 * (encode x).length + 2 := by
  refine ⟨true :: Encoding.frame (encode x), rfl, ?_⟩
  simp [Encoding.length_frame]

/-- Total prefix length copied by a strategy that rebuilds the whole output
after every insertion, even when each stored record has only one unit. -/
def copiedPrefixes : ℕ → ℕ
  | 0 => 0
  | n + 1 => copiedPrefixes n + (n + 1)

theorem copiedPrefixes_quadratic (n : ℕ) :
    2 * copiedPrefixes n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [copiedPrefixes]
      nlinarith

/-- Recopying all previous leaves cannot be absorbed into a fixed constant
overhead per visit. -/
theorem copiedPrefixes_not_linear (C : ℕ) :
    ∃ n : ℕ, C * n < copiedPrefixes n := by
  refine ⟨2 * C + 1, ?_⟩
  have h := copiedPrefixes_quadratic (2 * C + 1)
  nlinarith

/-- For exponentially many leaves, full-prefix copying squares the main
exponential factor. Local operations preserve the stated per-node bound. -/
theorem copiedPrefixes_exponential_square (e : ℕ) :
    2 ^ (2 * e) ≤ 2 * copiedPrefixes (2 ^ e) := by
  rw [copiedPrefixes_quadratic]
  have hpow : (2 : ℕ) ^ (2 * e) = (2 ^ e) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow, pow_two]
  exact Nat.mul_le_mul_left _ (Nat.le_succ _)

end RecordLocalityGuards

section InvariantTree

open ExecSparsifyWorklist

variable {α : Type*}

/-- Choice correctness is needed only on the maintained node invariant. -/
def RefinesChoicesOn {n : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ) (P : α → Prop) : Prop :=
  ∀ x, P x → ∀ a b, branch.split x = some (a, b) →
    ∃ c : Sparsify.Choice (sem x) z k, sem a = c.child false ∧ sem b = c.child true

/-- Terminality is needed only on the maintained node invariant. -/
def RefinesTerminalOn {n : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ) (P : α → Prop) : Prop :=
  ∀ x, P x → branch.split x = none →
    ∀ d, 2 ≤ d → d ≤ k → Sparsify.FreeAt (sem x) z d

/-- The actual branch tree is a sunflower decomposition when local choices
and failed searches are correct on a preserved invariant. No assertion is
made about the splitter's behavior outside that invariant. -/
theorem tree_is_decomposition_on {n k : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n)) (z : ℕ → ℕ) (P : α → Prop)
    (hclosed : SplitClosed branch.split P)
    (hchoice : RefinesChoicesOn branch sem z k P)
    (hterminal : RefinesTerminalOn branch sem z k P)
    (x : α) (hx : P x) :
    ∃ t : Sparsify.Decomposition z k (sem x), t.shape = tree branch x := by
  induction x using (measure branch.mass).wf.induction with
  | h x ih =>
    cases hs : branch.split x with
    | none =>
      refine ⟨.leaf (sem x) (hterminal x hx hs), ?_⟩
      rw [tree_none branch x hs]
      rfl
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hdec := branch.decreases x a b hs
      have hp := hclosed x a b hx hs
      obtain ⟨ta, hta⟩ := ih a hdec.1 hp.1
      obtain ⟨tb, htb⟩ := ih b hdec.2 hp.2
      obtain ⟨c, ha, hb⟩ := hchoice x hx a b hs
      refine ⟨.branch c (ha ▸ ta) (hb ▸ tb), ?_⟩
      simp only [Sparsify.Decomposition.shape, decomposition_shape_cast, hta, htb,
        tree_some branch x a b hs]

/-- Quantitative charging for the actual visit count needs local refinement
only on the invariant, plus the initial antichain and numeric budget. -/
theorem initial_run_visits_quantitative_on {n k M : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n)) (P : α → Prop)
    (hclosed : SplitClosed branch.split P)
    (hchoice : RefinesChoicesOn branch sem (SparsificationConstants.z M) k P)
    (hterminal : RefinesTerminalOn branch sem (SparsificationConstants.z M) k P)
    (x : α) (hx : P x) (hanti : SunflowerBranch.Antichain (sem x))
    (hM : 2 ≤ M) (hk : 0 < k) (σ : ℝ)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((run branch (initial x)).visits : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  obtain ⟨t, ht⟩ := tree_is_decomposition_on branch sem (SparsificationConstants.z M)
    P hclosed hchoice hterminal x hx
  rw [initial_run_visits, ← ht]
  exact QuantitativeBranchTree.decomposition_nodeCount_le t hM hk σ hanti hDim hbudget

end InvariantTree

/-- A deterministic transition function has only one halting trace from a
given input, both in its exact number of successful steps and final state. -/
theorem terminal_trace_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m ∧ b = c := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => exact ⟨rfl, rfl⟩
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have he : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          obtain ⟨hn, hbc⟩ := ih ht' hb hc
          exact ⟨congrArg Nat.succ hn, hbc⟩

theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m :=
  (terminal_trace_unique h₁ h₂ hb hc).1

/-- Transfer a proved runtime bound to any observed halting trace of the
same program from the same input, retaining equality of the final state. -/
theorem terminal_trace_le_of_runsIn {α : Type*} {step : α → Option α}
    {n bound : ℕ} {a b c : α} (h : Computation.Trace step n a b)
    (hbound : Computation.RunsIn step bound a c)
    (hb : step b = none) (hc : step c = none) : n ≤ bound ∧ b = c := by
  obtain ⟨m, hm, ht⟩ := hbound
  obtain ⟨he, hbc⟩ := terminal_trace_unique h ht hb hc
  exact ⟨he.le.trans hm, hbc⟩

end SubexponentialSAT.SparsifyIntegrity

end OAI.Algorithms
