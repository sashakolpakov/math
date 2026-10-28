import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify

namespace OAI.Algorithms

/-!
# Original-ambient sparsification for the square-root-logarithmic algorithm

The executable splitter is reused without changing its search rule.  Its
reciprocal budget is a free natural parameter, so the new asymptotic schedule
can be supplied independently.  These are output and worklist-visit bounds;
primitive instruction costs must also charge the search inside every visit.

The leaves form an OR-cover, not a disjoint partition.  In particular, this
module does not sum the numbers of satisfying assignments of different leaves.
-/

namespace SubexponentialSAT.SqrtLog.Sparsify

open SAT

variable {n : ℕ}

abbrev leaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :=
  ExecQuantitativeSparsify.chosenLeaves k hk s F

abbrev occurrenceBound (k : ℕ) (hk : 2 ≤ k) (s : ℕ) :=
  QuantitativeSparsify.chosenOccurrenceBound k hk s

theorem leaves_eval_iff (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ leaves k hk s F, G.eval a = true :=
  ExecQuantitativeSparsify.chosenLeaves_eval_iff k hk s F a

theorem leaves_sat_iff (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ leaves k hk s F, Satisfiable G :=
  ExecQuantitativeSparsify.chosenLeaves_correct k hk s F

theorem leaves_spec (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) (hF : WidthAtMost k F) :
    ∀ G ∈ leaves k hk s F,
      WidthAtMost k G ∧ OccurrenceAtMost (occurrenceBound k hk s) G := by
  intro G hG
  exact ⟨ExecQuantitativeSparsify.chosenLeaves_width k hk s F hF G hG,
    ExecQuantitativeSparsify.chosenLeaves_occurrence k hk s F hF G hG⟩

/-- Constants precede the reciprocal budget, ambient size, and input.
The three fixed exponents need not coincide. -/
theorem polynomial_parameters (k : ℕ) (hk : 2 ≤ k) :
    ∃ A qB qV qC : ℕ,
      (∀ s, occurrenceBound k hk s ≤ (s + 2) ^ qB) ∧
      (∀ (s : ℕ), 0 < s → ∀ {n : ℕ}
        (F : ExecQuantitativeSparsify.Formula n),
        ((ExecQuantitativeSparsify.chosenExecute k hk s F).visits : ℝ) ≤
          (A : ℝ) * ((s : ℝ) + 2) ^ qV * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ ((n : ℝ) / s)) ∧
      (∀ (s d : ℕ), d ≤ k → ∀ {n : ℕ} (F : CNF (Fin n)),
        WidthAtMost k F → 0 < n →
        (SubexponentialSAT.Sparsify.candidates F
          (SparsificationConstants.z (SparsificationBudget.chooseM k hk s)) d).length ≤
            (n + 1) ^ ((s + 2) ^ qC)) := by
  obtain ⟨qB, hB⟩ := QuantitativeSparsify.chosenOccurrenceBound_power k hk
  obtain ⟨A, qV, hV⟩ := ExecQuantitativeSparsify.chosenExecute_visits_polynomial k hk
  obtain ⟨qC, hC⟩ := QuantitativeSparsify.chosen_candidate_count_power k hk
  exact ⟨A, qB, qV, qC, hB, hV, hC⟩

theorem leaf_count_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (s : ℕ), 0 < s → ∀ {n : ℕ} (F : CNF (Fin n)),
      ((leaves k hk s F).length : ℝ) ≤
        (A : ℝ) * ((s : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / s) :=
  ExecQuantitativeSparsify.chosenLeaves_length_polynomial k hk

/-- An empty clause makes a leaf unusable; deleting that leaf is SAT-safe. -/
theorem empty_clause_not_mem_of_sat (G : CNF (Fin n)) (hG : Satisfiable G) :
    (∅ : Clause (Fin n)) ∉ G := by
  obtain ⟨a, ha⟩ := hG
  intro hempty
  have h := (CNF.eval_eq_true a G).mp ha ∅ hempty
  simp at h

/-- The extra `1` often used for empty clauses is unnecessary once a leaf
containing an empty clause is rejected. Unused ambient variables are retained. -/
theorem clause_count_le_of_occurrence (G : CNF (Fin n)) (B : ℕ)
    (hB : OccurrenceAtMost B G) (hempty : (∅ : Clause (Fin n)) ∉ G) :
    G.card ≤ n * B := by
  let occ := fun v : Fin n => G.filter (fun C => ∃ l ∈ C, l.variable = v)
  have hcover : G ⊆ Finset.univ.biUnion occ := by
    intro C hC
    have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      exact hempty (he ▸ hC))
    obtain ⟨l, hl⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨l.variable, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hC, l, hl, rfl⟩⟩
  calc
    G.card ≤ (Finset.univ.biUnion occ).card := Finset.card_le_card hcover
    _ ≤ ∑ v : Fin n, (occ v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, B := Finset.sum_le_sum (fun v _ => hB v)
    _ = n * B := by simp

def liveLeaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :
    List (CNF (Fin n)) :=
  (leaves k hk s F).filter (fun G => decide ((∅ : Clause (Fin n)) ∉ G))

theorem mem_liveLeaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F G : CNF (Fin n)) :
    G ∈ liveLeaves k hk s F ↔
      G ∈ leaves k hk s F ∧ (∅ : Clause (Fin n)) ∉ G := by
  simp [liveLeaves]

theorem liveLeaves_sat_iff (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ liveLeaves k hk s F, Satisfiable G := by
  rw [leaves_sat_iff k hk s F]
  constructor
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, (mem_liveLeaves k hk s F G).mpr
      ⟨hG, empty_clause_not_mem_of_sat G hsat⟩, hsat⟩
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, ((mem_liveLeaves k hk s F G).mp hG).1, hsat⟩

theorem liveLeaves_spec (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) (hF : WidthAtMost k F) :
    ∀ G ∈ liveLeaves k hk s F,
      WidthAtMost k G ∧ OccurrenceAtMost (occurrenceBound k hk s) G ∧
        G.card ≤ n * occurrenceBound k hk s := by
  intro G hG
  obtain ⟨hleaf, hempty⟩ := (mem_liveLeaves k hk s F G).mp hG
  obtain ⟨hw, hb⟩ := leaves_spec k hk s F hF G hleaf
  exact ⟨hw, hb, clause_count_le_of_occurrence G _ hb hempty⟩

theorem liveLeaves_length_le (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (F : CNF (Fin n)) :
    (liveLeaves k hk s F).length ≤ (leaves k hk s F).length :=
  List.length_filter_le _ _

/-- A Boolean leaf solver is combined only by disjunction. Its proof premise
is restricted to the actual bounded-occurrence leaves on the original `Fin n`. -/
def decideByLeaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (decideLeaf : CNF (Fin n) → Bool) (F : CNF (Fin n)) : Bool :=
  (liveLeaves k hk s F).any decideLeaf

theorem decideByLeaves_correct (k : ℕ) (hk : 2 ≤ k) (s : ℕ)
    (decideLeaf : CNF (Fin n) → Bool) (F : CNF (Fin n))
    (hdecide : ∀ G ∈ liveLeaves k hk s F,
      decideLeaf G = true ↔ Satisfiable G) :
    decideByLeaves k hk s decideLeaf F = true ↔ Satisfiable F := by
  rw [liveLeaves_sat_iff k hk s F]
  simp only [decideByLeaves, List.any_eq_true]
  constructor
  · rintro ⟨G, hG, hyes⟩
    exact ⟨G, hG, (hdecide G hG).mp hyes⟩
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, hG, (hdecide G hG).mpr hsat⟩

end SubexponentialSAT.SqrtLog.Sparsify

end OAI.Algorithms
