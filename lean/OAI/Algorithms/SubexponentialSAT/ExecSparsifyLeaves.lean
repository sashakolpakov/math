import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyObserved

namespace OAI.Algorithms

/-! Semantic properties of the exact ordered leaves of the observed run. -/

namespace SubexponentialSAT.ExecSparsifyObserved

open ExecCNF ExecSparsifyWorklist
open ExecSparsifyNode (Data)

variable {n k : ℕ}

noncomputable def leaves (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) : List (Formula n) :=
  (run (branching frame z hf hb hz) (initial F)).leaves

theorem leaves_ready (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ∀ G ∈ leaves frame z hf hb hz F, Ready k G :=
  initial_run_leaves_invariant _ (Ready k) (branching_closed frame z hf hb hz) F hF

/-- The emitted order itself supplies a duplicate-free list of semantic clauses. -/
theorem leaf_clause_nodup (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (G : Formula n) (hG : G ∈ leaves frame z hf hb hz F) :
    (G.map clauseSet).Nodup := (leaves_ready frame z hf hb hz F hF G hG).1

theorem leaves_models (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n)
    (a : SAT.Assignment (Fin n)) :
    SAT.CNF.eval a (formulaSet F) = true ↔
      ∃ G ∈ leaves frame z hf hb hz F, SAT.CNF.eval a (formulaSet G) = true := by
  refine initial_run_correct (branching frame z hf hb hz)
    (fun X : Formula n => SAT.CNF.eval a (formulaSet X) = true) ?_ F
  intro X A B hs
  have hX := split_some_ready frame z hf hb hz X A B hs
  obtain ⟨c, hcA, hcB⟩ := branching_choices frame z hf hb hz X hX A B hs
  change SAT.CNF.eval a (formulaSet X) = true ↔
    SAT.CNF.eval a (formulaSet A) = true ∨ SAT.CNF.eval a (formulaSet B) = true
  rw [hcA, hcB]
  exact SunflowerBranch.eval_children_iff a _ c.flower.core c.flower.petals c.present

theorem leaves_satisfiable (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) :
    SAT.Satisfiable (formulaSet F) ↔
      ∃ G ∈ leaves frame z hf hb hz F, SAT.Satisfiable (formulaSet G) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨G, hG, he⟩ := (leaves_models frame z hf hb hz F a).mp ha
    exact ⟨G, hG, a, he⟩
  · rintro ⟨G, hG, a, ha⟩
    exact ⟨a, (leaves_models frame z hf hb hz F a).mpr ⟨G, hG, ha⟩⟩

theorem leaves_terminal (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    ∀ G ∈ leaves frame z hf hb hz F,
      ∀ d, 2 ≤ d → d ≤ k → Sparsify.FreeAt (formulaSet G) z d := by
  intro G hG
  exact branching_terminal frame z hf hb hz G
    (leaves_ready frame z hf hb hz F hF G hG)
    (initial_run_leaves_terminal _ F G hG)

theorem leaf_width (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (G : Formula n) (hG : G ∈ leaves frame z hf hb hz F) :
    SAT.WidthAtMost k (formulaSet G) := by
  exact semantic_width_of_raw G k (leaves_ready frame z hf hb hz F hF G hG).2.2

/-- Each emitted leaf retains the polynomial encoding size of a normalized
width-k formula over the original variable type. -/
theorem leaf_encoding_length (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (G : Formula n) (hG : G ∈ leaves frame z hf hb hz F) :
    (encode G).length ≤ (8 * k + 5) * (n + 1) ^ (2 * k + 1) := by
  have hg := leaves_ready frame z hf hb hz F hF G hG
  have he : encode G = ExecQuantitativeSparsify.encodeRawFormula G :=
    ExecSparsifyEncoding.words_encodeRawFormula G
  rw [he]
  exact ExecQuantitativeSparsify.encodeRawFormula_polynomial G k hg.1 hg.2.2

/-- Framing the complete leaf stream is linear in the number of leaves
times the proved per-leaf bit bound. -/
theorem leaves_encoding_length (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    (Encoding.encodeList encode (leaves frame z hf hb hz F)).length ≤
      1 + (2 * ((8 * k + 5) * (n + 1) ^ (2 * k + 1)) + 2) *
        (leaves frame z hf hb hz F).length :=
  Encoding.length_encodeList_upper encode _ _
    (leaf_encoding_length frame z hf hb hz F hF)

theorem leaf_occurrence (frame : Data k) (M : ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : Ready k F) (hM : 2 ≤ M)
    (G : Formula n) (hG : G ∈ leaves frame (SparsificationConstants.z M) hf hb hz F) :
    SAT.OccurrenceAtMost (SparsificationConstants.occurrenceCap M k) (formulaSet G) :=
  Sunflower.terminal_occurrenceAtMost (formulaSet G) M k hM
    (leaf_width frame _ hf hb hz F hF G hG)
    (leaves_terminal frame _ hf hb hz F hF G hG)

theorem visits_quantitative (frame : Data k) (M : ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : Ready k F) (hanti : SunflowerBranch.Antichain (formulaSet F))
    (hM : 2 ≤ M) (hk : 0 < k) (σ : ℝ)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((run (branching frame (SparsificationConstants.z M) hf hb hz) (initial F)).visits : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) :=
  SparsifyIntegrity.initial_run_visits_quantitative_on _ formulaSet (Ready k)
    (branching_closed frame _ hf hb hz) (branching_choices frame _ hf hb hz)
    (branching_terminal frame _ hf hb hz) F hF hanti hM hk σ hDim hbudget

end SubexponentialSAT.ExecSparsifyObserved

end OAI.Algorithms
