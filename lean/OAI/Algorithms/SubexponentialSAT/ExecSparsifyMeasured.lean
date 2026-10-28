import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyWorklist
import OAI.Algorithms.SubexponentialSAT.QuantitativeSparsify

namespace OAI.Algorithms

/-!
# Concrete measured sparsification execution

The input normalization, candidate search, child construction, and worklist are
composed from their actual measured procedures. The resulting count is a count
of their specified list/comparison events, not a primitive bit-machine bound.
The finite threshold table is a supplied parameter; computing that table is a
separate implementation cost.
-/

namespace SubexponentialSAT.ExecSparsifyWorklist

section ConcreteMeasuredExecution

variable {n : ℕ}
open ExecClauseCost ExecSunflowerSearch

/-- Build petals once, then run both measured children and literal cleanups. -/
def childrenM (F : Formula n) (c : Candidate (SAT.Literal (Fin n))) :
    (Formula n × Formula n) × ℕ :=
  let petals := petalsM c
  let left := childA_M F c.2 petals.1
  let right := childB_M F c.2 petals.1
  let cleanLeft := cleanLiteralsM left.1
  let cleanRight := cleanLiteralsM right.1
  ((cleanLeft.1, cleanRight.1),
    petals.2 + left.2 + right.2 + cleanLeft.2 + cleanRight.2 + 1)

@[simp] theorem childrenM_value (F : Formula n) (c : Candidate (SAT.Literal (Fin n))) :
    (childrenM F c).1 = children F c := by
  simp [childrenM, children, cleanLiterals]

def childrenBudget (m k : ℕ) : ℕ :=
  petalsBudget m k + 2 * childBudget m m k +
    2 * ((2*m+1) * ((k+1)^2+1) + 1) + 1

theorem childrenM_cost_le (F : Formula n) (c : Candidate (SAT.Literal (Fin n)))
    (k : ℕ) (hF : RawWidthAtMost k F) (hG : RawWidthAtMost k c.1)
    (hH : c.2.length ≤ k) (hm : c.1.length ≤ F.length) :
    (childrenM F c).2 ≤ childrenBudget F.length k := by
  have hp : RawWidthAtMost k (petals c) := petals_width c k hG
  have hpc := petalsM_cost_le c k hG hH
  have hpc' : (petalsM c).2 ≤ petalsBudget F.length k := by
    apply hpc.trans
    unfold petalsBudget
    gcongr
  have hl := childA_M_cost_le F c.2 (petals c) k hF hH hp
  have hr := childB_M_cost_le F c.2 (petals c) k hF hH hp
  have hbudget : childBudget F.length (petals c).length k ≤ childBudget F.length F.length k := by
    rw [petals_length]
    unfold childBudget
    gcongr
  have hl' := hl.trans hbudget
  have hr' := hr.trans hbudget
  have hcl := cleanLiteralsM_cost_le (ExecCNF.childA F c.2 (petals c)) k
    (childA_raw_width F c.2 (petals c) k hF hH)
  have hcr := cleanLiteralsM_cost_le (ExecCNF.childB F c.2 (petals c)) k
    (childB_raw_width F c.2 (petals c) k hF hp)
  have hll : (ExecCNF.childA F c.2 (petals c)).length ≤ 2*F.length+1 := by
    have := ExecCNF.childA_length_le F c.2 (petals c)
    omega
  have hrl : (ExecCNF.childB F c.2 (petals c)).length ≤ 2*F.length+1 := by
    have := ExecCNF.childB_length_le F c.2 (petals c)
    rw [petals_length] at this
    omega
  have hcl' : (cleanLiteralsM (ExecCNF.childA F c.2 (petals c))).2 ≤
      (2*F.length+1)*((k+1)^2+1)+1 := by
    apply hcl.trans
    gcongr
  have hcr' : (cleanLiteralsM (ExecCNF.childB F c.2 (petals c))).2 ≤
      (2*F.length+1)*((k+1)^2+1)+1 := by
    apply hcr.trans
    gcongr
  simp only [childrenM, petalsM_value, childA_M_value, childB_M_value]
  unfold childrenBudget
  omega

/-- Complete measured node processing; search and rebuilding are expanded into
actual recursive measured procedures, rather than charged as unit callbacks. -/
def splitFormulaM (z : ℕ → ℕ) (k : ℕ) (F : Formula n) :
    Option (Formula n × Formula n) × ℕ :=
  let selected := selectM F z k
  match selected.1 with
  | none => (none, selected.2 + 1)
  | some (_, c) =>
      let built := childrenM F c
      (some built.1, selected.2 + built.2 + 2)

@[simp] theorem splitFormulaM_value (z : ℕ → ℕ) (k : ℕ) (F : Formula n) :
    (splitFormulaM z k F).1 = splitFormula z k F := by
  cases hs : (select F z k).1 <;> simp [splitFormulaM, splitFormula, hs]

def nodeBudget (m k Z : ℕ) : ℕ := selectionBudget m k Z + childrenBudget m k + 2

theorem splitFormulaM_cost_le (z : ℕ → ℕ) (k Z : ℕ) (F : Formula n)
    (hF : RawWidthAtMost k F) (hZ : ∀ d, 2 ≤ d → d ≤ k → z d ≤ Z) :
    (splitFormulaM z k F).2 ≤ nodeBudget F.length k Z := by
  have hs := selectM_cost_le F z k Z hF hZ
  cases hsel : (select F z k).1 with
  | none =>
    simp only [splitFormulaM, selectM_value, hsel]
    unfold nodeBudget
    omega
  | some pair =>
    rcases pair with ⟨d,c⟩
    obtain ⟨hG,hH,hm⟩ := selected_candidate_bounds F z k hF hsel
    have hc := childrenM_cost_le F c k hF hG hH hm
    simp only [splitFormulaM, selectM_value, hsel]
    unfold nodeBudget
    omega

theorem nodeBudget_mono (k Z : ℕ) {m m' : ℕ} (h : m ≤ m') :
    nodeBudget m k Z ≤ nodeBudget m' k Z := by
  unfold nodeBudget selectionBudget searchBudget dedupBudget childrenBudget petalsBudget childBudget
  simp only [checkerBudget_expansion]
  unfold generationBudget
  gcongr

/-- Measured input normalization, including the final cleanup in `normalizedInput`. -/
def normalizedInputM (F : Formula n) : Formula n × ℕ :=
  let normalized := normalizeLiteralM F
  let clean := cleanLiteralsM normalized.1
  (clean.1, normalized.2 + clean.2 + 1)

@[simp] theorem normalizedInputM_value (F : Formula n) :
    (normalizedInputM F).1 = normalizedInput F := by
  simp [normalizedInputM, normalizedInput, cleanLiterals]

def initializationBudget (m k : ℕ) : ℕ :=
  normalizationBudget m k + m*((k+1)^2+1) + 2

theorem normalizedInputM_cost_le (F : Formula n) (k : ℕ) (hF : RawWidthAtMost k F) :
    (normalizedInputM F).2 ≤ initializationBudget F.length k := by
  have hn := normalizeLiteralM_cost_le F k hF
  have hw : RawWidthAtMost k (ExecCNF.normalize SAT.Literal.negate F) := by
    intro C hC
    have h1 := ExecCNF.absorb_subset _ hC
    have h2 := (List.mem_filter.mp h1).1
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp h2
    exact (ExecCNF.dedupLiterals_length_le D).trans (hF D hD)
  have hc := cleanLiteralsM_cost_le (ExecCNF.normalize SAT.Literal.negate F) k hw
  have hl := ExecCNF.normalize_length_le SAT.Literal.negate F
  have hc' : (cleanLiteralsM (ExecCNF.normalize SAT.Literal.negate F)).2 ≤
      F.length*((k+1)^2+1)+1 := by
    apply hc.trans
    gcongr
  simp only [normalizedInputM, normalizeLiteralM_value]
  unfold initializationBudget
  omega

/-- Executable normalization followed by the fuel-free measured worklist. The
threshold function is a supplied parameter; its construction is a separate cost. -/
def executeM (z : ℕ → ℕ) (k : ℕ) (hz : ∀ d, 2 ≤ d → 2 ≤ z d)
    (F : Formula n) : State (Formula n) × ℕ :=
  let normalized := normalizedInputM F
  let result := runM (executableBranching z k hz) (splitFormulaM z k)
    (fun G => splitFormulaM_value z k G) (initial normalized.1)
  (result.1, normalized.2 + result.2 + 1)

@[simp] theorem executeM_value (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) :
    (executeM z k hz F).1 = execute z k hz F := by
  unfold executeM
  simp only [normalizedInputM_value]
  change
    (runM (executableBranching z k hz) (splitFormulaM z k)
      (fun G => splitFormulaM_value z k G) (initial (normalizedInput F))).1 =
      run (executableBranching z k hz) (initial (normalizedInput F))
  exact runM_value _ _ _ _

/-- A concrete list invariant connecting raw sizes to finite-set width bounds. -/
def BoundedNode (k : ℕ) (F : Formula n) : Prop :=
  RawWidthAtMost k F ∧ (F.map ExecCNF.clauseSet).Nodup

theorem cleanLiterals_clause_sets (F : Formula n) :
    (cleanLiterals F).map ExecCNF.clauseSet = F.map ExecCNF.clauseSet := by
  simp [cleanLiterals, List.map_map, Function.comp_def]

theorem boundedNode_closed (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    SplitClosed (executableBranching (n := n) z k hz).split (BoundedNode k) := by
  intro F A B hF hs
  have hw := executable_raw_width_closed z k hz F A B hF.1 hs
  obtain ⟨d,c,_,rfl,rfl⟩ := splitFormula_some z k F A B hs
  refine ⟨⟨hw.1,?_⟩,⟨hw.2,?_⟩⟩ <;>
    simp only [children, cleanLiterals_clause_sets]
  · exact ExecCNF.absorb_map_nodup _
  · exact ExecCNF.absorb_map_nodup _

theorem normalizedInput_boundedNode (F : Formula n) (k : ℕ)
    (hF : RawWidthAtMost k F) : BoundedNode k (normalizedInput F) := by
  constructor
  · apply cleanLiterals_raw_width
    rw [ExecCNF.normalize_set]
    exact SAT.widthAtMost_of_subset (SAT.normalize_subset _) (semantic_width_of_raw F k hF)
  · rw [normalizedInput, cleanLiterals_clause_sets]
    exact ExecCNF.normalize_map_nodup _ _

theorem boundedNode_length (F : Formula n) (k : ℕ) (hF : BoundedNode k F) :
    F.length ≤ (2*n+1)^k := by
  have hcard := List.toFinset_card_of_nodup hF.2
  have heq : (ExecCNF.formulaSet F).card = F.length := by
    simpa only [ExecCNF.formulaSet, List.length_map] using hcard
  rw [← heq]
  exact QuantitativeSparsify.clause_count_le _ k (semantic_width_of_raw F k hF.1)

/-- Unconditional aggregation of the actual measured node operations over this
execution. The only bounds supplied are input width and the threshold table. -/
theorem executeM_events_bound (z : ℕ → ℕ) (k Z : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n)
    (hF : RawWidthAtMost k F) (hZ : ∀ d, 2 ≤ d → d ≤ k → z d ≤ Z) :
    (executeM z k hz F).2 ≤ initializationBudget F.length k +
      (nodeBudget ((2*n+1)^k) k Z + 6) * (execute z k hz F).visits + 2 := by
  have hi := normalizedInputM_cost_le F k hF
  have hr := initial_runM_events_bound (executableBranching z k hz) (splitFormulaM z k)
    (fun G => splitFormulaM_value z k G) (BoundedNode k) (boundedNode_closed z k hz)
    (nodeBudget ((2*n+1)^k) k Z) (by
      intro G hG
      exact (splitFormulaM_cost_le z k Z G hG.1 hZ).trans
        (nodeBudget_mono k Z (boundedNode_length G k hG)))
    (normalizedInput F) (normalizedInput_boundedNode F k hF)
  change _ ≤ initializationBudget F.length k +
    (nodeBudget ((2*n+1)^k) k Z + 6) * (run _ (initial (normalizedInput F))).visits + 2
  simp only [executeM, normalizedInputM_value]
  omega

end ConcreteMeasuredExecution

/-- The measured executor has the same assignment-wise union of leaves. -/
theorem executeM_models {n : ℕ} (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) (τ : Fin n → Bool) :
    SAT.CNF.eval τ (ExecCNF.formulaSet F) = true ↔
      ∃ G ∈ (executeM z k hz F).1.leaves,
        SAT.CNF.eval τ (ExecCNF.formulaSet G) = true := by
  rw [executeM_value]
  exact execute_models z k hz F τ

end SubexponentialSAT.ExecSparsifyWorklist

end OAI.Algorithms
