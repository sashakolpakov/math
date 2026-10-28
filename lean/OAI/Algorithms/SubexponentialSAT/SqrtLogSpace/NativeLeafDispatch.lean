import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

/-! Actual terminal dispatch for the disjoint counting DFS. The retained ambient
dimension determines the empty-formula count. The nonterminal command is composed
after the same concrete classifier and must supply its own execution proof. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch

open BitProgram StructuredCalls DisjointReuse DFSVisit

abbrev Data := State 80 1220

def command (nonterminal : Cmd 80 1220) : Cmd 80 1220 :=
  .seq NativeTerminal.readyCommand
    (.ite 0 (.base .skip) (.ite 7 nonterminal (.base .skip)))

variable {n k parameterBound : ℕ} {threshold : List Bool}
  {F : RawCNF n} {a : Data}

theorem ready_body (hr : LeafReady k threshold parameterBound F a) :
    a.stacks 265 = Encoding.encodeList id (NativeTerminal.clauseRecords F) :=
  hr.current.trans (NativeTerminal.clauseRecords_body F).symm

theorem ready_persistent (a : Data) (F : RawCNF n) (i : Fin 1220)
    (hi : i ∈ ([256, 257, 258, 259, 260, 261, 262, 264, 266, 267] : List (Fin 1220))) :
    (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i = a.stacks i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact NativeTerminal.readyResult_frame a n _ _ (by decide) (by decide) (by decide)

/-- The terminal branch returns the canonical whole count, including n = 0. -/
theorem terminal_done (hr : LeafReady k threshold parameterBound F a)
    (hterminal : [] ∈ F ∨ F = []) :
    LeafDone F a (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) := by
  constructor
  · exact NativeTerminal.readyResult_count a F hterminal
  · rw [NativeTerminal.readyResult_frame a n _ 30 (by decide) (by decide) (by decide)]
    exact hr.low_empty 30 (by decide)
  · exact ready_persistent a F

/-- Classification does not enlarge either persistent parameter word. -/
theorem nonterminal_ready (hr : LeafReady k threshold parameterBound F a)
    (hz : [] ∉ F) (hf : F ≠ []) :
    LeafReady k threshold parameterBound F
      (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) := by
  have frame := NativeTerminal.readyResult_frame a n (NativeTerminal.clauseRecords F)
  constructor
  · rw [frame 265 (by decide) (by decide) (by decide)]
    exact hr.current
  · rw [frame 264 (by decide) (by decide) (by decide)]
    exact hr.dimension
  · rw [frame 267 (by decide) (by decide) (by decide)]
    exact hr.ambient
  · rw [frame 264 (by decide) (by decide) (by decide)]
    exact hr.occurrence_length
  · rw [frame 267 (by decide) (by decide) (by decide)]
    exact hr.dimension_length
  · rw [frame 258 (by decide) (by decide) (by decide)]
    exact hr.header
  · rw [frame 259 (by decide) (by decide) (by decide)]
    exact hr.threshold
  · rw [frame 261 (by decide) (by decide) (by decide)]
    exact hr.left_empty
  · rw [frame 262 (by decide) (by decide) (by decide)]
    exact hr.right_empty
  · rw [NativeTerminal.readyResult, NativeTerminal.result_nonterminal _ F hz hf,
      NativeTerminal.classified_stacks, NativeTerminal.prepared_output]
  · intro i hi
    rw [frame i]
    · exact hr.low_empty i hi
    · intro h; have hv : i.val = 263 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 268 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 269 := congrArg Fin.val h; omega

theorem done_after_ready {e : Data}
    (hd : LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
    LeafDone F a e :=
  ⟨hd.count, hd.scratch, fun i hi => (hd.persistent i hi).trans (ready_persistent a F i hi)⟩

private theorem skip_bounded (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval (.base .skip) 0 a a bound := by
  refine ⟨.base (.skip a), ?_⟩
  intro prefixSteps c hp hc
  have hz : prefixSteps = 0 := by omega
  subst prefixSteps
  cases hc
  exact ha

/-- Actual classifier, terminal handling and nonterminal execution share one
uniform bound at every compiled prefix. The callback is an execution proof for
the explicit command argument, to be instantiated by the streamed leaf. -/
theorem command_execution (nonterminal : Cmd 80 1220) (leafTime bound : ℕ)
    (hr : LeafReady k threshold parameterBound F a)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hcallback : [] ∉ F → F ≠ [] →
      LeafReady k threshold parameterBound F
        (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) →
      (∀ i, ((NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i).length
        ≤ bound) →
      ∃ t ≤ leafTime, ∃ e,
        BoundedEval nonterminal t
          (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e bound ∧
        LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
    ∃ t ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + leafTime + 33,
      ∃ e, BoundedEval (command nonterminal) t a e bound ∧ LeafDone F a e := by
  obtain ⟨steps, hs, first⟩ := NativeTerminal.readyCommand_bounded a n bound
    (NativeTerminal.clauseRecords F) (ready_body hr)
    (fun i hi => hr.low_empty i (by omega)) hr.header hframe hclassifier hpower
  have hzero := NativeTerminal.readyResult_empty_clause a F
  have hnonempty := NativeTerminal.readyResult_nonempty a F
  by_cases hz : [] ∈ F
  · have second := (skip_bounded _ bound first.final_bound).ite_true
      (no := .ite 7 nonterminal (.base .skip)) (by simpa [hz] using hzero)
    exact ⟨_, by omega, _, first.seq second, terminal_done hr (Or.inl hz)⟩
  · by_cases hf : F = []
    · have second := ((skip_bounded _ bound first.final_bound).ite_false
        (yes := nonterminal) (by simpa [hf] using hnonempty)).ite_false
        (yes := .base .skip) (by simpa [hz] using hzero)
      exact ⟨_, by omega, _, first.seq second, terminal_done hr (Or.inr hf)⟩
    · obtain ⟨t, ht, e, last, hd⟩ :=
        hcallback hz hf (nonterminal_ready hr hz hf) first.final_bound
      have second := (last.ite_true (no := .base .skip)
        (by simpa [hf] using hnonempty)).ite_false (yes := .base .skip)
        (by simpa [hz] using hzero)
      exact ⟨_, by omega, e, first.seq second, done_after_ready hd⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
