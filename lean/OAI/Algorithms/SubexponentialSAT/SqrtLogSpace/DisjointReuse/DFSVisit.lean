import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

structure BoundedEval (command : Code) (steps : ℕ) (a b : Data) (bound : ℕ) : Prop where
  eval : Eval command steps a b
  space : ∀ prefixSteps c, prefixSteps ≤ steps →
    Trace (compiled command 256 256) prefixSteps
      (a.withPC (some (compiled command 256 256).entry)) c →
    ∀ i, (c.stacks i).length ≤ bound

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

theorem ite_true {flag : Fin 80} (hf : a.regs flag = true)
    (h : BoundedEval yes t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_true hf h.eval, StructuredSpace.conditional_true_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

theorem ite_false {flag : Fin 80} (hf : a.regs flag = false)
    (h : BoundedEval no t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_false hf h.eval, StructuredSpace.conditional_false_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

end BoundedEval

variable {n : ℕ}

structure LeafReady (k : ℕ) (threshold : List Bool) (parameterBound : ℕ)
    (F : RawCNF n) (d : Data) : Prop where
  current : d.stacks 265 = SparseCountProgram.encodeBody F
  dimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1)
  ambient : BinaryArithmetic.toNat (d.stacks 267) = n
  occurrence_length : (d.stacks 264).length ≤ parameterBound
  dimension_length : (d.stacks 267).length ≤ n + 1
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = threshold
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []

structure LeafDone (F : RawCNF n) (d e : Data) : Prop where
  count : e.stacks 263 = binaryNat (rawCount F)
  scratch : e.stacks 30 = []
  persistent : ∀ i, i ∈ ([256, 257, 258, 259, 260, 261, 262, 264, 266, 267] : List (Fin 1220)) →
    e.stacks i = d.stacks i

/-- The bound is uniform over all actual leaf inputs; time is separate. -/
structure LeafContract (k : ℕ) (threshold : List Bool) (parameterBound : ℕ)
    (leaf : Code) (time space : ℕ) : Prop where
  execution : ∀ (F : RawCNF n) (d : Data), Valid k F → LeafReady k threshold parameterBound F d →
    SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat threshold) = none →
    (∀ i, (d.stacks i).length ≤ space) →
    ∃ t ≤ time, ∃ e, BoundedEval leaf t d e space ∧ LeafDone F d e

def visitTime (k n bodyLength thresholdLength leafTime bound : ℕ) : ℕ :=
  9 * bodyLength + 11 +
    (SparsePriorityProgram.Selector.selectorCoefficient k * (bodyLength + thresholdLength + 1) ^ 4 + 1 +
      (max (621000 * (4 * bodyLength + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
        ((2 * bound + 3) * 257 + 1)))

/-- All branch construction, failed selector scans, accumulation and cleanup
are part of the same actual body evaluation. No elapsed traversal time enters
its source-space bound. -/
theorem body_refinement {k : ℕ} (threshold : List Bool) (leaf : Code)
    (node : Node n) (rest : List (Node n)) (total parameterBound leafTime bound : ℕ) (d : Data)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k node.formula) (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hparameterLength : (d.stacks 264).length ≤ parameterBound)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound)
    (hpop : n + 1 + (pendingBytes rest).length +
      11 * (SparseCountProgram.encodeBody node.formula).length + 13 ≤ bound)
    (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
      SparseSelectorRefinement.inputVolume node.formula threshold ^ 4 ≤ bound)
    (hbranch : (pendingBytes rest).length + (n + 1) +
      620001 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2 ≤ bound)
    (hadd : 100 * (n + 1) ≤ bound)
    (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
    ∃ next t, t ≤ visitTime k n (SparseCountProgram.encodeBody node.formula).length
        threshold.length leafTime bound ∧
      ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
        Boundary threshold next e ∧
        (∀ i, i ∈ ([256, 264, 266, 267] : List (Fin 1220)) → e.stacks i = d.stacks i) := by
  obtain ⟨a, hpa, hcurrent, hpending, hpf, hlow, _, _, _, hpspace⟩ :=
    popCurrent_boundary threshold node rest total d bound hb hbound
  have popEval : BoundedEval popCurrent
      (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d a bound :=
    ⟨hpa, fun t c ht hc i => (hpspace t c ht hc i).trans (max_le hpop le_rfl)⟩
  obtain ⟨ts, hts, b, hsb, hsf, hmissing, hfound, hsspace⟩ :=
    SparseSelectorRefinement.selectCurrent_execution node.formula threshold a bound hk hM
      hv.width hv.literal_nodup hv.clause_nodup hcurrent
      ((hpf 259 (by decide) (by decide)).trans hb.threshold)
      (fun i hi => hlow i (by omega)) popEval.final_bound
  have selectEval : BoundedEval (selectCurrent k) ts a b bound :=
    ⟨hsb, fun t c ht hc i => (hsspace t c ht hc i).trans (max_le hselect le_rfl)⟩
  have highFrame (i : Fin 1220) (hi : 256 ≤ i.val) (hic : i ≠ 265) (hip : i ≠ 257) :
      b.stacks i = d.stacks i := by
    rw [hsf i (by intro h; subst i; omega) (by intro h; subst i; omega), hpf i hic hip]
  have bPending : b.stacks 257 = pendingBytes rest :=
    (hsf 257 (by decide) (by decide)).trans hpending
  have bCurrent : b.stacks 265 = SparseCountProgram.encodeBody node.formula :=
    (hsf 265 (by decide) (by decide)).trans hcurrent
  have bHeader := (highFrame 258 (by decide) (by decide) (by decide)).trans hb.header
  have bThreshold := (highFrame 259 (by decide) (by decide) (by decide)).trans hb.threshold
  have bTotal := (highFrame 260 (by decide) (by decide) (by decide)).trans hb.total
  have bLeft := (highFrame 261 (by decide) (by decide) (by decide)).trans hb.left_empty
  have bRight := (highFrame 262 (by decide) (by decide) (by decide)).trans hb.right_empty
  have bLeaf := (highFrame 263 (by decide) (by decide) (by decide)).trans hb.leaf_empty
  have finish (next : Frontier n) (c : Data) (visit : AfterVisit threshold next c)
      (hc : ∀ i, (c.stacks i).length ≤ bound) :=
    finishVisit_boundary threshold next c bound visit hc
  cases hflag : b.regs 23 with
  | false =>
    obtain ⟨hstacks, _, _, hnone, _, _⟩ := hmissing hflag
    have ready : LeafReady k threshold parameterBound node.formula b :=
      ⟨bCurrent, by rw [highFrame 264 (by decide) (by decide) (by decide)]; exact hdimension,
        by rw [highFrame 267 (by decide) (by decide) (by decide)]; exact hambient,
        by rw [highFrame 264 (by decide) (by decide) (by decide)]; exact hparameterLength,
        by rw [highFrame 267 (by decide) (by decide) (by decide)]; exact hambientLength,
        bHeader, bThreshold, bLeft, bRight, bLeaf,
        fun i hi => (congrFun hstacks i).trans (hlow i hi)⟩
    obtain ⟨tl, htl, c, leafEval, done⟩ := hleaf.execution node.formula b hv ready hnone selectEval.final_bound
    obtain ⟨ta, hta, f, hacc, hvisit, hacframe, haspace⟩ :=
      accumulate_after_leaf threshold node rest total bound c
        ((done.persistent 257 (by simp)).trans bPending)
        ((done.persistent 258 (by simp)).trans bHeader)
        ((done.persistent 259 (by simp)).trans bThreshold)
        ((done.persistent 260 (by simp)).trans bTotal)
        ((done.persistent 261 (by simp)).trans bLeft)
        ((done.persistent 262 (by simp)).trans bRight)
        done.count done.scratch hcount leafEval.final_bound
    have accEval : BoundedEval accumulate ta c f bound :=
      ⟨hacc, fun t c ht hc i => (haspace t c ht hc i).trans (max_le hadd le_rfl)⟩
    obtain ⟨tf, htf, e, hfe, hboundary, hfframe, hfspace⟩ :=
      finish ⟨rest, total + rawCount node.formula⟩ f hvisit accEval.final_bound
    have finishEval : BoundedEval finishVisit tf f e bound := ⟨hfe, hfspace⟩
    have whole := popEval.seq (selectEval.seq
      (((leafEval.seq accEval).ite_false (yes := branch) hflag).seq finishEval))
    have hm := Nat.le_max_right (621000 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2)
      (leafTime + 100 * (n + 1))
    refine ⟨⟨rest, total + rawCount node.formula⟩, _, ?_, e, whole,
      .leaf node rest total hnone, hboundary, ?_⟩
    · unfold visitTime SparseSelectorRefinement.inputVolume at *
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [hfframe _ (by decide) (by decide),
        hacframe _ (by decide) (by decide) (by decide), done.persistent _ (by simp),
        highFrame _ (by decide) (by decide) (by decide)]
  | true =>
    obtain ⟨c, H, priority, _, hH, hS⟩ := hfound hflag
    have hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → b.stacks i = [] := by
      intro i hi hi9 hi12
      rw [hsf i hi9 hi12]
      exact hlow i (by omega)
    obtain ⟨tb, htb, f, hbf, transition, hvisit, hbspace⟩ :=
      branch_after_selection threshold node rest total bound H b hv priority bPending bHeader
        bThreshold bTotal bLeft bRight bLeaf bCurrent hH hS hclean selectEval.final_bound
    have hV := SparseDFSInvariantSpace.selected_inputVolume_le node.formula H priority.candidate
    have hVpow := Nat.pow_le_pow_left hV 2
    have branchEval : BoundedEval branch tb b f bound := by
      refine ⟨hbf, ?_⟩
      intro t c ht hc i
      apply (hbspace t c ht hc i).trans
      apply max_le le_rfl
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left 620001 hVpow) _).trans hbranch
    obtain ⟨tf, htf, e, hfe, hboundary, hfframe, hfspace⟩ :=
      finish _ f hvisit branchEval.final_bound
    have finishEval : BoundedEval finishVisit tf f e bound := ⟨hfe, hfspace⟩
    have whole := popEval.seq (selectEval.seq
      ((branchEval.ite_true (no := .seq leaf accumulate) hflag).seq finishEval))
    have htime := htb.trans (Nat.mul_le_mul_left 621000 hVpow)
    have hm := Nat.le_max_left (621000 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2)
      (leafTime + 100 * (n + 1))
    refine ⟨_, _, ?_, e, whole, transition, hboundary, ?_⟩
    · unfold visitTime SparseSelectorRefinement.inputVolume at *
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [hfframe _ (by decide) (by decide),
        SparseDFSResource.branch_preserves_other_high hbf _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide),
        highFrame _ (by decide) (by decide) (by decide)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
