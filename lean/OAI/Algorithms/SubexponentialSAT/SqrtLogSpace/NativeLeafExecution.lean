import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafCall

/-! Concrete shared-ABI loading, local execution and whole-count export for a
DFS leaf. The local command remains explicit; its actual execution proof is
supplied by the streamed leaf construction. No new machine service is defined. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution

open BitProgram StructuredCalls DisjointReuse DFSVisit

abbrev Data := State 80 1220
abbrev LocalData := State 40 896

def command (localCommand : Cmd 40 896) : Cmd 80 1220 :=
  .seq Native.loadLeaf
    (.seq (ABI.leafCall (compiled localCommand 784 788)) Native.exportLeaf)

theorem outside_leaf_low (i : Fin 1220) (hi : i.val < 320) :
    ¬ ∃ j, ABI.leafStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change 320 + j.val = i.val at hv
  omega

/-- The local compiled halt is paid before the full count word is copied out;
the leaf bank is then physically cleared, with every prefix bounded by B. -/
theorem call_export_execution (localCommand : Cmd 40 896) (a : Data) (b : LocalData)
    {steps localBound B : ℕ}
    (he : Eval localCommand steps (projectState ABI.leafRegisters ABI.leafStacks a) b)
    (hp : ∀ q z, q ≤ steps →
      Trace (compiled localCommand 784 788) q
        ((projectState ABI.leafRegisters ABI.leafStacks a).withPC
          (some (compiled localCommand 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ localBound)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hB : localBound ≤ B) :
    ∃ t ≤ steps + 1803 * B + 2700, ∃ e,
      BoundedEval (.seq (ABI.leafCall (compiled localCommand 784 788)) Native.exportLeaf)
        t a e B ∧
      e.stacks 263 = b.stacks 788 ∧ e.stacks 1219 = [] ∧
      (∀ j, e.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
        e.stacks i = a.stacks i) := by
  have first := Native.leafCall_bounded_eval localCommand a b he hp ha hB
  obtain ⟨t, e, ht, heval, hout, hs, hempty, hframe, _⟩ :=
    Native.exportLeaf_eval _ B first.final_bound
  have second : BoundedEval Native.exportLeaf t _ e B :=
    ⟨heval, Native.exportLeaf_space heval first.final_bound⟩
  refine ⟨_, by omega, e, first.seq second,
    hout.trans (Native.leafResult_output a b), hs, hempty, ?_⟩
  intro i hi hi263 hi1219
  exact (hframe i hi hi263 hi1219).trans (Native.leafResult_frame a b i hi)

/-- Concrete input words, empty worker ports and reset registers are produced
by the loader. The local bound depends on those input sizes independently of
the suspended DFS frame. The caller supplies a proof of the explicit local
command, rather than an abstract evaluator or layout service. -/
theorem command_execution {n k parameterBound B localBound localTime : ℕ}
    (threshold : List Bool) (F : RawCNF n) (a : Data) (localCommand : Cmd 40 896)
    (hv : SparseDFSRefinement.Valid k F)
    (hr : LeafReady k threshold parameterBound F a)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hB : localBound ≤ B)
    (hlocal : ∀ d : LocalData,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval localCommand steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (compiled localCommand 784 788) q
          (d.withPC (some (compiled localCommand 784 788).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    ∃ steps ≤ 3618 * B + localTime + 5446, ∃ e,
      BoundedEval (command localCommand) steps a e B ∧ LeafDone F a e ∧
      e.stacks 1219 = [] ∧ (∀ j, e.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
        e.stacks i = a.stacks i) := by
  obtain ⟨loadSteps, b, hload, first, hformula, hn, hdimension, hsize,
      hempty, hregs, hframe⟩ := Native.loadLeaf_input_bound threshold F a hv hr ha
  obtain ⟨localSteps, hlocalSteps, c, he, hout, hp⟩ :=
    hlocal (projectState ABI.leafRegisters ABI.leafStacks b)
      hformula hn hdimension hsize hempty hregs
  obtain ⟨tailSteps, htail, e, second, hcount, hs, hclear, htailFrame⟩ :=
    call_export_execution localCommand b c he hp first.final_bound hB
  have frame (i : Fin 1220) (hi : ¬ ∃ j, ABI.leafStacks j = i)
      (hi263 : i ≠ 263) (hi1219 : i ≠ 1219) : e.stacks i = a.stacks i :=
    (htailFrame i hi hi263 hi1219).trans (hframe i hi hi1219)
  refine ⟨_, by omega, e, first.seq second, ?_, hs, hclear, frame⟩
  constructor
  · exact hcount.trans hout
  · exact (frame 30 (outside_leaf_low 30 (by decide)) (by decide) (by decide)).trans
      (hr.low_empty 30 (by decide))
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact frame _ (outside_leaf_low _ (by decide)) (by decide) (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution
