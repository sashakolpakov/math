import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev graphWordCallback : Cmd 16 36 :=
  .seq prepareGraphWordCommand <|
  .seq (invoke graphWordProgram graphWorkRegisters graphWordStacks) (clearMany graphWorkPorts)

def graphCallbackProgram := compiled graphWordCallback 34 34

private theorem prepared_register_frame (a : GraphSearchState) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (preparedGraphWord a).regs i = a.regs i := by
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    readRegs, h0, h1]

private theorem work_stack_frame (frame : GraphSearchState) (out : GraphWordState)
    (i : Fin 36) (hi : 29 ≤ i.val) :
    (embedState id graphWordStacks frame out).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [graphWordStacks] at hv
  omega

def graphCallbackBudget (D r qlen Dlen : ℕ) :=
  (35 * (D * r) + 7 * D + 7 * qlen + 7 * Dlen + 15 * r + 31) +
    graphWordBudget D r qlen Dlen +
      29 * (2 * (graphInputSpan D r qlen Dlen + graphWordBudget D r qlen Dlen) + 3)

private theorem clearManyCost_le_on (ps : List (Fin 36)) (a : GraphSearchState) (B : ℕ)
    (ha : ∀ i ∈ ps, (a.stacks i).length ≤ B) :
    clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
      have hc := ih (clearState p a) (by
        intro i hi
        by_cases hip : i = p
        · simp [clearState, hip]
        · simpa [clearState, hip] using ha i (by simp [hi]))
      have hp := ha p (by simp)
      simp only [clearManyCost, List.length_cons]
      nlinarith

/-- Every character uses the same closed bit predicate, whether or not this
candidate graph is good. The cleanup charge includes all arithmetic scratch. -/
theorem graphWordCallback_eval {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : GraphSearchState) (he : GraphWorkEmpty a)
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : GraphSearchState), n ≤ graphCallbackBudget D r qbits.length Dbits.length ∧
      Eval graphWordCallback n a out ∧ GraphWorkEmpty out ∧
      out.regs 15 = decide (graphWordRejects s x q) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 34 = [] ∧
      (∀ i : Fin 36, 29 ≤ i.val → i ≠ 34 → out.stacks i = a.stacks i) := by
  let initial := projectState id graphWordStacks (preparedGraphWord a)
  have hp := prepareGraphWord_eval a htmp
  obtain ⟨nw,small,hnw,hw,hf,hqout,hDout,hclean,h13,h14⟩ :=
    graphWord_eval s x q qbits Dbits hqv hDv initial
      (preparedGraphWord_project s x qbits Dbits a he hm ht hq hD hx)
      (preparedGraphWord_scratch a he)
  have hi := invoke_eval graphWordProgram id graphWordStacks Function.injective_id
    (Fin.castAdd_injective _ _) (preparedGraphWord a) small (compiled_halt_trace hw 11 9)
  let middle := embedState id graphWordStacks (preparedGraphWord a) small
  let out := clearManyState graphWorkPorts middle
  have hc := clearMany_eval graphWorkPorts middle
  have hsmall (i : Fin 29) : (small.stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length + graphWordBudget D r qbits.length Dbits.length := by
    have h := SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace hw 11 9) i
    have hinput := preparedGraphWord_length_le s x qbits Dbits a he hm ht hq hD hx i
    change (small.stacks i).length ≤ (initial.stacks i).length + (nw+1) at h
    change (initial.stacks i).length ≤ graphInputSpan D r qbits.length Dbits.length at hinput
    omega
  have hcleanup := clearManyCost_le_on graphWorkPorts middle
    (graphInputSpan D r qbits.length Dbits.length + graphWordBudget D r qbits.length Dbits.length) (by
      intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      rw [show middle.stacks (graphWordStacks j) = small.stacks j from
        embedState_stack id graphWordStacks (preparedGraphWord a) small (Fin.castAdd_injective _ _) j]
      exact hsmall j)
  have hprep : prepareGraphWordCost a =
      35 * (D * r) + 7 * D + 7 * qbits.length + 7 * Dbits.length + 15 * r + 31 := by
    simp only [prepareGraphWordCost,hm,ht,hq,hD,hx,List.length_reverse,
      List.length_replicate,scalarFrames_binary_length,matrixFrames_binary_length,List.length_ofFn]
    ring
  have hclen : graphWorkPorts.length = 29 := by simp [graphWorkPorts]
  rw [hclen] at hcleanup
  refine ⟨prepareGraphWordCost a + (nw+1+clearManyCost graphWorkPorts middle),out,?_,
    hp.seq (hi.seq hc),?_,?_,?_,?_,?_,?_⟩
  · rw [hprep]; unfold graphCallbackBudget; omega
  · intro i
    have hm : graphWordStacks i ∈ graphWorkPorts := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [clearMany_stacks,ite_eq_left hm]
  · rw [show out.regs 15 = middle.regs 15 from
      clearMany_reg_frame graphWorkPorts middle 15 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 15).trans hf
  · rw [show out.regs 13 = middle.regs 13 from
      clearMany_reg_frame graphWorkPorts middle 13 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 13).trans (h13.trans (prepared_register_frame a 13 (by decide) (by decide)))
  · rw [show out.regs 14 = middle.regs 14 from
      clearMany_reg_frame graphWorkPorts middle 14 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 14).trans (h14.trans (prepared_register_frame a 14 (by decide) (by decide)))
  · rw [clearMany_stacks,ite_eq_right (by rw [graphWorkPorts_mem]; decide)]
    rw [work_stack_frame _ _ _ (by decide)]
    exact preparedGraphWord_payload a
  · intro i hi hne
    rw [clearMany_stacks,ite_eq_right (by rw [graphWorkPorts_mem]; omega)]
    rw [work_stack_frame _ _ _ hi]
    exact preparedGraphWord_frame a i hi hne

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
