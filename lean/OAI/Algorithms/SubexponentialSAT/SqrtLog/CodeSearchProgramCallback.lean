import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev wordCallback : Cmd 16 24 :=
  .seq prepareWordCommand <|
  .seq (invoke wordProgram wordRegisters wordStacks) <|
  .seq (.base (.atom (.copy 15 7))) (clearMany workPorts)

def callbackProgram := compiled wordCallback 22 22

private theorem prepared_register_frame (a : SearchState) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (preparedWord a).regs i = a.regs i := by
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    readRegs, h0, h1]

private theorem work_register_frame (frame : SearchState) (out : ScanState)
    (i : Fin 16) (hi : 8 ≤ i.val) :
    (embedState wordRegisters wordStacks frame out).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [wordRegisters] at hv
  omega

private theorem work_stack_frame (frame : SearchState) (out : ScanState)
    (i : Fin 24) (hi : 18 ≤ i.val) :
    (embedState wordRegisters wordStacks frame out).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [wordStacks] at hv
  omega

def callbackBudget (t D d : ℕ) :=
  (35 * (t * D) + 7 * t + 7 * d + 15 * D + 25) + wordBudget t D + 1 +
    18 * (2 * (wordInputSpan t D d + wordBudget t D) + 3)

private theorem clearManyCost_le_on (ps : List (Fin 24)) (a : SearchState) (B : ℕ)
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

/-- Callback correctness is unconditional on the supplied matrix; a rejected
candidate is processed by the same bit program. The quantitative theorem is
separate so that cleanup, too, must be charged. -/
theorem wordCallback_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : SearchState), n ≤ callbackBudget t D d ∧
      Eval wordCallback n a out ∧ WorkEmpty out ∧
      out.regs 15 = decide (wordRejects Q x d) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 22 = [] ∧
      (∀ i : Fin 24, 18 ≤ i.val → i ≠ 22 → out.stacks i = a.stacks i) := by
  have hp := prepareWord_eval a htmp
  have hproj := preparedWord_project Q x d a he hm ht hd hx
  obtain ⟨nw, small, hnw, hw, hf, hs⟩ :=
    word_eval Q x d ((preparedWord a).regs ∘ wordRegisters) []
  have htrace := compiled_halt_trace hw 11 10
  rw [← hproj] at htrace
  have hi := invoke_eval wordProgram wordRegisters wordStacks
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) (preparedWord a) small htrace
  let middle := embedState wordRegisters wordStacks (preparedWord a) small
  let flagged := (Atom.copy 15 7).eval middle
  let out := clearManyState workPorts flagged
  have hc := clearMany_eval workPorts flagged
  have hsmall : ∀ i : Fin 18, (small.stacks i).length ≤
      wordInputSpan t D d + wordBudget t D := by
    intro i
    have h := Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace hw 11 10) i
    have hi := wordInput_length_le Q x d ((preparedWord a).regs ∘ wordRegisters) i
    change (small.stacks i).length ≤
      ((extendMatrixState (matrixInput Q x ((preparedWord a).regs ∘ wordRegisters)) d []).stacks i).length +
        (nw + 1) at h
    omega
  have hcleanup := clearManyCost_le_on workPorts flagged
    (wordInputSpan t D d + wordBudget t D) (by
      intro i hi
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      change (middle.stacks (wordStacks j)).length ≤ _
      rw [show middle.stacks (wordStacks j) = small.stacks j from
        embedState_stack wordRegisters wordStacks (preparedWord a) small
          (Fin.castAdd_injective _ _) j]
      exact hsmall j)
  have hprep : prepareWordCost a =
      35 * (t * D) + 7 * t + 7 * d + 15 * D + 25 := by
    simp only [prepareWordCost, hm, ht, hd, hx, List.length_reverse,
      List.length_replicate, scalarFrames_ternary_length, matrixFrames_ternary_length,
      List.length_ofFn]
    ring
  have hclen : workPorts.length = 18 := by simp [workPorts]
  rw [hclen] at hcleanup
  refine ⟨prepareWordCost a + (nw + 1 + (1 + clearManyCost workPorts flagged)), out,
    ?_, hp.seq (hi.seq ((Eval.base (.atom _ middle)).seq hc)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprep]
    unfold callbackBudget
    omega
  · intro i
    change (clearManyState workPorts flagged).stacks (wordStacks i) = []
    rw [clearMany_stacks, ite_eq_left]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · rw [show out.regs 15 = flagged.regs 15 from
      clearMany_reg_frame workPorts flagged 15 (by decide) (by decide)]
    change middle.regs 7 = _
    exact (embedState_register wordRegisters wordStacks (preparedWord a) small
      (Fin.castAdd_injective _ _) 7).trans hf
  · rw [show out.regs 13 = flagged.regs 13 from
      clearMany_reg_frame workPorts flagged 13 (by decide) (by decide)]
    change middle.regs 13 = _
    rw [work_register_frame _ _ _ (by decide)]
    exact prepared_register_frame _ _ (by decide) (by decide)
  · rw [show out.regs 14 = flagged.regs 14 from
      clearMany_reg_frame workPorts flagged 14 (by decide) (by decide)]
    change middle.regs 14 = _
    rw [work_register_frame _ _ _ (by decide)]
    exact prepared_register_frame _ _ (by decide) (by decide)
  · change (clearManyState workPorts flagged).stacks 22 = []
    rw [clearMany_stacks, ite_eq_right (by rw [workPorts_mem]; decide)]
    change middle.stacks 22 = []
    rw [work_stack_frame _ _ _ (by decide)]
    exact preparedWord_payload a
  · intro i hi22 hneq
    change (clearManyState workPorts flagged).stacks i = _
    rw [clearMany_stacks, ite_eq_right (by rw [workPorts_mem]; omega)]
    change middle.stacks i = _
    rw [work_stack_frame _ _ _ hi22]
    exact preparedWord_frame a i hi22 hneq

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
