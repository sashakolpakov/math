import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureRescan
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

/-- Copy the runtime palette size and initial physical head address into two
persistent controller tapes. The active flag is set even for zero heads, so
the empty tuple reaches the callback exactly once. -/
def initializeLevelsCommand : Cmd 40 896 :=
  .seq (copyWord 130 (tupleStacks 6) (tupleStacks 5))
    (.seq (copyWord 649 (tupleStacks 9) (tupleStacks 5))
      (.base (.seq (.atom (.peek (tupleStacks 6) 0 1))
        (.seq (.atom (.bnot controllerPorts.leaf 1))
          (.atom (.set controllerPorts.active true))))))

def initializeLevelsState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.active true).eval
    ((StructuredProgram.Atom.bnot controllerPorts.leaf 1).eval
      ((StructuredProgram.Atom.peek (tupleStacks 6) 0 1).eval
        (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a))))

theorem initializeLevels_eval (a : State 40 896) (hs : a.stacks (tupleStacks 5) = []) :
    Eval initializeLevelsCommand
      (7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13)
      a (initializeLevelsState a) := by
  let b := copyState 130 (tupleStacks 6) a
  have hb := copyWord_eval 130 (tupleStacks 6) (tupleStacks 5)
    (by decide) (by decide) (by decide) a hs
  have hbs : b.stacks (tupleStacks 5) = [] := by
    simpa [b, copyState, StackRoutines.copyStacks] using hs
  have hc := copyWord_eval 649 (tupleStacks 9) (tupleStacks 5)
    (by decide) (by decide) (by decide) b hbs
  have ht := Eval.seq hb (Eval.seq hc
    (Eval.base (StructuredProgram.Eval.seq (.atom (.peek (tupleStacks 6) 0 1) _)
      (.seq (.atom (.bnot controllerPorts.leaf 1) _)
        (.atom (.set controllerPorts.active true) _)))))
  have hw : b.stacks 649 = a.stacks 649 := by
    simp [b, copyState, StackRoutines.copyStacks, (by decide : (649 : Fin 896) ≠ tupleStacks 6)]
  rw [hw] at ht
  change Eval initializeLevelsCommand _ a (initializeLevelsState a) at ht
  convert ht using 1
  omega

theorem initializeLevelsState_words (a : State 40 896) (heads address : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (ha : a.stacks 649 = List.replicate address true)
    (he : a.stacks (tupleStacks 6) = []) (hz : a.stacks (tupleStacks 9) = []) :
    (initializeLevelsState a).stacks (tupleStacks 6) = List.replicate heads true ∧
      (initializeLevelsState a).stacks (tupleStacks 9) = List.replicate address true := by
  change (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 6) = _ ∧
    (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 9) = _
  simp [copyState, StackRoutines.copyStacks, hh, ha, he, hz,
    (by decide : tupleStacks 6 ≠ tupleStacks 9),
    (by decide : tupleStacks 9 ≠ tupleStacks 6),
    (by decide : (649 : Fin 896) ≠ tupleStacks 6)]

theorem initializeLevelsState_flags (a : State 40 896) (heads : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (he : a.stacks (tupleStacks 6) = []) :
    (initializeLevelsState a).regs controllerPorts.active = true ∧
      (initializeLevelsState a).regs controllerPorts.leaf = decide (heads = 0) := by
  cases heads <;>
    simp [initializeLevelsState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      copyState, StackRoutines.copyStacks, controllerPorts, hh, he, List.replicate_succ,
      (by decide : tupleStacks 6 ≠ tupleStacks 9)]

/-- The scratch bank is disjoint from the retained ring tables and metadata.
Only the five named persistent source fields are mapped outside340..363. -/
def rescanStacks : Fin 24 ↪ Fin 896 where
  toFun i :=
    ⟨if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val, by
        split_ifs <;> have hi := i.isLt <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have he := congrArg Fin.val hij
    dsimp at he
    split_ifs at he <;> omega

def rescanRegisters : Fin 16 ↪ Fin 40 := Fin.castLEEmb (by decide)

@[simp] theorem rescanStacks_offset : rescanStacks 0 = 141 := rfl
@[simp] theorem rescanStacks_matrix : rescanStacks 15 = tupleStacks 11 := rfl
@[simp] theorem rescanStacks_candidate : rescanStacks 16 = tupleStacks 2 := rfl
@[simp] theorem rescanStacks_key : rescanStacks 17 = tupleStacks 3 := rfl
@[simp] theorem rescanStacks_predecessor : rescanStacks 18 = tupleStacks 8 := rfl
@[simp] theorem rescanStacks_fresh : rescanStacks 22 = 362 := rfl

/-- A real one-bit latch initializer, charged on every predicate call. It
also covers the first call after the loader has cleared its scratch bank. -/
def initializeFreshCommand : Cmd 40 896 :=
  .seq (clearWord (rescanStacks 22))
    (.base (.seq (.atom (.set 0 false)) (.atom (.push (rescanStacks 22) 0))))

def initializeFreshState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.push (rescanStacks 22) 0).eval
    ((StructuredProgram.Atom.set 0 false).eval (clearState (rescanStacks 22) a))

theorem initializeFresh_eval (a : State 40 896) :
    Eval initializeFreshCommand (2 * (a.stacks (rescanStacks 22)).length + 5) a
      (initializeFreshState a) := by
  have ht := Eval.seq (clearWord_eval (rescanStacks 22) a)
    (Eval.base (StructuredProgram.Eval.seq (.atom (.set 0 false) _)
      (.atom (.push (rescanStacks 22) 0) _)))
  simpa only [initializeFreshCommand, initializeFreshState, Nat.add_assoc] using ht

theorem initializeFreshState_word (a : State 40 896) :
    (initializeFreshState a).stacks (rescanStacks 22) = [false] := by
  simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, clearState]

/-- A completed duplicate step clears its saved key before the next predicate.
Thus every scan boundary has an empty output key tape. -/
def advanceCandidateCommand : Cmd 40 896 :=
  .seq advanceCommand (clearWord (tupleStacks 3))

/-- On return to a parent, only the predecessor zero word is reset. The saved
candidate and remaining counter are restored and then advanced exactly once. -/
def resetPredecessorCommand : Cmd 40 896 :=
  copyWord 651 (tupleStacks 8) (tupleStacks 5)

/-- The candidate predicate runs only when the complete remaining word is
nonzero. Its one-bit result is copied from the actual latch, not from a key. -/
def probeWith (predicate : Cmd 40 896) : Cmd 40 896 :=
  .seq testAvailableCommand
    (.ite controllerPorts.available
      (.seq initializeFreshCommand
        (.seq predicate (.base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0)))))
      (.base .skip))

/-- A child starts after one emitted representative is recorded and its
parent's bounded cursor is suspended. All current head arrays are cleared. -/
def descendWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq recordRepresentativeCommand
    (.seq saveCursorCommand
      (.seq descendLevelCommand
        (.seq leaveHeadCommand
          (.ite controllerPorts.leaf (.base .skip)
            (.seq loadHead resetGeneratorCommand)))))

/-- The parent cursor is restored without rerunning its preceding candidate
scans. Only its polynomial-size matrix is reconstructed before the advance. -/
def resumeParentWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq dropRepresentativeCommand
    (.seq restoreCursorCommand
      (.seq ascendLevelCommand
        (.seq loadHead (.seq resetPredecessorCommand advanceCandidateCommand))))

def ascendWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq leaveHeadCommand
    (.seq testParentCommand
      (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip)))

/-- Clear every tuple controller tape once at entry. The fixed list has twelve
ports, independent of the input, assignment count, and number of signatures. -/
def setupWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq (clearWords (List.ofFn tupleStacks))
    (.seq initializeLevelsCommand
      (.ite controllerPorts.leaf (.base .skip) (.seq loadHead resetGeneratorCommand)))

/-- Finite-command assembly used by the concrete loader/predicate adapters.
The exact callback is instantiated by the query evaluator. These arguments
are syntactic programs; this constructor is not the final correctness theorem. -/
def assembleRoutines (loadHead predicate visit : Cmd 40 896) : Routines 40 896 where
  setup := setupWith loadHead
  probe := probeWith predicate
  descend := descendWith loadHead
  advance := advanceCandidateCommand
  ascend := ascendWith loadHead
  visit := visit

/-- Decrement retains the full `h+1`-bit remaining word, including leading
zeros. This matches the suspended-frame encoding after every candidate. -/
theorem remaining_word_after_advance (a : State 40 896) (h candidate : ℕ)
    (hc : candidate < 2 ^ h)
    (hs : a.stacks candidatePorts.scratch = [])
    (hr : a.stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - candidate)) :
    (advanceState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - (candidate + 1)) := by
  have hpow : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hbound : 2 ^ h - candidate < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hnext : 2 ^ h - (candidate + 1) < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hv : CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - candidate := by
    rw [hr]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ hbound
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by omega
  rw [advanceState_remaining a hs]
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · rw [CounterPrograms.decrement_length hp, hr]
    simp
  · rw [ExecCNFTupleEnumeration.fixedBits_value _ _ hnext]
    have hd := CounterPrograms.value_decrement hp
    omega

theorem initial_remaining_word (h : ℕ) :
    List.replicate h false ++ [true] =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h) := by
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hb : 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ]; omega
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by rw [Counters.powerTwo_value, ExecCNFTupleEnumeration.fixedBits_value _ _ hb])

/-- The initial head-controller copies and flag operations have polynomial
space at every source prefix, including all persistent caller stacks. -/
theorem initializeLevels_stack_bound (a : State 40 896) (entryBound : ℕ)
    (ha : stackBits a.stacks ≤ entryBound) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13 →
      Trace (compiled initializeLevelsCommand 0 0) prefixSteps
        (a.withPC (some (compiled initializeLevelsCommand 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ entryBound +
        7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13 := by
  have hb := StructuredSpace.local_stack_bound (compiled initializeLevelsCommand 0 0)
    (a := a.withPC (some (compiled initializeLevelsCommand 0 0).entry))
    (steps := 7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13) ha
  simpa only [Nat.add_assoc] using hb

/-- Every tuple control tape outside the four current predicate fields is
outside the local rescan's port image. -/
theorem rescan_avoids_tuple (j : Fin 12) (h2 : j ≠ 2) (h3 : j ≠ 3)
    (h8 : j ≠ 8) (h11 : j ≠ 11) :
    ¬ ∃ i, rescanStacks i = tupleStacks j := by
  rintro ⟨i, he⟩
  have hi := i.isLt
  have hj := j.isLt
  have hj2 : j.val ≠ 2 := fun hv => h2 (Fin.ext hv)
  have hj3 : j.val ≠ 3 := fun hv => h3 (Fin.ext hv)
  have hj8 : j.val ≠ 8 := fun hv => h8 (Fin.ext hv)
  have hj11 : j.val ≠ 11 := fun hv => h11 (Fin.ext hv)
  have hv := congrArg Fin.val he
  change (if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) = 836 + j.val at hv
  by_cases h0 : i.val = 0 <;> by_cases h15 : i.val = 15 <;>
    by_cases h16 : i.val = 16 <;> by_cases h17 : i.val = 17 <;>
    by_cases h18 : i.val = 18 <;> simp [h0, h15, h16, h17, h18] at hv <;> omega

theorem rescan_embed_tuple (frame : State 40 896) (callee : State 16 24)
    (j : Fin 12) (h2 : j ≠ 2) (h3 : j ≠ 3) (h8 : j ≠ 8) (h11 : j ≠ 11) :
    (embedState rescanRegisters rescanStacks frame callee).stacks (tupleStacks j) =
      frame.stacks (tupleStacks j) :=
  embedState_stack_frame _ _ _ _ _ (rescan_avoids_tuple j h2 h3 h8 h11)

theorem rescan_embed_controller (frame : State 40 896) (callee : State 16 24)
    (j : Fin 40) (hj : 16 ≤ j.val) :
    (embedState rescanRegisters rescanStacks frame callee).regs j = frame.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [rescanRegisters] at hv
  omega

/-- The preserved caller frame is charged once when transferring the local
predicate's uniform bound to all896 physical source stacks. -/
theorem rescan_lifted_stack_bound {labels steps bound frameBound : ℕ}
    (routine : Program 16 24 labels) (frame : Cfg 40 896 labels)
    {a b : Cfg 16 24 labels} (hrun : Trace routine steps a b)
    (hlocal : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram routine rescanRegisters rescanStacks) prefixSteps
        (ProgramLinking.embedCfg rescanRegisters rescanStacks id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  StructuredSpace.liftProgram_stack_bound routine rescanRegisters rescanStacks frame
    rescanRegisters.injective rescanStacks.injective hrun hlocal hframe


/-- The complete predecessor predicate, on the fixed shared leaf ABI. The
program computes its candidate key before rescanning earlier assignments. -/
def candidateMachine := ProgramLinking.liftProgram
  AttainedSignatureProgram.Rescan.candidateProgram rescanRegisters rescanStacks

def candidateCall : Cmd 40 896 := .call candidateMachine

noncomputable def candidateInput (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (fresh : Bool) : State 40 896 :=
  embedState rescanRegisters rescanStacks frame
    (AttainedSignatureProgram.Rescan.workState regs W rows
      (ExecCNFTupleEnumeration.fixedBits h candidate) []
      (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])

noncomputable def candidateOutput (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) : State 40 896 :=
  embedState rescanRegisters rescanStacks frame
    (AttainedSignatureProgram.Rescan.workState regs W rows
      (ExecCNFTupleEnumeration.fixedBits h candidate)
      (AttainedSignatureProgram.Rescan.naturalKey W rows h candidate)
      (List.replicate h false) []
      (!(AttainedSignatures.duplicateScan
        (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate)) [] [])

/-- The actual complete predicate retains its exact key and freshness result,
with time and all physical source-stack prefixes bounded on one lifted run.
The caller's persistent data are included through `frameBound`. -/
theorem candidate_run (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h B frameBound : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 1, ∃ out,
      Eval candidateCall n (candidateInput frame regs W rows h candidate fresh)
        (candidateOutput frame out W rows h candidate) ∧
      Trace candidateMachine n
        ((candidateInput frame regs W rows h candidate fresh).withPC
          (some candidateMachine.entry))
        ((candidateOutput frame out W rows h candidate).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace candidateMachine prefixSteps
          ((candidateInput frame regs W rows h candidate fresh).withPC
            (some candidateMachine.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (AttainedSignatureProgram.Rescan.spaceBudget W rows h B) frameBound := by
  obtain ⟨n, hn, out, ht, hspace⟩ :=
    AttainedSignatureProgram.Rescan.candidate_run regs W rows h B hlen hwidth candidate fresh
  have htrace := ProgramLinking.liftProgram_trace
    AttainedSignatureProgram.Rescan.candidateProgram rescanRegisters rescanStacks
    (frame.withPC none) rescanRegisters.injective rescanStacks.injective ht
  have htrace' : Trace candidateMachine n
      ((candidateInput frame regs W rows h candidate fresh).withPC
        (some candidateMachine.entry))
      ((candidateOutput frame out W rows h candidate).withPC none) := by
    simpa [candidateMachine, candidateInput, candidateOutput, ProgramLinking.embedCfg,
      ProgramLinking.relocatePc, embedState, StructuredProgram.State.withPC,
      ProgramLinking.liftProgram] using htrace
  refine ⟨n, hn, out, .call _ htrace', htrace', ?_⟩
  have hb := rescan_lifted_stack_bound
    AttainedSignatureProgram.Rescan.candidateProgram (frame.withPC none) ht hspace hframe
  simpa [candidateMachine, candidateInput, ProgramLinking.embedCfg,
    ProgramLinking.relocatePc, embedState, StructuredProgram.State.withPC,
    ProgramLinking.liftProgram] using hb

/-- Saved cursor frames, representative frames, depth, remaining assignments,
and the physical head address survive the actual predicate call unchanged. -/
theorem candidateOutput_control (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 12)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (h8 : j ≠ 8) (h11 : j ≠ 11) :
    (candidateOutput frame regs W rows h candidate).stacks (tupleStacks j) =
      frame.stacks (tupleStacks j) :=
  rescan_embed_tuple _ _ j h2 h3 h8 h11

theorem candidateOutput_flag (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val) :
    (candidateOutput frame regs W rows h candidate).regs j = frame.regs j :=
  rescan_embed_controller _ _ j hj

theorem candidateOutput_fresh (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) :
    (candidateOutput frame regs W rows h candidate).stacks (rescanStacks 22) =
      [!(AttainedSignatures.duplicateScan
        (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate)] := by
  rw [candidateOutput, embedState_stack _ _ _ _ rescanStacks.injective]
  rfl


/-- Calling from a concrete caller requires only its explicit local data
projection, rather than a supplied successful evaluation. -/
theorem candidate_eval (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool)
    (hdata : projectState rescanRegisters rescanStacks a =
      AttainedSignatureProgram.Rescan.workState (a.regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []) :
    ∃ n ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 1, ∃ out,
      Eval candidateCall n a (candidateOutput a out W rows h candidate) := by
  obtain ⟨n, hn, out, ht, _⟩ := AttainedSignatureProgram.Rescan.candidate_run
    (a.regs ∘ rescanRegisters) W rows h B hlen hwidth candidate fresh
  rw [← hdata] at ht
  exact ⟨n, hn, out, eval_call_from_state _ _ _ a
    rescanRegisters.injective rescanStacks.injective ht⟩

theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

theorem initializeFreshState_controller (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (initializeFreshState a).regs j = a.regs j := by
  simp only [initializeFreshState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    execInstr, Function.update_of_ne h0]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

noncomputable def probePreState (a : State 40 896) : State 40 896 :=
  initializeFreshState (testAvailableState a)

noncomputable def probePostState (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) : State 40 896 :=
  (StructuredProgram.Atom.peek (rescanStacks 22) controllerPorts.fresh 0).eval
    (candidateOutput (probePreState a) out W rows h candidate)

/-- Every nonempty generator probe includes its full-word availability test,
latch initialization, actual complete predecessor scan, and latch readback. -/
theorem probe_candidate_eval (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h))
    (hs : a.stacks remainingPorts.scratch = [])
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false)
    (hdata : projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] []) :
    ∃ n ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        8 * (a.stacks remainingPorts.counter).length +
        2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
      Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) := by
  have havailable : (testAvailableState a).regs controllerPorts.available = true := by
    rw [testAvailableState_flag, hnonzero]
    rfl
  obtain ⟨n, hn, out, ht⟩ :=
    candidate_eval (probePreState a) W rows h B hlen hwidth candidate false hdata
  have hinit := initializeFresh_eval (testAvailableState a)
  have he : Eval (probeWith candidateCall)
      (8 * (a.stacks remainingPorts.counter).length + 8 +
        (2 * ((testAvailableState a).stacks (rescanStacks 22)).length + 5 + (n + 1) + 1))
      a (probePostState a out W rows h candidate) := (testAvailable_eval a hs).seq
    (Eval.ite_true havailable (hinit.seq (ht.seq
      (Eval.base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0) _)))))
  rw [testAvailableState_stacks a hs] at he
  refine ⟨_, ?_, out, he⟩
  omega

/-- Exhaustion never runs the candidate scanner. In particular the binary
fuel word can be zero even when it retains leading zero cells. -/
theorem probe_exhausted_eval (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = [])
    (hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true) :
    Eval (probeWith candidateCall) (8 * (a.stacks remainingPorts.counter).length + 9)
      a (testAvailableState a) := by
  have hf : (testAvailableState a).regs controllerPorts.available = false := by
    rw [testAvailableState_flag, hzero]
    rfl
  have he : Eval (probeWith candidateCall)
      (8 * (a.stacks remainingPorts.counter).length + 8 + (0 + 1))
      a (testAvailableState a) :=
    (testAvailable_eval a hs).seq (Eval.ite_false hf (Eval.base (.skip _)))
  simpa only [probeWith, Nat.add_assoc] using he

theorem probePostState_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan
          (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) := by
  have hw := candidateOutput_fresh (probePreState a) out W rows h candidate
  simp only [rescanStacks_fresh] at hw
  have hav : (candidateOutput (probePreState a) out W rows h candidate).regs
      controllerPorts.available = true := by
    rw [candidateOutput_flag _ _ _ _ _ _ _ (by decide)]
    rw [probePreState, initializeFreshState_controller _ _ (by decide) (by decide)]
    rw [testAvailableState_flag, hnonzero]
    rfl
  constructor
  · simpa [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts] using hav
  · simp [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts]


/-- Exact physical data needed by the rescan. The predicate itself supplies
its evaluation; these are byte descriptions of its input tapes. The latch
may initially contain any word because `probeWith` initializes it. -/
structure CandidateReady (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ) (candidate : Fin (2 ^ h)) : Prop where
  offset : a.stacks (rescanStacks 0) = W
  matrix : a.stacks (rescanStacks 15) =
    Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words)
  current : a.stacks (rescanStacks 16) = ExecCNFTupleEnumeration.fixedBits h candidate
  saved : a.stacks (rescanStacks 17) = []
  predecessor : a.stacks (rescanStacks 18) = ExecCNFTupleEnumeration.fixedBits h 0
  scratch : ∀ i : Fin 24, i ≠ 0 → i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 22 →
    a.stacks (rescanStacks i) = []

theorem initializeFreshState_stacks (a : State 40 896) :
    (initializeFreshState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  funext i
  by_cases hi : i = rescanStacks 22
  · subst i
    rw [Function.update_self, initializeFreshState_word]
  · simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, clearState]

theorem probePreState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePreState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  rw [probePreState, initializeFreshState_stacks, testAvailableState_stacks a hs]

/-- Preparing a candidate changes only the latch word. The whole fixed local
input projection is then the one used in the proved native rescan theorem. -/
theorem CandidateReady.probe_projection {a : State 40 896} {W : List Bool}
    {rows : List (List (List Bool))} {h : ℕ} {candidate : Fin (2 ^ h)}
    (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change (probePreState a).stacks (rescanStacks i) = _
  rw [probePreState_stacks a hs]
  have hf (j : Fin 24) (hj : j ≠ 22) : rescanStacks j ≠ rescanStacks 22 :=
    fun he => hj (rescanStacks.injective he)
  by_cases h22 : i = 22
  · subst i
    rw [Function.update_self]
    rfl
  rw [Function.update_of_ne (hf i h22)]
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  by_cases h16 : i = 16
  · subst i; exact ready.current
  by_cases h17 : i = 17
  · subst i; exact ready.saved
  by_cases h18 : i = 18
  · subst i; exact ready.predecessor
  rw [ready.scratch i h0 h15 h16 h17 h18 h22]
  fin_cases i <;> simp_all

theorem probe_ready_eval (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    ∃ n ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        8 * (a.stacks remainingPorts.counter).length +
        2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
      Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) :=
  probe_candidate_eval a W rows h B hlen hwidth candidate hs hnonzero
    (ready.probe_projection hs)


noncomputable def advanceCandidateState (a : State 40 896) : State 40 896 :=
  clearState (tupleStacks 3) (advanceState a)

/-- No physical tape outside the two counters and their decrement scratch is
changed by advancement. The increment scratch is restored as well. -/
theorem advanceState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (ht : i ≠ remainingPorts.scratch) :
    (advanceState a).stacks i = a.stacks i := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks i = a.stacks i
  rw [← CounterForPrograms.nextState_outside remainingPorts _ i hr ht]
  rw [Counters.incrementResult_stacks candidatePorts a hs, Function.update_of_ne hc]

theorem advanceCandidate_eval (a : State 40 896)
    (hc : a.stacks candidatePorts.scratch = [])
    (hr : a.stacks remainingPorts.scratch = []) :
    Eval advanceCandidateCommand
      (advanceTime a + 2 * (a.stacks (tupleStacks 3)).length + 3) a
      (advanceCandidateState a) := by
  have he := (advance_eval a hc hr).seq (clearWord_eval (tupleStacks 3) (advanceState a))
  rw [advanceState_outside a hc (tupleStacks 3) (by decide) (by decide) (by decide)] at he
  simpa only [advanceCandidateCommand, advanceCandidateState, Nat.add_assoc] using he

/-- The numeric candidate may reach2^h only at exhaustion. Its retained word
has at mosth+1 bits, and every candidate sent to the scanner has exactlyh. -/
structure CursorWords (a : State 40 896) (h candidate : ℕ) : Prop where
  range : candidate ≤ 2 ^ h
  value : CounterPrograms.value (a.stacks candidatePorts.counter) = candidate
  width : (a.stacks candidatePorts.counter).length ≤ h + 1
  exact : candidate < 2 ^ h →
    a.stacks candidatePorts.counter = ExecCNFTupleEnumeration.fixedBits h candidate
  remaining : a.stacks remainingPorts.counter =
    ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - candidate)
  incrementScratch : a.stacks candidatePorts.scratch = []
  decrementScratch : a.stacks remainingPorts.scratch = []

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem CursorWords.available {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.isZero (a.stacks remainingPorts.counter) = decide (c = 2 ^ h) := by
  have hv := hw.remaining_value
  have hr := hw.range
  by_cases he : c = 2 ^ h
  · simp only [he, decide_true]
    apply (CounterPrograms.isZero_eq_true_iff _).mpr
    rw [hv, he, Nat.sub_self]
  · simp only [he, decide_false]
    apply (CounterPrograms.isZero_eq_false_iff _).mpr
    omega

theorem CursorWords.advance {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) (hc : c < 2 ^ h) :
    CursorWords (advanceCandidateState a) h (c + 1) := by
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by
    rw [hw.remaining_value]
    omega
  have hwidth := advanceState_widths a h hw.incrementScratch hw.width
    (by rw [hw.remaining]; simp) hp (by rw [hw.value, hw.remaining_value]; omega)
  have hcandidate : (advanceCandidateState a).stacks candidatePorts.counter =
      (advanceState a).stacks candidatePorts.counter := by
    exact Function.update_of_ne (by decide : candidatePorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  have hremaining : (advanceCandidateState a).stacks remainingPorts.counter =
      (advanceState a).stacks remainingPorts.counter := by
    exact Function.update_of_ne (by decide : remainingPorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcandidate, advanceState_candidate, CounterPrograms.value_increment, hw.value]
  · rw [hcandidate]
    exact hwidth.1
  · intro hn
    rw [hcandidate]
    exact advanceState_assignment a h ⟨c, hc⟩ (hw.exact hc) hn
  · rw [hremaining]
    exact remaining_word_after_advance a h c hc hw.incrementScratch hw.remaining
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] candidatePorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    rw [advanceState_outside a hw.incrementScratch candidatePorts.scratch
      (by decide) (by decide) (by decide), hw.incrementScratch]
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] remainingPorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    exact CounterForPrograms.nextState_scratch remainingPorts _


section CursorStorage

open SignatureTupleDFS SignatureTupleTraversal

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- These are actual retained controller words at an attained prefix. The
prefix is proof data, while the run stores only the two framed bit stacks. -/
structure AncestorStorage (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (a : State 40 896) : Prop where
  depth_le : depth ≤ levels
  cursors : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors
  representatives : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors
  heads : a.stacks (tupleStacks 6) = List.replicate (levels - depth) true
  address : a.stacks (tupleStacks 9) = List.replicate (base + depth) true
  active : a.regs controllerPorts.active = true

structure ScanStorage (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ)
    (a : State 40 896) : Prop extends
      AncestorStorage h key levels base depth.val ancestors a,
      CursorWords a (h depth.val) candidate where
  leaf : a.regs controllerPorts.leaf = false
  saved : a.stacks (tupleStacks 3) = []
  payload : a.stacks (tupleStacks 4) = []
  predecessor : a.stacks (tupleStacks 8) = List.replicate (h depth.val) false

structure LeafStorage (levels base : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a : State 40 896) : Prop extends
      AncestorStorage h key levels base levels ancestors a where
  leaf : a.regs controllerPorts.leaf = true
  cleared : ∀ i ∈ currentHeadPorts, a.stacks i = []

/-- The same fixed controller state is related to scan, leaf, and halted
semantic cursors. Matrix/cache and accumulator facts are supplied separately
by their concrete program invariants. -/
inductive CursorStorage (levels base : ℕ) : Cursor key levels → State 40 896 → Prop
  | scan {depth ancestors candidate a} :
      ScanStorage h key levels base depth ancestors candidate a →
      CursorStorage levels base (.scan depth ancestors candidate) a
  | leaf {ancestors a} : LeafStorage h key levels base ancestors a →
      CursorStorage levels base (.leaf ancestors) a
  | halt {a} : a.regs controllerPorts.active = false → CursorStorage levels base .halt a

theorem AncestorStorage.frame_bound {levels base depth : ℕ}
    {ancestors : Prefix (Representatives key) depth} {a : State 40 896}
    (ha : AncestorStorage h key levels base depth ancestors a) (hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax) :
    (a.stacks (tupleStacks 0)).length + (a.stacks (tupleStacks 1)).length ≤
      6 * levels * (hmax + 1) := by
  rw [ha.cursors, ha.representatives, Nat.add_comm]
  exact retainedFrames_length_le h key depth levels hmax ancestors ha.depth_le
    (fun d hd => hh d (hd.trans_le ha.depth_le))

/-- Every tuple-control tape at a scan boundary has a uniform polynomial
word bound. In particular no number of completed probes is added to it. -/
theorem ScanStorage.tuple_bound {levels base : ℕ} {depth : Fin levels}
    {ancestors : Prefix (Representatives key) depth.val} {candidate : ℕ} {a : State 40 896}
    (ha : ScanStorage h key levels base depth ancestors candidate a) (hmax matrixBound : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax)
    (hm : (a.stacks (tupleStacks 11)).length ≤ matrixBound) :
    ∀ i : Fin 12, (a.stacks (tupleStacks i)).length ≤
      6 * levels * (hmax + 1) + (base + levels) + (hmax + 1) + matrixBound := by
  have hf := ha.toAncestorStorage.frame_bound h key hmax hh
  have hd := depth.isLt
  have hs := hh depth.val depth.isLt
  have hc := ha.width
  have hr := congrArg List.length ha.remaining
  have ht := ha.incrementScratch
  have he := ha.decrementScratch
  have hn := ha.heads
  have hz := ha.address
  have hp := ha.predecessor
  have hk := ha.saved
  have hb := ha.payload
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hr
  change (a.stacks (tupleStacks 2)).length ≤ h depth.val + 1 at hc
  change (a.stacks (tupleStacks 7)).length = h depth.val + 1 at hr
  intro i
  fin_cases i
  · change (a.stacks (tupleStacks 0)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 1)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 2)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 3)).length ≤ _
    rw [hk]; simp
  · change (a.stacks (tupleStacks 4)).length ≤ _
    rw [hb]; simp
  · change (a.stacks remainingPorts.scratch).length ≤ _
    rw [he]; simp
  · change (a.stacks (tupleStacks 6)).length ≤ _
    rw [hn, List.length_replicate]; omega
  · change (a.stacks (tupleStacks 7)).length ≤ _
    omega
  · change (a.stacks (tupleStacks 8)).length ≤ _
    rw [hp, List.length_replicate]; omega
  · change (a.stacks (tupleStacks 9)).length ≤ _
    rw [hz, List.length_replicate]; omega
  · change (a.stacks candidatePorts.scratch).length ≤ _
    rw [ht]; simp
  · change (a.stacks (tupleStacks 11)).length ≤ _
    omega


end CursorStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
