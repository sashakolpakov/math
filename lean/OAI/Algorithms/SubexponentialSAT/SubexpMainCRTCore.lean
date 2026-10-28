import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose
import OAI.Algorithms.SubexponentialSAT.SubexpMainDecode
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# CRT preparation and storage in the Main allocation

The CRT bank occupies ordinary 320..639. Three redirected I/O ports leave
three holes, used by the preparation routine's temporaries. Retained inputs
are read through copies. The epilogue clears the five low scratch stacks used
by the final decoder, with an actual measured program.

This module checks preparation, allocation, and the final scratch cleanup
independently of the larger CRT arithmetic controller.
-/

namespace SubexponentialSAT.SubexpMainCRT

open BitProgram StructuredCalls SubexpMainProgram

structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 640 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

def ordinary {es : ℕ} (alloc : Allocation es) (i : Fin 640) : Fin (totalStacks es) :=
  ⟨i.val, by have := alloc.enough; have := alloc.within; dsimp [totalStacks]; omega⟩

def inputIndex : Fin 7 → Fin 32 := ![12, 13, 14, 29, 30, 31, 19]

def highPort {es : ℕ} (alloc : Allocation es) : Fin 10 → Fin (totalStacks es) :=
  ![persistent es 12, persistent es 13, persistent es 14, persistent es 29,
    persistent es 30, persistent es 31, persistent es 19,
    ordinary alloc 256, ordinary alloc 265, persistent es 10]

theorem highPort_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (highPort alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hb := alloc.enough.trans alloc.within
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [highPort, ordinary, persistent] at hv <;> omega

theorem highPort_range {es : ℕ} (alloc : Allocation es) (i : Fin 10) :
    (highPort alloc i).val < 320 ∨ workStacks es ≤ (highPort alloc i).val := by
  fin_cases i <;> norm_num [highPort, ordinary, persistent, Fin.coe_ofNat_eq_mod]

theorem highPort_lower_bound {es : ℕ} (alloc : Allocation es) (i : Fin 10) :
    256 ≤ (highPort alloc i).val := by
  have hb := alloc.enough.trans alloc.within
  fin_cases i <;> simp [highPort, ordinary, persistent] <;> omega

def baseMap {es : ℕ} (alloc : Allocation es) (i : Fin 330) : Fin (totalStacks es) :=
  if hi : i.val < 320 then ordinary alloc ⟨320 + i.val, by omega⟩
  else highPort alloc ⟨i.val - 320, by omega⟩

theorem baseMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (baseMap alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hb := alloc.enough.trans alloc.within
  by_cases hi : i.val < 320 <;> by_cases hj : j.val < 320
  · apply Fin.ext
    simp only [baseMap, dite_eq_left hi, dite_eq_left hj, ordinary] at hv
    omega
  · have hr := highPort_range alloc ⟨j.val - 320, by omega⟩
    simp only [baseMap, dite_eq_left hi, dite_eq_right hj, ordinary] at hv
    omega
  · have hr := highPort_range alloc ⟨i.val - 320, by omega⟩
    simp only [baseMap, dite_eq_right hi, dite_eq_left hj, ordinary] at hv
    omega
  · have he := highPort_injective alloc (by
      simpa only [baseMap, dite_eq_right hi, dite_eq_right hj] using h)
    have hv' := congrArg Fin.val he
    apply Fin.ext
    dsimp only at hv'
    omega

def permutation : Fin 330 ≃ Fin 330 :=
  ((Equiv.swap 256 327).trans (Equiv.swap 265 328)).trans (Equiv.swap 261 329)

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 330) : Fin (totalStacks es) :=
  baseMap alloc (permutation i)

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) :=
  (baseMap_injective alloc).comp permutation.injective

@[simp] theorem stackMap_nodes {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 256 = ordinary alloc 256 := rfl

@[simp] theorem stackMap_jets {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 265 = ordinary alloc 265 := rfl

@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 261 = persistent es 10 := rfl

@[simp] theorem stackMap_input {es : ℕ} (alloc : Allocation es) (i : Fin 7) :
    stackMap alloc (SubexpCRTPreparation.inputPort i) = persistent es (inputIndex i) := by
  fin_cases i <;> rfl

theorem stackMap_lower_bound {es : ℕ} (alloc : Allocation es) (i : Fin 330) :
    256 ≤ (stackMap alloc i).val := by
  have hb := alloc.enough.trans alloc.within
  unfold stackMap baseMap
  split
  · simp only [ordinary]
    omega
  · exact highPort_lower_bound alloc _

def register (er : ℕ) : Fin 16 ↪ Fin (workRegs er) :=
  ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩

def preparation (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 330
  labels := size SubexpCRTPreparation.command + 1
  program := SubexpCRTPreparation.program
  register := register er
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

noncomputable def preparedData {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  (preparation er alloc).install a
    (SubexpCRTPreparation.result ((preparation er alloc).project a))

def projectCRT {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    StructuredProgram.State 16 320 :=
  ⟨a.regs ∘ (preparation er alloc).registerMap,
    fun i => a.stacks (stackMap alloc (i.castAdd 10))⟩

def preparationBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpCRTPreparation.runtimeBound ((preparation er alloc).project a)

theorem local_preparationBound_le (a : SubexpCRTPreparation.Data) :
    SubexpCRTPreparation.runtimeBound a ≤
      1100 * (BitProgram.stackBits a.stacks + 1) +
        CounterConversions.runtimeBound (a.stacks 326) := by
  let W := BitProgram.stackBits a.stacks
  have ha : SubexpPreparedSetupCalls.StackBound a W := by
    intro i
    change (a.stacks i).length ≤ Finset.sum Finset.univ (fun j : Fin 330 => (a.stacks j).length)
    exact Finset.single_le_sum (fun (j : Fin 330) _ => Nat.zero_le (a.stacks j).length)
      (Finset.mem_univ i)
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le
    [SubexpCRTPreparation.copyTemporary] a ha
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le SubexpCRTPreparation.clearPorts
    (SubexpSetupStorage.clearManyState [SubexpCRTPreparation.copyTemporary] a)
    (SubexpPreparedSetupCalls.clearMany_bound _ _ ha)
  have h3 := SubexpPreparedSetupCalls.copyManyCost_le SubexpCRTPreparation.copies
    (SubexpSetupStorage.beforeCopies SubexpCRTPreparation.copyTemporary
      SubexpCRTPreparation.clearPorts a)
    (fun q _ => SubexpPreparedSetupCalls.beforeCopies_bound _ _ a ha q.1)
    SubexpCRTPreparation.copies_separated
  have hlen : SubexpCRTPreparation.clearPorts.length ≤ 330 := by
    simpa only [SubexpCRTPreparation.clearPorts, List.length_finRange] using
      List.length_filter_le (fun i => decide (SubexpCRTPreparation.NeedsClear i))
        (List.finRange 330)
  have h2' := h2.trans (Nat.mul_le_mul_right (2 * W + 3) hlen)
  simp only [List.length_singleton, one_mul] at h1
  have hc : SubexpCRTPreparation.copies.length = 9 := rfl
  rw [hc] at h3
  change SubexpSetupStorage.prepareCost SubexpCRTPreparation.copyTemporary
    SubexpCRTPreparation.clearPorts SubexpCRTPreparation.copies a +
      CounterConversions.runtimeBound (a.stacks 326) + 17 ≤ _
  unfold SubexpSetupStorage.prepareCost
  change _ ≤ 1100 * (W + 1) + _
  omega

/-- The size term counts only the330 selected words, excluding the pending
leaf stream and the protected source/threshold caches. -/
theorem preparationBound_le {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    preparationBound alloc a ≤
      1100 * (BitProgram.stackBits ((preparation er alloc).project a).stacks + 1) +
        CounterConversions.runtimeBound (a.stacks (persistent es 19)) := by
  have h := local_preparationBound_le ((preparation er alloc).project a)
  have hi := stackMap_input alloc (6 : Fin 7)
  change stackMap alloc 326 = persistent es 19 at hi
  change preparationBound alloc a ≤
    1100 * (BitProgram.stackBits ((preparation er alloc).project a).stacks + 1) +
      CounterConversions.runtimeBound (a.stacks (stackMap alloc 326)) at h
  rw [hi] at h
  exact h

theorem preparation_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ∃ n ≤ preparationBound alloc a,
      Eval (preparation er alloc).invoke n a (preparedData alloc a) := by
  obtain ⟨n, hn, ht⟩ := SubexpCRTPreparation.program_runs ((preparation er alloc).project a)
  exact ⟨n, hn, Procedure.invoke_trace _ _ _ ht⟩

/-- The exact local320 entry state, with every register reset. The remaining
stack values are governed by the preparation routine's copied/unary/empty
postconditions; no unproved CRT entry-state assumption is inserted. -/
theorem prepared_entry {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    projectCRT alloc (preparedData alloc a) =
      ⟨fun _ => false, fun i =>
        (SubexpCRTPreparation.result ((preparation er alloc).project a)).stacks
          (i.castAdd 10)⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact (embedState_register (preparation er alloc).registerMap (preparation er alloc).stack
      a (SubexpCRTPreparation.result ((preparation er alloc).project a))
      (preparation er alloc).registerMap_injective i).trans
        (SubexpCRTPreparation.result_registers _ i)
  · funext i
    exact embedState_stack (preparation er alloc).registerMap (preparation er alloc).stack
      a (SubexpCRTPreparation.result ((preparation er alloc).project a))
      (preparation er alloc).stack.injective (i.castAdd 10)

theorem prepared_low_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hi : i.val < 256) :
    (preparedData alloc a).stacks i = a.stacks i := by
  apply embedState_stack_frame (preparation er alloc).registerMap (preparation er alloc).stack
    a (SubexpCRTPreparation.result ((preparation er alloc).project a)) i
  rintro ⟨j, hj⟩
  have hl := stackMap_lower_bound alloc j
  have hv := congrArg Fin.val hj
  change (stackMap alloc j).val = i.val at hv
  omega

theorem prepared_word {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (q : Fin 330 × Fin 330) (hq : q ∈ SubexpCRTPreparation.copies)
    (hb : q.2 ≠ SubexpCRTPreparation.binaryCopy) :
    (preparedData alloc a).stacks (stackMap alloc q.2) = a.stacks (stackMap alloc q.1) := by
  have h := embedState_stack (preparation er alloc).registerMap (preparation er alloc).stack
    a (SubexpCRTPreparation.result ((preparation er alloc).project a))
    (preparation er alloc).stack.injective q.2
  exact h.trans (SubexpCRTPreparation.result_word _ q hq hb)

theorem prepared_unary {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (preparedData alloc a).stacks (stackMap alloc 243) =
      List.replicate (CounterPrograms.value (a.stacks (persistent es 19))) true := by
  have h := embedState_stack (preparation er alloc).registerMap (preparation er alloc).stack
    a (SubexpCRTPreparation.result ((preparation er alloc).project a))
    (preparation er alloc).stack.injective (243 : Fin 330)
  have hc := h.trans (SubexpCRTPreparation.result_unary ((preparation er alloc).project a))
  change (preparedData alloc a).stacks (stackMap alloc 243) =
    List.replicate (CounterPrograms.value (a.stacks (stackMap alloc 326))) true at hc
  have hi := stackMap_input alloc (6 : Fin 7)
  change stackMap alloc 326 = persistent es 19 at hi
  rw [hi] at hc
  exact hc

def decoderIndex : Fin 5 → Fin 640 := ![1, 2, 3, 4, 6]

theorem decoderIndex_injective : Function.Injective decoderIndex := by decide

def decoderScratch {es : ℕ} (alloc : Allocation es) (i : Fin 5) : Fin (totalStacks es) :=
  ordinary alloc (decoderIndex i)

theorem decoderScratch_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (decoderScratch alloc) := by
  intro i j h
  apply decoderIndex_injective
  exact Fin.ext (congrArg (fun k : Fin (totalStacks es) => k.val) h)

def scratchPorts : List (Fin 5) := [0, 1, 2, 3, 4]
abbrev scratchCommand : Cmd 16 5 := SubexpSetupStorage.clearMany scratchPorts
def scratchProgram := compiled scratchCommand (0 : Fin 5) 0

def epilogue (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 5
  labels := size scratchCommand + 1
  program := scratchProgram
  register := register er
  stack := ⟨decoderScratch alloc, decoderScratch_injective alloc⟩

def epilogueBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  SubexpSetupStorage.clearManyCost scratchPorts ((epilogue er alloc).project a) + 1

noncomputable def finalData {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  (epilogue er alloc).install a
    (SubexpSetupStorage.clearManyState scratchPorts ((epilogue er alloc).project a))

theorem epilogue_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Eval (epilogue er alloc).invoke (epilogueBound alloc a) a (finalData alloc a) := by
  apply Procedure.invoke_trace
  exact compiled_halt_trace (SubexpSetupStorage.clearMany_eval scratchPorts
    ((epilogue er alloc).project a)) 0 0

theorem finalData_scratch {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 5) : (finalData alloc a).stacks (decoderScratch alloc i) = [] := by
  let d : SubexpSetupStorage.Data 5 := (epilogue er alloc).project a
  have h := embedState_stack (epilogue er alloc).registerMap (epilogue er alloc).stack a
    (SubexpSetupStorage.clearManyState scratchPorts d)
    (epilogue er alloc).stack.injective i
  have hi : i ∈ scratchPorts := by fin_cases i <;> simp [scratchPorts]
  have hc : (SubexpSetupStorage.clearManyState scratchPorts d).stacks i = [] := by
    rw [SubexpSetupStorage.clearMany_stacks, ite_eq_left hi]
  exact h.trans hc

def scratchBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  (a.stacks (ordinary alloc 1)).length + (a.stacks (ordinary alloc 2)).length +
    (a.stacks (ordinary alloc 3)).length + (a.stacks (ordinary alloc 4)).length +
    (a.stacks (ordinary alloc 6)).length

theorem epilogueBound_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    epilogueBound alloc a = 2 * scratchBits alloc a + 16 := by
  have hs (i : Fin 5) : ((epilogue er alloc).project a).stacks i =
      a.stacks (decoderScratch alloc i) := rfl
  simp [epilogueBound, scratchPorts, SubexpSetupStorage.clearManyCost,
    SubexpSetupStorage.clearState, hs, decoderScratch, decoderIndex, scratchBits]
  omega

theorem finalData_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hi : ¬ ∃ j, decoderScratch alloc j = i) :
    (finalData alloc a).stacks i = a.stacks i :=
  embedState_stack_frame (epilogue er alloc).registerMap (epilogue er alloc).stack a
    (SubexpSetupStorage.clearManyState scratchPorts ((epilogue er alloc).project a)) i hi

theorem finalData_high_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hi : 7 ≤ i.val) :
    (finalData alloc a).stacks i = a.stacks i := by
  apply finalData_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  fin_cases j <;> simp [decoderScratch, decoderIndex, ordinary] at hv <;> omega

/-- The five physical clears establish the decoder's full scratch premise;
the polynomial and retained context remain the actual words present on tape. -/
theorem decoder_ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (SubexpMainDecode.procedure er es).project (finalData alloc a) =
      SubexpFlatCount.start
        ((SubexpMainDecode.procedure er es).project (finalData alloc a)).regs
        ((finalData alloc a).stacks (persistent es 12))
        ((finalData alloc a).stacks (persistent es 13))
        ((finalData alloc a).stacks (persistent es 10)) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i
    · rfl
    · exact finalData_scratch alloc a (0 : Fin 5)
    · exact finalData_scratch alloc a (1 : Fin 5)
    · exact finalData_scratch alloc a (2 : Fin 5)
    · exact finalData_scratch alloc a (3 : Fin 5)
    · rfl
    · exact finalData_scratch alloc a (4 : Fin 5)
    · rfl

end SubexponentialSAT.SubexpMainCRT

end OAI.Algorithms
