import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCacheStorage
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheCleanup
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeInverseCall
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Fixed Main control for the target Lagrange cache

The native command is the exact expression frozen with its producer.  The
wrapper adds physical erasure of old scratch/output and final scratch and
register cleanup.  The trace-lifting lemma below requires an actual native
trace; the semantic Main adapter supplies it from the native correctness
theorem.
-/

namespace SubexponentialSAT.SubexpMainLagrangeCache

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLagrangeCachePreparation (rawStore rawState)

abbrev nativeCommand : Cmd 16 256 :=
  .seq SubexpLagrangeCacheControl.prepare
    (.seq (SubexpLagrangeCacheControl.outerLoop SubexpLagrangeInverseCall.command)
      (.seq SubexpLagrangeCacheControl.reverseCache SubexpLagrangeCacheCleanup.command))

abbrev nativeProgram : Program 16 256 (size nativeCommand + 1) :=
  compiled nativeCommand 206 250

abbrev command : Cmd 16 256 := .seq prepare (.seq (.call nativeProgram) finish)

abbrev localProgram : Program 16 256 (size command + 1) := compiled command 206 250

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 256
  labels := size command + 1
  program := localProgram
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

theorem localInputs_project {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    localInputs ((procedure er alloc).project a) = sourceInputs a := rfl

theorem command_eval (a out : LocalState) (bytes : List Bool) {n : ℕ}
    (ht : Trace nativeProgram n
      ((rawState (localInputs a) (prepared a).regs).withPC (some nativeProgram.entry))
      (out.withPC none))
    (hs : out.stacks = Function.update (rawStore (localInputs a)) 250 bytes) :
    Eval command (prepareCost a + (n + 757)) a (finished out) := by
  have hc : Eval (.call nativeProgram) n (prepared a) out := by
    apply Eval.call
    rw [prepared_rawState a]
    exact ht
  exact (prepare_eval a).seq (hc.seq (finish_eval out (localInputs a) bytes hs))

theorem local_program_trace (a out : LocalState) (bytes : List Bool) {n : ℕ}
    (ht : Trace nativeProgram n
      ((rawState (localInputs a) (prepared a).regs).withPC (some nativeProgram.entry))
      (out.withPC none))
    (hs : out.stacks = Function.update (rawStore (localInputs a)) 250 bytes) :
    Trace localProgram (prepareCost a + (n + 757) + 1)
      (a.withPC (some localProgram.entry)) ((finished out).withPC none) :=
  compiled_halt_trace (command_eval a out bytes ht hs) 206 250

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (bytes : List Bool) : Prop where
  output : b.stacks (master alloc 28) = bytes
  persistent : ∀ i, b.stacks (persistent es i) = a.stacks (persistent es i)
  scratch : ∀ i, inputIndex i = none → i ≠ 250 → b.stacks (stackMap alloc i) = []
  frame : ∀ i, (¬ ∃ j, stackMap alloc j = i) → b.stacks i = a.stacks i
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : LocalState) (bytes : List Bool)
    (hs : out.stacks = Function.update
      (rawStore (localInputs ((procedure er alloc).project a))) 250 bytes) :
    Result alloc a ((procedure er alloc).install a (finished out)) bytes := by
  have he (i : Fin 256) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a (finished out) (procedure er alloc).stack.injective i
  have hf := finished_stacks out (localInputs ((procedure er alloc).project a)) bytes hs
  constructor
  · exact (he 250).trans (by rw [hf]; simp)
  · intro i
    by_cases hm : ∃ j, stackMap alloc j = persistent es i
    · obtain ⟨j, hj⟩ := hm
      obtain ⟨k, rfl, hk⟩ := stackMap_eq_persistent alloc hj
      have ho : inputPort k ≠ 250 := by
        intro h
        have := inputIndex_inputPort k
        rw [h] at this
        cases this
      have hz := he (inputPort k)
      change ((procedure er alloc).install a (finished out)).stacks
        (stackMap alloc (inputPort k)) = (finished out).stacks (inputPort k) at hz
      rw [stackMap_input, hk] at hz
      apply hz.trans
      rw [hf, Function.update_of_ne ho, rawStore_input,
        localInputs_project, sourceInputs_word, hk]
    · exact embedState_stack_frame _ _ _ _ _ hm
  · intro i hi ho
    exact (he i).trans (by rw [hf, Function.update_of_ne ho, rawStore_other _ _ hi])
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans rfl
  · intro i hi
    exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

theorem lift_trace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : LocalState) (bytes : List Bool) {n : ℕ}
    (ht : Trace nativeProgram n
      ((rawState (sourceInputs a) (prepared ((procedure er alloc).project a)).regs).withPC
        (some nativeProgram.entry)) (out.withPC none))
    (hs : out.stacks = Function.update (rawStore (sourceInputs a)) 250 bytes) :
    let b := (procedure er alloc).install a (finished out)
    Eval (procedure er alloc).invoke
      (prepareCost ((procedure er alloc).project a) + (n + 757) + 1) a b ∧
      Result alloc a b bytes := by
  constructor
  · exact Procedure.invoke_trace _ _ _
      (local_program_trace ((procedure er alloc).project a) out bytes ht hs)
  · exact install_result alloc a out bytes hs

theorem Result.work_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {bytes : List Bool} (h : Result alloc a b bytes) (i : Fin (totalStacks es))
    (hwork : i.val < workStacks es) (hrange : i.val < 320 ∨ 576 ≤ i.val)
    (hout : i.val ≠ 668) : b.stacks i = a.stacks i :=
  h.frame i (stackMap_avoids_work alloc i hwork hrange hout)

theorem Result.master_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {bytes : List Bool} (h : Result alloc a b bytes) (i : Fin 32) (hi : i ≠ 28) :
    b.stacks (master alloc i) = a.stacks (master alloc i) := by
  apply h.work_frame
  · exact (SubexpLayoutPorts.master_below_cleanup alloc i).trans_le alloc.within
  · right; simp only [SubexpLayoutPorts.master_val]; omega
  · simp only [SubexpLayoutPorts.master_val]
    have hn : i.val ≠ 28 := fun he => hi (Fin.ext he)
    omega

theorem Result.source_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {bytes : List Bool} (h : Result alloc a b bytes) (i : Fin 10) :
    b.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  apply h.work_frame
  · have hw := alloc.enough.trans alloc.within
    change 128 + i.val < workStacks es
    omega
  · left; change 128 + i.val < 320; omega
  · change 128 + i.val ≠ 668; omega

end SubexponentialSAT.SubexpMainLagrangeCache

end OAI.Algorithms
