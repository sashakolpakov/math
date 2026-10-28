import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingStaging
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionSpec

namespace OAI.Algorithms

/-!
# Actual packing construction in Main storage

The fixed producer receives copied assignment, width, dimension, degree,
scope and alphabet words. Its computed outputs are copied to retained Main
slots, and all local stacks and registers are cleared. The only semantic
input premise identifies those six input words with the producer's input
representation; no packing result or execution is supplied.
-/

namespace SubexponentialSAT.SubexpMainPacking

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master ordinary)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 61
  labels := size Staging.command + 1
  program := Staging.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

def inputs {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : PackingProgram.Input :=
  Staging.inputs ((procedure er alloc).project a)

theorem inputs_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    inputs alloc a = ⟨a.stacks (master alloc 2), a.stacks (master alloc 4),
      a.stacks (master alloc 8), a.stacks (master alloc 7),
      a.stacks (master alloc 0), a.stacks (master alloc 3)⟩ := rfl

variable {U : Type*} [DecidableEq U]

def outputBytes (s : PackingExecution.Spec U) : Fin 6 → List Bool :=
  ![List.replicate s.packing.blockCount true, List.replicate s.packing.leftovers.length true,
    s.metadata, s.addresses, s.storage, s.inverse]

theorem producer_outputs (s : PackingExecution.Spec U) (regs : Fin 16 → Bool) (i : Fin 6) :
    (s.outputState regs).stacks (Staging.outputSource i) = outputBytes s i := by
  fin_cases i <;> rfl

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (s : PackingExecution.Spec U) : Prop where
  outputs : ∀ i, b.stacks (master alloc (outputIndex i)) = outputBytes s i
  inputs : ∀ i, b.stacks (master alloc (inputIndex i)) = a.stacks (master alloc (inputIndex i))
  scratch : ∀ i, b.stacks (lowPort alloc i) = []
  frame : ∀ j, (¬ ∃ i, stackMap alloc i = j) → b.stacks j = a.stacks j
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) (regs : Fin 16 → Bool) :
    Result alloc a ((procedure er alloc).install a
      (Staging.result ((procedure er alloc).project a) (s.outputState regs))) s := by
  let localStart := (procedure er alloc).project a
  let out := Staging.result localStart (s.outputState regs)
  have hp (i : Fin 61) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  constructor
  · intro i
    have h := (hp (outputPort i)).trans
      ((Staging.result_output localStart (s.outputState regs) i).trans (producer_outputs s regs i))
    change ((procedure er alloc).install a out).stacks (stackMap alloc (outputPort i)) = _ at h
    simpa only [stackMap_output] using h
  · intro i
    have h := (hp (inputPort i)).trans (Staging.result_input localStart (s.outputState regs) i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc (inputPort i)) =
      a.stacks (stackMap alloc (inputPort i)) at h
    simpa only [stackMap_input] using h
  · intro i
    refine Fin.addCases (m := 48) (n := 1) (fun j => ?_) (fun j => ?_) i
    · have h := (hp (calleePort j)).trans (Staging.result_work localStart (s.outputState regs) j)
      change ((procedure er alloc).install a out).stacks (stackMap alloc (calleePort j)) = [] at h
      simpa only [stackMap_callee, lowPort, Fin.val_castAdd] using h
    · fin_cases j
      have h := (hp temporary).trans (Staging.result_temporary localStart (s.outputState regs))
      change ((procedure er alloc).install a out).stacks (stackMap alloc temporary) = [] at h
      exact h
  · intro j hj
    exact embedState_stack_frame _ _ _ _ _ hj
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans
      (Staging.result_registers localStart (s.outputState regs) i)
  · intro i hi
    exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

namespace Result

variable {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {s : PackingExecution.Spec U}

theorem blockCount (h : Result alloc a b s) :
    b.stacks (master alloc 15) = List.replicate s.packing.blockCount true := h.outputs 0

theorem leftoverCount (h : Result alloc a b s) :
    b.stacks (master alloc 16) = List.replicate s.packing.leftovers.length true := h.outputs 1

theorem metadata (h : Result alloc a b s) : b.stacks (master alloc 13) = s.metadata := h.outputs 2
theorem addresses (h : Result alloc a b s) : b.stacks (master alloc 17) = s.addresses := h.outputs 3
theorem storage (h : Result alloc a b s) : b.stacks (master alloc 18) = s.storage := h.outputs 4
theorem inverse (h : Result alloc a b s) : b.stacks (master alloc 19) = s.inverse := h.outputs 5

theorem persistent_frame (h : Result alloc a b s) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) :=
  h.frame _ (stackMap_avoids_persistent alloc i)

theorem master_frame (h : Result alloc a b s) (j : Fin 32) (hj : j ∉ writtenMasters) :
    b.stacks (master alloc j) = a.stacks (master alloc j) := by
  by_cases hi : ∃ i, inputIndex i = j
  · obtain ⟨i, rfl⟩ := hi
    exact h.inputs i
  · exact h.frame _ (stackMap_avoids_master alloc j (fun i he => hi ⟨i, he⟩) hj)

theorem work_frame (h : Result alloc a b s) (j : Fin (totalStacks es))
    (hlo : 49 ≤ j.val) (hhi : j.val < 640) : b.stacks j = a.stacks j :=
  h.frame j (stackMap_avoids_middle alloc j hlo hhi)

theorem source_frame (h : Result alloc a b s) (i : Fin 10) :
    b.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) :=
  h.work_frame _ (by simp [ordinary]; omega) (by simp [ordinary]; omega)

theorem threshold_frame (h : Result alloc a b s) (j : Fin (totalStacks es))
    (hstart : alloc.ordinaryCount ≤ j.val) : b.stacks j = a.stacks j := by
  apply h.frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hm := stackMap_val_lt alloc i
  have ha := alloc.enough
  omega

end Result

end SubexponentialSAT.SubexpMainPacking

end OAI.Algorithms
