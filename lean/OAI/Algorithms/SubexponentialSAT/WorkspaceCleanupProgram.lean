import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

def finalRegs {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) : Fin r → Bool :=
  match ports with
  | [] => regs
  | _ :: _ => readRegs regs value present none

def finish {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) : State r s :=
  ⟨finalRegs value present ports d.regs, BankRoutines.clearBankStacks ports d.stacks⟩

def command {r s : ℕ} (value present : Fin r) : List (Fin s) → Cmd r s
  | [] => .base .skip
  | port :: rest => .seq (.call (clearProgram port value present)) (command value present rest)

def cost {r s : ℕ} (ports : List (Fin s)) (d : State r s) : ℕ :=
  2 * (ports.map (fun i => (d.stacks i).length)).sum + 3 * ports.length

@[simp] theorem finalRegs_cons {r s : ℕ} (value present : Fin r)
    (port : Fin s) (rest : List (Fin s)) (regs : Fin r → Bool) :
    finalRegs value present (port :: rest) regs = readRegs regs value present none := rfl

theorem finalRegs_after_reset {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) :
    finalRegs value present ports (readRegs regs value present none) =
      readRegs regs value present none := by
  cases ports <;> simp [finalRegs, readRegs_reset]

theorem command_eval {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (d : State r s) :
    Eval (command value present ports) (cost ports d) d (finish value present ports d) := by
  rcases d with ⟨regs, stk⟩
  induction ports generalizing regs stk with
  | nil =>
      simpa [command, cost, finish, finalRegs] using
        (Eval.base (StructuredProgram.Eval.skip (⟨regs, stk⟩ : State r s)))
  | cons port rest ih =>
      have hn := List.nodup_cons.mp hnodup
      have hmap : rest.map (fun i => (clearStacks port stk i).length) =
          rest.map (fun i => (stk i).length) := by
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ port := by
          intro h
          subst i
          exact hn.1 hi
        rw [clearStacks_frame port i stk hne]
      have hfirst := BankRoutines.clear_call_eval port value present regs stk
      have hrest := ih hn.2 (readRegs regs value present none) (clearStacks port stk)
      have hrun := Eval.seq hfirst hrest
      simpa only [command, cost, finish, finalRegs_after_reset, finalRegs_cons,
        List.map_cons, List.sum_cons, List.length_cons, hmap,
        BankRoutines.clearBankStacks_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

theorem command_size {r s : ℕ} (value present : Fin r) (ports : List (Fin s)) :
    size (command value present ports) = 3 * ports.length := by
  induction ports with
  | nil => rfl
  | cons port rest ih =>
      simp [command, size, ih, Nat.mul_add]
      omega

@[simp] theorem finish_stack {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) (i : Fin s) :
    (finish value present ports d).stacks i = if i ∈ ports then [] else d.stacks i := rfl

theorem finish_stack_frame {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) (i : Fin s) (hi : i ∉ ports) :
    (finish value present ports d).stacks i = d.stacks i := by
  simp [hi]

theorem finish_register_frame {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) (i : Fin r) (hv : i ≠ value) (hp : i ≠ present) :
    (finish value present ports d).regs i = d.regs i := by
  cases ports with
  | nil => rfl
  | cons port rest => exact readRegs_frame d.regs value present i none hv hp

def program {r s : ℕ} (value present : Fin r) (ports : List (Fin s)) (input output : Fin s) :=
  compiled (command value present ports) input output

theorem program_trace {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (input output : Fin s) (d : State r s) :
    Trace (program value present ports input output) (cost ports d + 1)
      (d.withPC (some (program value present ports input output).entry))
      ((finish value present ports d).withPC none) :=
  compiled_halt_trace (command_eval value present ports hnodup d) input output

theorem primitive_execution {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (input output : Fin s) (d : State r s) :
    Computation.RunsIn (primitive (program value present ports input output)).step
      (primitiveOverhead (program value present ports input output) * (cost ports d + 1))
      (primitiveCfg (program value present ports input output)
        (d.withPC (some (program value present ports input output).entry)))
      (primitiveCfg (program value present ports input output)
        ((finish value present ports d).withPC none)) :=
  BitProgram.primitive_trace _ (program_trace value present ports hnodup input output d)

theorem selectedBits_le_stackBits {s : ℕ} (ports : List (Fin s)) (hnodup : ports.Nodup)
    (stk : Fin s → List Bool) :
    (ports.map (fun i => (stk i).length)).sum ≤ BitProgram.stackBits stk := by
  rw [← List.sum_toFinset (fun i => (stk i).length) hnodup]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Actual trace growth bounds cleanup without a separate size assumption
for each work array. A concrete instruction allocates at most one new bit. -/
theorem cost_after_runsIn {r s l : ℕ} (p : Program r s l)
    (ports : List (Fin s)) (hnodup : ports.Nodup) {n : ℕ} {a b : Cfg r s l}
    (h : RunsIn p n a b) :
    cost ports (StructuredProgram.State.ofCfg b) + 1 ≤
      2 * (BitProgram.dataBits a + n) + 3 * ports.length + 1 := by
  have hs := selectedBits_le_stackBits ports hnodup b.stacks
  have hv := BitProgram.runsIn_dataBits p h
  dsimp [cost, StructuredProgram.State.ofCfg, BitProgram.dataBits] at *
  omega

/-- An explicit static initial segment of stack ports. -/
def prefixPorts {s : ℕ} (count : ℕ) (hcount : count ≤ s) : List (Fin s) :=
  (List.finRange count).map (Fin.castLE hcount)

theorem prefixPorts_nodup {s : ℕ} (count : ℕ) (hcount : count ≤ s) :
    (prefixPorts count hcount).Nodup :=
  (List.nodup_finRange count).map (Fin.castLE_injective hcount)

@[simp] theorem prefixPorts_length {s : ℕ} (count : ℕ) (hcount : count ≤ s) :
    (prefixPorts count hcount).length = count := by
  simp [prefixPorts]

@[simp] theorem mem_prefixPorts {s : ℕ} (count : ℕ) (hcount : count ≤ s) (i : Fin s) :
    i ∈ prefixPorts count hcount ↔ i.val < count := by
  simp only [prefixPorts, List.mem_map]
  constructor
  · rintro ⟨j, _, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    exact hv ▸ j.isLt
  · intro hi
    refine ⟨⟨i.val, hi⟩, List.mem_finRange _, ?_⟩
    exact Fin.ext rfl

namespace Main

open SubexpMainProgram

abbrev selectedPorts (es count : ℕ) (hcount : count ≤ workStacks es) : List (Fin (totalStacks es)) :=
  prefixPorts count (hcount.trans (Nat.le_add_right _ _))

abbrev value (er : ℕ) : Fin (workRegs er) := ⟨0, by simp [workRegs]⟩
abbrev present (er : ℕ) : Fin (workRegs er) := ⟨1, by dsimp [workRegs]; omega⟩
abbrev ioPort (es : ℕ) : Fin (totalStacks es) := ⟨0, by dsimp [totalStacks, workStacks]; omega⟩

/-- Main procedures automatically place all scratch registers below the
three protected caller-control bits. The stack map is the identity. -/
abbrev procedure (er es count : ℕ) (hcount : count ≤ workStacks es) : Procedure er es where
  registers := workRegs er
  stackCount := totalStacks es
  labels := size (command (value er) (present er) (selectedPorts es count hcount)) + 1
  program := program (value er) (present er) (selectedPorts es count hcount) (ioPort es) (ioPort es)
  register := Function.Embedding.refl _
  stack := Function.Embedding.refl _

def selectedBits {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) : ℕ :=
  ((selectedPorts es count hcount).map (fun i => (a.stacks i).length)).sum

def bound {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) : ℕ := 2 * selectedBits count hcount a + 3 * count + 1

noncomputable def result {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) : MainState er es :=
  (procedure er es count hcount).install a
    (finish (value er) (present er) (selectedPorts es count hcount)
      ((procedure er es count hcount).project a))

theorem execution {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) :
    Eval (procedure er es count hcount).invoke (bound count hcount a) a (result count hcount a) := by
  have ht := program_trace (value er) (present er) (selectedPorts es count hcount)
    (prefixPorts_nodup _ _) (ioPort es) (ioPort es)
    ((procedure er es count hcount).project a)
  have he := Procedure.invoke_trace (procedure er es count hcount) a _ ht
  simpa [bound, selectedBits, cost, selectedPorts, Procedure.project, procedure, result] using he

theorem result_stack {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (i : Fin (totalStacks es)) :
    (result count hcount a).stacks i = if i.val < count then [] else a.stacks i := by
  have hs := embedState_stack (procedure er es count hcount).registerMap
    (procedure er es count hcount).stack a
    (finish (value er) (present er) (selectedPorts es count hcount)
      ((procedure er es count hcount).project a))
    (procedure er es count hcount).stack.injective i
  change (result count hcount a).stacks i =
    (finish (value er) (present er) (selectedPorts es count hcount)
      ((procedure er es count hcount).project a)).stacks i at hs
  rw [hs, finish_stack]
  simp [selectedPorts, Procedure.project, procedure]

theorem result_cleared {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (i : Fin (totalStacks es)) (hi : i.val < count) :
    (result count hcount a).stacks i = [] := by
  simp [result_stack, hi]

theorem result_frame {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (i : Fin (totalStacks es)) (hi : count ≤ i.val) :
    (result count hcount a).stacks i = a.stacks i := by
  simp [result_stack, Nat.not_lt.mpr hi]

theorem result_control {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (i : Fin 3) :
    (result count hcount a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ i

theorem result_persistent {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (i : Fin 32) :
    (result count hcount a).stacks (persistent es i) = a.stacks (persistent es i) := by
  apply result_frame
  change count ≤ workStacks es + i.val
  omega

theorem bound_after_runsIn {er es l : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (p : Program (totalRegs er) (totalStacks es) l) {n : ℕ}
    {a b : MainState er es} {pc pc' : Option (Fin l)}
    (h : RunsIn p n (a.withPC pc) (b.withPC pc')) :
    bound count hcount b ≤ 2 * (BitProgram.stackBits a.stacks + n) + 3 * count + 1 := by
  have hb := cost_after_runsIn p (selectedPorts es count hcount)
    (prefixPorts_nodup _ _) h
  simpa [bound, selectedBits, cost, selectedPorts, BitProgram.dataBits,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC] using hb

end Main
end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
