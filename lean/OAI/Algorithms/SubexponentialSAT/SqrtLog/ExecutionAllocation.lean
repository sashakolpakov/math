import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionProcedure
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProcedure

namespace OAI.Algorithms

/-! Fixed storage for the wide leaf implementation.  Its 768 query stacks
and 128 outer-context stacks occupy a workspace prefix.  Neither the threshold bank nor the 32 persistent
controller stacks is used as a local worker stack.  Input/output transfers
remain separate executable obligations. -/

namespace SubexponentialSAT.SqrtLog.Execution

open StructuredCalls SubexpMainProgram
open SubexpSetupProgram (Config helperSize mainExtraStacks)

def finalExtraRegisters : ℕ := 24

def finalConfig (k T : ℕ) (hk : 2 ≤ k)
    (hT : SparsificationBudgetProgram.Control k T) : Config where
  k := k
  T := T
  extra := 768
  width_ge_two := hk
  control := hT

theorem finalConfig_exists (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : Config, c.k = k ∧ c.extra = 768 := by
  obtain ⟨T,hT⟩ := SparsificationBudgetProgram.exists_control k
  exact ⟨finalConfig k T hk hT,rfl,rfl⟩

theorem final_workRegs : workRegs finalExtraRegisters = 40 := rfl

theorem final_totalRegs : totalRegs finalExtraRegisters = 43 := rfl

theorem finalConfig_leaf_fits (k T : ℕ) (hk : 2 ≤ k)
    (hT : SparsificationBudgetProgram.Control k T) :
    896 < helperSize (finalConfig k T hk hT) := by
  have ho : 16 ≤ SubexpSetupProgram.occurrenceSlots (finalConfig k T hk hT) :=
    ArithmeticExpressionProgram.slots_ge (SparsificationThresholdProgram.occurrenceExpr k)
  unfold helperSize
  change 896 < 128 + SubexpSetupProgram.occurrenceSlots (finalConfig k T hk hT) +
    SubexpSetupProgram.tableSlots (finalConfig k T hk hT) + 768
  omega

namespace WideLeaf

def register : Fin 40 ↪ Fin (workRegs finalExtraRegisters) :=
  ⟨fun i => i,fun _ _ h => h⟩

def stack (c : Config) (hc : 896 < helperSize c) :
    Fin 896 ↪ Fin (totalStacks (mainExtraStacks c)) :=
  ⟨fun i => SubexpSetupProgram.mainStack c (SubexpSetupProgram.workPort c hc i),
    (SubexpSetupProgram.mainStack_injective c).comp
      (SubexpSetupProgram.workPort_injective c hc)⟩

@[simp] theorem stack_val (c : Config) (hc : 896 < helperSize c) (i : Fin 896) :
    (stack c hc i).val = i.val := rfl

theorem stack_lt_helper (c : Config) (hc : 896 < helperSize c) (i : Fin 896) :
    (stack c hc i).val < helperSize c := by
  rw [stack_val]
  exact lt_trans i.isLt hc

theorem stack_ne_threshold (c : Config) (hc : 896 < helperSize c)
    (i : Fin 896) (j : Fin (SubexpSetupProgram.thresholdCount c)) :
    stack c hc i ≠ SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c j) := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = helperSize c + j.val at hv
  have hi := stack_lt_helper c hc i
  rw [stack_val] at hi
  omega

theorem stack_ne_persistent (c : Config) (hc : 896 < helperSize c)
    (i : Fin 896) (j : Fin 32) :
    stack c hc i ≠ persistent (mainExtraStacks c) j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = workStacks (mainExtraStacks c) + j.val at hv
  have hi := stack_lt_helper c hc i
  rw [stack_val] at hi
  unfold workStacks SubexpSetupProgram.mainExtraStacks helperSize at *
  omega

abbrev procedure (c : Config) (hc : 896 < helperSize c)
    (command : Cmd 40 896) (input output : Fin 896) :
    Procedure finalExtraRegisters (mainExtraStacks c) :=
  procedureOfCommand command input output register (stack c hc)

theorem procedure_eval (c : Config) (hc : 896 < helperSize c)
    (command : Cmd 40 896) (input output : Fin 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c))
    {steps : ℕ} {result : StructuredProgram.State 40 896}
    (h : Eval command steps ((procedure c hc command input output).project a) result) :
    Eval (procedure c hc command input output).invoke (steps+1) a
      ((procedure c hc command input output).install a result) :=
  procedureOfCommand_eval command input output register (stack c hc) a h

theorem procedure_persistent_frame (c : Config) (hc : 896 < helperSize c)
    (command : Cmd 40 896) (input output : Fin 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c))
    (result : StructuredProgram.State 40 896) (j : Fin 32) :
    ((procedure c hc command input output).install a result).stacks
        (persistent (mainExtraStacks c) j) = a.stacks (persistent (mainExtraStacks c) j) := by
  apply procedure_install_stack_frame
  rintro ⟨i,hi⟩
  exact stack_ne_persistent c hc i j hi

end WideLeaf
end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
