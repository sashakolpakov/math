import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProgram

namespace OAI.Algorithms

/-! The closed post-prefix setup as a real top-level procedure. -/

namespace SubexponentialSAT.SubexpSetupProgram

def mainExtraStacks (c : Config) : ℕ :=
  occurrenceSlots c + tableSlots c + c.extra + thresholdCount c

theorem helperSize_ge (c : Config) : 144 ≤ helperSize c := by
  have h : 16 ≤ occurrenceSlots c :=
    ArithmeticExpressionProgram.slots_ge (SparsificationThresholdProgram.occurrenceExpr c.k)
  unfold helperSize
  omega

theorem mainWorkStacks_ge (c : Config) :
    144 ≤ SubexpMainProgram.workStacks (mainExtraStacks c) := by
  have h := helperSize_ge c
  unfold mainExtraStacks SubexpMainProgram.workStacks helperSize at *
  omega

theorem main_stackCount (c : Config) :
    stackCount c = SubexpMainProgram.totalStacks (mainExtraStacks c) := by
  unfold stackCount helperSize SubexpMainProgram.totalStacks SubexpMainProgram.workStacks mainExtraStacks
  omega

def mainStack (c : Config) (i : Fin (stackCount c)) :
    Fin (SubexpMainProgram.totalStacks (mainExtraStacks c)) := Fin.cast (main_stackCount c) i

theorem mainStack_injective (c : Config) : Function.Injective (mainStack c) := by
  intro i j h
  have hv := congrArg (fun x : Fin (SubexpMainProgram.totalStacks (mainExtraStacks c)) => x.val) h
  exact Fin.ext hv

theorem mainStack_persistent (c : Config) (i : Fin 32) :
    mainStack c (persistent c i) = SubexpMainProgram.persistent (mainExtraStacks c) i := by
  apply Fin.ext
  change helperSize c + thresholdCount c + i.val =
    SubexpMainProgram.workStacks (mainExtraStacks c) + i.val
  unfold SubexpMainProgram.workStacks mainExtraStacks helperSize
  omega

/-- This procedure consumes the retained post-prefix state; it never reads
or strips the raw variable-count header a second time. -/
def mainProcedure (c : Config) (extraRegisters : ℕ) :
    SubexpMainProgram.Procedure extraRegisters (mainExtraStacks c) where
  registers := 16
  stackCount := stackCount c
  labels := StructuredCalls.size (command c) + 1
  program := program c
  register := ⟨fun i => i.castLE (by unfold SubexpMainProgram.workRegs; omega), by
    intro i j h
    have hv := congrArg (fun x : Fin (SubexpMainProgram.workRegs extraRegisters) => x.val) h
    exact Fin.ext hv⟩
  stack := ⟨mainStack c, mainStack_injective c⟩

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
