import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def retainedPorts : List (Fin 768) := [659]
def retainedCopies : List (Fin 768 × Fin 768) := [(640,710),(641,711),(642,712)]
def retainCache : Code := .seq (clearMany retainedPorts) (copyMany temporary retainedCopies)
def retainedState (a : Data) : Data := copyManyState retainedCopies (clearManyState retainedPorts a)
def retainCost (a : Data) : ℕ := clearManyCost retainedPorts a +
  copyManyCost retainedCopies (clearManyState retainedPorts a)

theorem retainCache_eval (a : Data) : Eval retainCache (retainCost a) a (retainedState a) := by
  apply (clearMany_eval retainedPorts a).seq
  apply copyMany_eval
  · simp [retainedCopies,temporary]
  · simp [clearMany_stacks,retainedPorts,temporary]


theorem retainedState_positive_append (a : Data) :
    (retainedState a).stacks 710=a.stacks 640++a.stacks 710 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]


theorem retainedState_negative_append (a : Data) :
    (retainedState a).stacks 711=a.stacks 641++a.stacks 711 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]


theorem retainedState_denominator_append (a : Data) :
    (retainedState a).stacks 712=a.stacks 642++a.stacks 712 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]

theorem retainedState_positive (a : Data) (h : a.stacks 710=[]) : (retainedState a).stacks 710=a.stacks 640 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]
theorem retainedState_negative (a : Data) (h : a.stacks 711=[]) : (retainedState a).stacks 711=a.stacks 641 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]
theorem retainedState_denominator (a : Data) (h : a.stacks 712=[]) : (retainedState a).stacks 712=a.stacks 642 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

theorem retainCost_linear (a : Data) : retainCost a=
    2*(a.stacks 659).length+
    7*((a.stacks 640).length+(a.stacks 641).length+(a.stacks 642).length)+18 := by
  simp [retainCost,retainedPorts,retainedCopies,clearManyCost,clearManyState,clearState,
    copyManyCost,copyState,StackRoutines.copyStacks]
  ring

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
