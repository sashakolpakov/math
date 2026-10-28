import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramCore
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

def parameterCopies : List (Fin 64 × Fin 64) := [(56,20),(57,21),(58,22),(59,23)]
def addDepth : Code := .seq (TupleProgram.pushConst 34 0 true) (TupleProgram.pushConst 34 0 true)
def finish : Code := .seq addDepth (copyMany 31 parameterCopies)
def finishBudget (outside : Store) :=
  7*((outside 56).length+(outside 57).length+(outside 58).length+(outside 59).length)+24

def readyLocal (regs : Fin 16 → Bool) (r Q n f : ℕ) (pairs nb sb mb rb : List Bool) : State 16 48 :=
  ⟨regs,fun i => if i=20 then nb else if i=21 then sb else if i=22 then mb
    else if i=23 then rb else if i=34 then List.replicate 4 true
    else (AssignmentInitProgram.outputState (context r Q n f pairs)).stacks i⟩

theorem finish_eval (outside : Store) (r Q n f : ℕ) (pairs : List Bool) :
    ∃ rf, Eval finish (finishBudget outside)
      (framed outside (AssignmentInitProgram.outputState (context r Q n f pairs)))
      (framed outside (readyLocal rf r Q n f pairs
        (outside 56) (outside 57) (outside 58) (outside 59))) := by
  let a := framed outside (AssignmentInitProgram.outputState (context r Q n f pairs))
  let b := TupleProgram.pushedState 34 0 true (TupleProgram.pushedState 34 0 true a)
  let e := copyManyState parameterCopies b
  have h1 : Eval addDepth 4 a b :=
    (TupleProgram.pushConst_eval 34 0 true a).seq
      (TupleProgram.pushConst_eval 34 0 true (TupleProgram.pushedState 34 0 true a))
  have h31 : b.stacks 31=[] := by
    simp [b,a,framed_stack,AssignmentInitProgram.outputState,
      AssignmentInitProgram.state]
  have h2 := copyMany_eval 31 parameterCopies b (by
    intro p hp; simp [parameterCopies] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide) h31
  have he : e=framed outside (readyLocal e.regs r Q n f pairs
      (outside 56) (outside 57) (outside 58) (outside 59)) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [readyLocal]
    · funext i
      fin_cases i <;> simp [e,b,a,parameterCopies,copyManyState,copyState,StackRoutines.copyStacks,
        TupleProgram.pushedState,framed_stack,readyLocal,AssignmentInitProgram.outputState,
        AssignmentInitProgram.state,context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
  have hcost : 4+copyManyCost parameterCopies b=finishBudget outside := by
    simp [finishBudget,parameterCopies,copyManyCost,copyState,StackRoutines.copyStacks,
      b,a,TupleProgram.pushedState,framed_stack]
    omega
  have h := h1.seq h2
  change Eval finish _ a e at h
  rw [hcost,he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
