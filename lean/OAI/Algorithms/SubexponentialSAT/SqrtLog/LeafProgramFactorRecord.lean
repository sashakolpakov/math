import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorDispatchFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorFinish

namespace OAI.Algorithms

/-! Actual parser-state restoration for the factor callback and the direct
neutral-factor branch. Neutral IDs never invoke source or arithmetic code. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

def returned (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 13 false) 14 true) 15 false,a.stacks⟩

theorem returnToRecords_eval (a : Data) : Eval returnToRecords 3 a (returned a) := by
  let b : Data := ⟨Function.update a.regs 13 false,a.stacks⟩
  let c : Data := ⟨Function.update b.regs 14 true,a.stacks⟩
  have h1 : Eval (.base (.atom (.set 13 false))) 1 a b := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 14 true))) 1 b c := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.set 15 false))) 1 c (returned a) := .base (.atom _ _)
  exact h1.seq (h2.seq h3)

def callbackFinished (a : Data) : Data := returned (cleared a 149)

theorem callbackFinish_eval (a : Data) :
    Eval (.seq (clear 149) returnToRecords) (2*(a.stacks 149).length+6) a (callbackFinished a) := by
  have h := (clear_eval a 149).seq (returnToRecords_eval (cleared a 149))
  change Eval (.seq (clear 149) returnToRecords) (2*(a.stacks 149).length+6) a
    (returned (cleared a 149))
  simpa [Nat.add_assoc] using h

@[simp] theorem callbackFinished_stacks (a : Data) :
    (callbackFinished a).stacks=Function.update a.stacks 149 [] := rfl
@[simp] theorem callbackFinished_tag (a : Data) : (callbackFinished a).regs 13=false := by
  simp [callbackFinished,returned]
@[simp] theorem callbackFinished_present (a : Data) : (callbackFinished a).regs 14=true := by
  simp [callbackFinished,returned]
@[simp] theorem callbackFinished_found (a : Data) : (callbackFinished a).regs 15=false := by
  simp [callbackFinished,returned]

theorem choose_neutral_eval (a : Data) (h5 : a.regs 5=false) (h6 : a.regs 6=false) :
    Eval choose 2 a a :=
  Eval.ite_false h5 (Eval.ite_false h6 (Eval.base (StructuredProgram.Eval.skip a)))

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
