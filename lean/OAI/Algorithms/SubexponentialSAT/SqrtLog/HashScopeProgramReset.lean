import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Reset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Only instantiated at the fixed register inventory of the outer program. -/
def command {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i :: is => .seq (.base (.atom (.set i false))) (command is)

def result {r s : ℕ} (is : List (Fin r)) (a : State r s) : State r s :=
  ⟨fun i => if i ∈ is then false else a.regs i, a.stacks⟩

theorem command_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (command is) is.length a (result is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip _)
  | cons i is ih =>
      let b : State r s := ⟨Function.update a.regs i false,a.stacks⟩
      have hs : Eval (.base (.atom (.set i false))) 1 a b := .base (.atom _ _)
      have he : result is b = result (i::is) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hji : j=i <;> by_cases hj : j ∈ is <;>
            simp [b,hji,hj,Function.update]
        · rfl
      have h := hs.seq (ih b)
      rw [he] at h
      simpa [command,Nat.add_comm] using h

abbrev all {r s : ℕ} : Cmd r s := command (List.finRange r)

theorem all_eval {r s : ℕ} (a : State r s) :
    Eval (all : Cmd r s) r a ⟨fun _ => false,a.stacks⟩ := by
  simpa [all,result] using command_eval (List.finRange r) a

end SubexponentialSAT.SqrtLog.HashScopeProgram.Reset

end OAI.Algorithms
