import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! The physical input boundary for assignment-alphabet construction. -/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls

abbrev Data := State 16 48
abbrev Code := Cmd 16 48
abbrev unary (n : ℕ) := List.replicate n true

def inputState (regs : Fin 16 → Bool) (r Q delta D E : ℕ) (pairs : List Bool) : Data :=
  ⟨regs, fun j => if j = 1 then unary r else if j = 2 then unary Q
    else if j = 3 then unary delta else if j = 4 then unary D
    else if j = 5 then unary E else if j = 45 then pairs else []⟩

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
