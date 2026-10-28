import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramMatrix

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 1

def state (regs : Fin 4 → Bool) (bits : List Bool) : Data := ⟨regs,![bits]⟩
def frame (a b : Bool) : List Bool := [true,a,true,b,false]

abbrev command : Cmd 4 1 :=
  .seq (.base (.atom (.pop 0 0 1)))
    (.seq (.base (.atom (.pop 0 2 1)))
      (.seq (.base (.atom (.pop 0 0 1)))
        (.seq (.base (.atom (.pop 0 3 1))) (.base (.atom (.pop 0 0 1))))))

theorem command_eval (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Eval command 5 (state regs (frame a b++tail)) (state ![false,true,a,b] tail) := by
  let d := state regs (frame a b++tail)
  let d1 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d
  let d2 := (StructuredProgram.Atom.pop (0 : Fin 1) (2 : Fin 4) 1).eval d1
  let d3 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d2
  let d4 := (StructuredProgram.Atom.pop (0 : Fin 1) (3 : Fin 4) 1).eval d3
  let d5 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d4
  have h : Eval command 5 d d5 :=
    (Eval.base (.atom (.pop 0 0 1) d)).seq
      ((Eval.base (.atom (.pop 0 2 1) d1)).seq
        ((Eval.base (.atom (.pop 0 0 1) d2)).seq
          ((Eval.base (.atom (.pop 0 3 1) d3)).seq (Eval.base (.atom (.pop 0 0 1) d4)))))
  have he : d5=state ![false,true,a,b] tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext i
      fin_cases i ; simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
  exact he ▸ h

def program := compiled command 0 0

theorem program_trace (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Trace program 6 ((state regs (frame a b++tail)).withPC (some program.entry))
      ((state ![false,true,a,b] tail).withPC none) :=
  compiled_halt_trace (command_eval regs a b tail) 0 0

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
