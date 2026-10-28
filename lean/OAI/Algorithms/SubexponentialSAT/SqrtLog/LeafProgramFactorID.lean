import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-! Retain the parsed factor ID and prepare the bare unary counter expected
by the isolated source-row/incidence worker.  Zero is represented by the
empty unary tape; it is not confused with a missing source record. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorID

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 40 768
abbrev command : Cmd 40 768 :=
  .seq (.call (StackRoutines.copyProgram 149 556 359 0 1))
    (.base (.atom (.pop 556 0 1)))

def output (a : Data) (factor : ℕ) : Data :=
  ⟨readRegs (readRegs a.regs 0 1 none) 0 1 (some false),
    Function.update a.stacks 556 (List.replicate factor true)⟩

theorem command_eval (a : Data) (factor : ℕ)
    (hid : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hout : a.stacks 556=[]) (htmp : a.stacks 359=[]) :
    Eval command (7*(factor+1)+6) a (output a factor) := by
  have hc := copy_eval a 149 556 359 0 1
    (by decide) (by decide) (by decide) (by decide) htmp
  let b := afterCopy a 149 556 0 1
  have hs : b.stacks 556=false::List.replicate factor true := by
    simp [b,afterCopy,StackRoutines.copyStacks,hout,hid,Encoding.encodeNat]
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (556 : Fin 768) (0 : Fin 40) 1) b)
  have he : (StructuredProgram.Atom.pop (556 : Fin 768) (0 : Fin 40) 1).eval b=output a factor := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [StructuredProgram.Atom.instr,execInstr,b,afterCopy,
        hid,hout,Encoding.encodeNat]
    · funext i
      by_cases hi : i=556
      · subst i
        simp [StructuredProgram.Atom.instr,execInstr,hs]
      · simp [StructuredProgram.Atom.instr,execInstr,
          b,afterCopy,StackRoutines.copyStacks,hi]
  rw [he] at hp
  convert hc.seq hp using 1
  simp [hid,Encoding.encodeNat]

theorem output_frame (a : Data) (factor : ℕ) (i : Fin 768) (hi : i≠556) :
    (output a factor).stacks i=a.stacks i := by simp [output,hi]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorID

end OAI.Algorithms
