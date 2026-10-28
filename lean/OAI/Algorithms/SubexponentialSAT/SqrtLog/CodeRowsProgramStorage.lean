import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCode

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def copied (src dst : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩

def cleared (src : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks src []⟩

def pushed (dst : Fin 64) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 b,Function.update d.stacks dst (b::d.stacks dst)⟩

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src≠dst) (hst : src≠24) (htd : (24 : Fin 64)≠dst)
    (htmp : d.stacks 24=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 24 0 1 hsd hst htd (by decide) d htmp

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared src d) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem push_eval (dst : Fin 64) (b : Bool) (d : Data) :
    Eval (push dst b) 2 d (pushed dst b d) :=
  Subexp.TupleProgram.pushConst_eval dst 0 b d

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

theorem cleared_register (src : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (cleared src d).regs i=d.regs i := by
  exact copied_register src src d i hi

theorem pushed_register (dst : Fin 64) (b : Bool) (d : Data) (i : Fin 16)
    (hi : 1 ≤ i.val) : (pushed dst b d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  simp [pushed,h0]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
