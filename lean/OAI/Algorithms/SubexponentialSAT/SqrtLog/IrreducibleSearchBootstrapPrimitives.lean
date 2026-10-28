import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Fixed word loading and framed stack routines for the search bootstrap. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls

abbrev Data := State 22 28

abbrev copyCmd (src dst : Fin 28) : Cmd 22 28 :=
  .call (StackRoutines.copyProgram src dst 7 0 1)

theorem copyCmd_eval (src dst : Fin 28) (a : Data)
    (hsd : src ≠ dst) (hs7 : src ≠ 7) (h7d : (7 : Fin 28) ≠ dst)
    (h7 : a.stacks 7 = []) :
    Eval (copyCmd src dst) (7 * (a.stacks src).length + 5) a
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks dst (a.stacks src ++ a.stacks dst)⟩ := by
  exact Subexp.TupleProgram.copy_eval src dst 7 0 1 hsd hs7 h7d (by decide) a h7

abbrev clearCmd (src : Fin 28) : Cmd 22 28 :=
  .call (StackRoutines.clearProgram src 0 1)

theorem clearCmd_eval (src : Fin 28) (a : Data) :
    Eval (clearCmd src) (2 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩ := by
  exact Subexp.TupleProgram.clear_eval src 0 1 a

/-- The bits here are part of the finite command, never runtime advice. -/
def pushWord (dst : Fin 28) : List Bool → Cmd 22 28
  | [] => .base .skip
  | b :: bs => .seq (pushWord dst bs) (Subexp.TupleProgram.pushConst dst 0 b)

theorem pushWord_eval (dst : Fin 28) (bits : List Bool) (a : Data) :
    ∃ rf, Eval (pushWord dst bits) (2 * bits.length) a
      ⟨rf, Function.update a.stacks dst (bits ++ a.stacks dst)⟩ := by
  induction bits generalizing a with
  | nil =>
      refine ⟨a.regs, ?_⟩
      have hs := Function.update_eq_self dst a.stacks
      simpa [pushWord, hs] using Eval.base (StructuredProgram.Eval.skip a)
  | cons b bs ih =>
      obtain ⟨rf, h⟩ := ih a
      have hp := Subexp.TupleProgram.pushConst_eval dst (0 : Fin 22) b
        (⟨rf, Function.update a.stacks dst (bs ++ a.stacks dst)⟩ : Data)
      refine ⟨Function.update rf 0 b, ?_⟩
      simpa [pushWord, Subexp.TupleProgram.pushedState, Nat.mul_add,
        Nat.add_assoc] using h.seq hp

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
