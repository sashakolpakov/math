import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramDiagonal

namespace OAI.Algorithms

/-! Constant-size physical diagonal test after classification. The pop is
restored on the nonempty branch, so both unary counters survive literally. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.DiagonalTest

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := SubexponentialSAT.Subexp.MatrixScanProgram.Data

abbrev set (b : Bool) : Cmd 8 23 := .base (.atom (.set 6 b))
def setState (a : Data) (b : Bool) : Data := ⟨Function.update a.regs 6 b,a.stacks⟩
abbrev pop : Cmd 8 23 := .base (.atom (.pop 3 0 1))
def popped (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks 3).head?,Function.update a.stacks 3 (a.stacks 3).tail⟩
abbrev push : Cmd 8 23 := .base (.atom (.push 3 0))
def pushed (a : Data) : Data := ⟨a.regs,Function.update a.stacks 3 (a.regs 0 :: a.stacks 3)⟩
abbrev command : Cmd 8 23 := .ite 7 (.seq pop (.ite 1 (.seq push (set false)) (set true))) (set false)

private theorem set_eval (a : Data) (b : Bool) : Eval (set b) 1 a (setState a b) := .base (.atom _ _)
private theorem pop_eval (a : Data) : Eval pop 1 a (popped a) := .base (.atom _ _)
private theorem push_eval (a : Data) : Eval push 1 a (pushed a) := .base (.atom _ _)

theorem command_eval (a : Data) :
    ∃ t ≤ 5, ∃ e,
      Eval command t a e ∧ e.stacks = a.stacks ∧
      e.regs 6 = diagonalFromScan a ∧ e.regs 7 = a.regs 7 := by
  cases hc : a.regs 7 with
  | false =>
    refine ⟨2,by decide,setState a false,?_,rfl,?_,?_⟩
    · exact .ite_false hc (set_eval a false)
    · simp [setState,diagonalFromScan,hc]
    · simp [setState,hc]
  | true =>
    cases hs : a.stacks 3 with
    | nil =>
      have hflag : (popped a).regs 1 = false := by simp [popped,hs,readRegs]
      refine ⟨4,by decide,setState (popped a) true,?_,?_,?_,?_⟩
      · exact .ite_true hc ((pop_eval a).seq (.ite_false hflag (set_eval (popped a) true)))
      · funext j
        by_cases hj : j = 3 <;> simp [setState,popped,hj,hs]
      · simp [setState,diagonalFromScan,hc,hs]
      · simp [setState,popped,readRegs,hc]
    | cons bit rest =>
      have hflag : (popped a).regs 1 = true := by simp [popped,hs,readRegs]
      refine ⟨5,by decide,setState (pushed (popped a)) false,?_,?_,?_,?_⟩
      · exact .ite_true hc ((pop_eval a).seq (.ite_true hflag
          ((push_eval (popped a)).seq (set_eval (pushed (popped a)) false))))
      · funext j
        by_cases hj : j = 3 <;> simp [setState,pushed,popped,hj,hs,readRegs]
      · simp [setState,diagonalFromScan,hc,hs]
      · simp [setState,pushed,popped,readRegs,hc]

end SubexponentialSAT.SqrtLog.LayoutProgram.DiagonalTest

end OAI.Algorithms
