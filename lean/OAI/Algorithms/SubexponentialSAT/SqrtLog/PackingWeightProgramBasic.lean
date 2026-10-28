import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev Data := State 8 13

def work : Fin 5 ↪ Fin 13 where
  toFun i := ⟨i.val + 8, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def ports (i : Fin 4) : Ports 13 where
  left := ![0,6,2,7] i
  right := ![1,6,3,7] i
  out := ![6,4,7,5] i
  work := work
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

abbrev shift : Cmd 8 13 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false)
  (.seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false)
    (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false))

def shifted (d : Data) : Data :=
  ⟨Function.update d.regs 0 false,
    Function.update d.stacks 5 (false :: false :: false :: d.stacks 5)⟩

theorem shift_eval (d : Data) : Eval shift 6 d (shifted d) := by
  let a := SubexponentialSAT.Subexp.TupleProgram.pushedState 5 0 false d
  let b := SubexponentialSAT.Subexp.TupleProgram.pushedState 5 0 false a
  have h := (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false d).seq
    ((SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false a).seq
      (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false b))
  simpa [shift, shifted, a, b, SubexponentialSAT.Subexp.TupleProgram.pushedState] using h

abbrev clear (j : Fin 13) : Cmd 8 13 := .call (SubexponentialSAT.StackRoutines.clearProgram j 0 1)
def cleared (d : Data) (j : Fin 13) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩

theorem clear_eval (d : Data) (j : Fin 13) :
    Eval (clear j) (2 * (d.stacks j).length + 3) d (cleared d j) :=
  .call _ (SubexponentialSAT.ListRegisterProgram.clear_run j 0 1 d.regs d.stacks)

abbrev command : Cmd 8 13 := .seq (multiplyAt (ports 0))
  (.seq (multiplyAt (ports 1)) (.seq (multiplyAt (ports 2))
    (.seq (multiplyAt (ports 3)) (.seq shift (.seq (clear 6) (clear 7))))))

def program := compiled command 0 4

def ready (d : Data) : Prop := ∀ j : Fin 13, 4 ≤ j.val → d.stacks j = []
def inputLength (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length
def incidence (d : Data) : ℕ :=
  SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)^2 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)^2
def head (d : Data) : ℕ :=
  8 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2)^2 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 3)^2

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
