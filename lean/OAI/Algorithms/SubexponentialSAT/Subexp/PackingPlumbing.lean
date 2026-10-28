import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramSupport

namespace OAI.Algorithms

/-! Verified stack moves used between the fixed packing subroutines. -/

namespace SubexponentialSAT.Subexp.PackingPlumbing

open BitProgram StructuredCalls PackingProgramSupport

inductive Op where
  | copy (src dst tmp : Fin 48)
  | transfer (src dst : Fin 48)
  | clear (src : Fin 48)
  | push (dst : Fin 48) (bit : Bool)

def Op.command : Op → Cmd 16 48
  | .copy src dst tmp => PackingProgramSupport.copy src dst tmp
  | .transfer src dst => PackingProgramSupport.transfer src dst
  | .clear src => PackingProgramSupport.clear src
  | .push dst bit => TupleProgram.pushConst dst 0 bit

def Op.next : Op → Data → Data
  | .copy src dst _, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩
  | .transfer src dst, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩
  | .clear src, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks src a.stacks⟩
  | .push dst bit, a => TupleProgram.pushedState dst 0 bit a

def Op.cost : Op → Data → ℕ
  | .copy src _ _, a => 7 * (a.stacks src).length + 5
  | .transfer src _, a => 3 * (a.stacks src).length + 3
  | .clear src, a => 2 * (a.stacks src).length + 3
  | .push _ _, _ => 2

def Op.Valid : Op → Data → Prop
  | .copy src dst tmp, a => src ≠ dst ∧ src ≠ tmp ∧ tmp ≠ dst ∧ a.stacks tmp = []
  | .transfer src dst, _ => src ≠ dst
  | .clear _, _ => True
  | .push _ _, _ => True

theorem Op.eval (op : Op) (a : Data) (h : op.Valid a) :
    Eval op.command (op.cost a) a (op.next a) := by
  cases op with
  | copy src dst tmp =>
    exact TupleProgram.copy_eval src dst tmp 0 1 h.1 h.2.1 h.2.2.1 (by decide) a h.2.2.2
  | transfer src dst =>
    exact TupleProgram.transfer_eval src dst 0 1 h (by decide) a
  | clear src => exact TupleProgram.clear_eval src 0 1 a
  | push dst bit => exact TupleProgram.pushConst_eval dst 0 bit a

def command : List Op → Cmd 16 48
  | [] => .base .skip
  | op :: ops => .seq op.command (command ops)

def run : List Op → Data → Data
  | [], a => a
  | op :: ops, a => run ops (op.next a)

def cost : List Op → Data → ℕ
  | [], _ => 0
  | op :: ops, a => op.cost a + cost ops (op.next a)

def Valid : List Op → Data → Prop
  | [], _ => True
  | op :: ops, a => op.Valid a ∧ Valid ops (op.next a)

theorem eval (ops : List Op) (a : Data) (h : Valid ops a) :
    Eval (command ops) (cost ops a) a (run ops a) := by
  induction ops generalizing a with
  | nil => exact Eval.base (.skip a)
  | cons op ops ih => exact (op.eval a h.1).seq (ih _ h.2)

/-- Two real transfers preserve the source word's order. -/
def move (src dst tmp : Fin 48) : List Op := [.transfer src tmp, .transfer tmp dst]

end SubexponentialSAT.Subexp.PackingPlumbing

end OAI.Algorithms
