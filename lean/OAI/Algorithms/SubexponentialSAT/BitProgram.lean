import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StackAdapter

namespace OAI.Algorithms

/-! A first-order finite program language. Unbounded data lives only in Boolean
stacks; every register is one bit and all control labels are fixed finite data. -/

namespace SubexponentialSAT.BitProgram

inductive Instr (r s l : ℕ) where
  | halt
  | goto (next : Fin l)
  | set (dst : Fin r) (value : Bool) (next : Fin l)
  | copy (dst src : Fin r) (next : Fin l)
  | bnot (dst src : Fin r) (next : Fin l)
  | band (dst left right : Fin r) (next : Fin l)
  | bor (dst left right : Fin r) (next : Fin l)
  | bxor (dst left right : Fin r) (next : Fin l)
  | branch (test : Fin r) (yes no : Fin l)
  | push (stack : Fin s) (src : Fin r) (next : Fin l)
  | peek (stack : Fin s) (value present : Fin r) (next : Fin l)
  | pop (stack : Fin s) (value present : Fin r) (next : Fin l)
  deriving DecidableEq, Fintype

structure Program (r s l : ℕ) where
  inputStack : Fin s
  outputStack : Fin s
  entry : Fin l
  code : Fin l → Instr r s l

structure Cfg (r s l : ℕ) where
  pc : Option (Fin l)
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

def readRegs {r : ℕ} (regs : Fin r → Bool) (value present : Fin r)
    (top : Option Bool) : Fin r → Bool :=
  Function.update (Function.update regs value (top.getD false)) present top.isSome

/-- One source instruction performs at most one stack operation. -/
def execInstr {r s l : ℕ} (instr : Instr r s l) (c : Cfg r s l) : Cfg r s l :=
  match instr with
  | .halt => { c with pc := none }
  | .goto next => { c with pc := some next }
  | .set dst value next =>
      { c with pc := some next, regs := Function.update c.regs dst value }
  | .copy dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs src) }
  | .bnot dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (!(c.regs src)) }
  | .band dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a && c.regs b) }
  | .bor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a || c.regs b) }
  | .bxor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a ^^ c.regs b) }
  | .branch test yes no => { c with pc := some (if c.regs test then yes else no) }
  | .push stack src next =>
      { c with pc := some next, «stacks» := Function.update c.stacks stack (c.regs src :: c.stacks stack) }
  | .peek stack value present next =>
      { c with pc := some next, regs := readRegs c.regs value present (c.stacks stack).head? }
  | .pop stack value present next =>
      { pc := some next, regs := readRegs c.regs value present (c.stacks stack).head?, «stacks» := Function.update c.stacks stack (c.stacks stack).tail }

abbrev step {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) : Option (Cfg r s l) :=
  c.pc.map fun label => execInstr (p.code label) c

abbrev initial {r s l : ℕ} (p : Program r s l) (input : List Bool) : Cfg r s l :=
  ⟨some p.entry, fun _ => false, fun stack => if stack = p.inputStack then input else []⟩

/-- A canonical output boundary, for the strong TM2 input/output convention. -/
abbrev terminal {r s l : ℕ} (p : Program r s l) (output : List Bool) : Cfg r s l :=
  ⟨none, fun _ => false, fun stack => if stack = p.outputStack then output else []⟩

abbrev Trace {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.Trace (step p)
abbrev RunsIn {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.RunsIn (step p)

@[simp] theorem step_none {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (h : c.pc = none) : step p c = none := by simp [step, h]

theorem step_code {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (label : Fin l) (instr : Instr r s l) (hp : c.pc = some label)
    (hc : p.code label = instr) : step p c = some (execInstr instr c) := by
  simp [step, hp, hc]

@[simp] theorem readRegs_present {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) :
    readRegs regs value present top present = top.isSome := by
  simp [readRegs]

theorem readRegs_value {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) (h : value ≠ present) :
    readRegs regs value present top value = top.getD false := by
  simp [readRegs, h]

end SubexponentialSAT.BitProgram

end OAI.Algorithms
