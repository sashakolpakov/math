import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramCore

namespace OAI.Algorithms

/-! A fixed four-register Newton instruction stream and its exact execution
relation. Registers contain coefficient arrays at the intended instantiation.
This is an arithmetic-register trace, not yet a native Boolean-stack trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

inductive ArithmeticInstruction where
  | add (dst left right : Fin 4)
  | mul (dst left right : Fin 4)
  | neg (dst src : Fin 4)
  deriving DecidableEq, Repr

abbrev Registers (C : Type*) := Fin 4 → C

variable {C R : Type*} [CommRing R]

def instructionRun (ops : RingProgram C) (i : ArithmeticInstruction)
    (state : Registers C) : Registers C × ℕ :=
  match i with
  | .add dst left right =>
      let out := ops.addRun (state left) (state right)
      (Function.update state dst out.1, out.2+1)
  | .mul dst left right =>
      let out := ops.mulRun (state left) (state right)
      (Function.update state dst out.1, out.2+1)
  | .neg dst src =>
      let out := ops.negRun (state src)
      (Function.update state dst out.1, out.2+1)

def codeRun (ops : RingProgram C) : List ArithmeticInstruction → Registers C → Registers C × ℕ
  | [], state => (state, 0)
  | i::is, state =>
      let next := instructionRun ops i state
      let rest := codeRun ops is next.1
      (rest.1, next.2+rest.2)

inductive ArithmeticTrace (ops : RingProgram C) :
    List ArithmeticInstruction → Registers C → Registers C → ℕ → Prop where
  | nil (state) : ArithmeticTrace ops [] state state 0
  | cons {i is state final cost}
      (rest : ArithmeticTrace ops is (instructionRun ops i state).1 final cost) :
      ArithmeticTrace ops (i::is) state final ((instructionRun ops i state).2+cost)

theorem codeRun_trace (ops : RingProgram C) (code : List ArithmeticInstruction)
    (state : Registers C) :
    ArithmeticTrace ops code state (codeRun ops code state).1 (codeRun ops code state).2 := by
  induction code generalizing state with
  | nil => exact .nil state
  | cons i is ih => exact .cons (ih (instructionRun ops i state).1)

theorem instructionRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (i : ArithmeticInstruction) (state : Registers C) :
    (instructionRun ops i state).2 ≤ q+1 := by
  cases i with
  | add dst left right => exact Nat.add_le_add_right (hq.add _ _) 1
  | mul dst left right => exact Nat.add_le_add_right (hq.mul _ _) 1
  | neg dst src => exact Nat.add_le_add_right (hq.neg _) 1

theorem codeRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (code : List ArithmeticInstruction) (state : Registers C) :
    (codeRun ops code state).2 ≤ code.length*(q+1) := by
  induction code generalizing state with
  | nil => simp [codeRun]
  | cons i is ih =>
      have h₁ := instructionRun_cost ops hq i state
      have h₂ := ih (instructionRun ops i state).1
      simp only [codeRun, List.length_cons]
      nlinarith

def newtonCode : List ArithmeticInstruction :=
  [.mul 1 0 0, .mul 2 1 0, .add 3 1 1, .add 3 3 1,
   .add 2 2 2, .neg 2 2, .add 0 3 2]

@[simp] theorem newtonCode_length : newtonCode.length = 7 := rfl

theorem newtonCode_result (ops : RingProgram C) (state : Registers C) :
    (codeRun ops newtonCode state).1 0 = (newtonRun ops (state 0)).1 := by
  simp [codeRun, newtonCode, instructionRun, newtonRun, Function.update]

theorem newtonCode_correct (ops : RepresentedRing C R) (state : Registers C) :
    ops.decode ((codeRun ops.program newtonCode state).1 0) =
      Idempotent.newton (ops.decode (state 0)) := by
  rw [newtonCode_result, newtonRun_correct]

theorem codeRun_append (ops : RingProgram C) (xs ys : List ArithmeticInstruction)
    (state : Registers C) :
    codeRun ops (xs++ys) state =
      ((codeRun ops ys (codeRun ops xs state).1).1,
        (codeRun ops xs state).2+(codeRun ops ys (codeRun ops xs state).1).2) := by
  induction xs generalizing state with
  | nil => simp [codeRun]
  | cons i xs ih =>
      simp only [List.cons_append, codeRun, ih]
      simp only [Nat.add_assoc]

/-- Only the constant seven-instruction block is copied; expressions do not
expand recursively with the Newton iteration count. -/
def liftCode : ℕ → List ArithmeticInstruction
  | 0 => []
  | n+1 => liftCode n ++ newtonCode

@[simp] theorem liftCode_length (n : ℕ) : (liftCode n).length = 7*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liftCode, ih]; omega

theorem liftCode_correct (ops : RepresentedRing C R) (n : ℕ) (state : Registers C) :
    ops.decode ((codeRun ops.program (liftCode n) state).1 0) =
      Idempotent.iterate (ops.decode (state 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftCode, codeRun_append]
      change ops.decode ((codeRun ops.program newtonCode
        (codeRun ops.program (liftCode n) state).1).1 0) = _
      rw [newtonCode_correct, ih]
      rfl

theorem liftCode_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (n : ℕ) (state : Registers C) :
    (codeRun ops (liftCode n) state).2 ≤ 7*n*(q+1) := by
  simpa only [liftCode_length] using codeRun_cost ops hq (liftCode n) state

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

/-- Exact code-word correspondence, independent of any semantic decoder. -/
theorem liftCode_result {C : Type*} (ops : RingProgram C) (n : ℕ) (state : Registers C) :
    (codeRun ops (liftCode n) state).1 0 = (iterateRun ops (state 0) n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftCode, codeRun_append]
      change (codeRun ops newtonCode (codeRun ops (liftCode n) state).1).1 0 = _
      rw [newtonCode_result, ih]
      rfl

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
