import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTernary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramAlgebra

namespace OAI.Algorithms

/-! Executable Newton control over a supplied represented coefficient ring.
The measured counters below charge every callback and seven control events.
They are an intermediate interface, not a primitive bit-runtime certificate;
the supplied callbacks must be refined by actual serialized-array services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

/-- Seven ring callbacks implement `3 e^2 - 2 e^3`, without division. -/
def newtonRun (ops : RingProgram C) (e : C) : C × ℕ :=
  let square := ops.mulRun e e
  let cube := ops.mulRun square.1 e
  let twiceSquare := ops.addRun square.1 square.1
  let threeSquare := ops.addRun twiceSquare.1 square.1
  let twiceCube := ops.addRun cube.1 cube.1
  let minusCube := ops.negRun twiceCube.1
  let out := ops.addRun threeSquare.1 minusCube.1
  (out.1, square.2 + cube.2 + twiceSquare.2 + threeSquare.2 +
    twiceCube.2 + minusCube.2 + out.2 + 7)

@[simp] theorem newtonRun_correct (ops : RepresentedRing C R) (e : C) :
    ops.decode (newtonRun ops.program e).1 = Idempotent.newton (ops.decode e) := by
  simp only [newtonRun, ops.mul_correct,
    ops.add_correct, ops.neg_correct, Idempotent.newton]
  ring

theorem newtonRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (e : C) :
    (newtonRun ops e).2 ≤ 7 * q + 7 := by
  have h₁ := hq.mul e e
  have h₂ := hq.mul (ops.mulRun e e).1 e
  have h₃ := hq.add (ops.mulRun e e).1 (ops.mulRun e e).1
  have h₄ := hq.add (ops.addRun (ops.mulRun e e).1 (ops.mulRun e e).1).1
    (ops.mulRun e e).1
  have h₅ := hq.add (ops.mulRun (ops.mulRun e e).1 e).1
    (ops.mulRun (ops.mulRun e e).1 e).1
  have h₆ := hq.neg (ops.addRun (ops.mulRun (ops.mulRun e e).1 e).1
    (ops.mulRun (ops.mulRun e e).1 e).1).1
  have h₇ := hq.add
    (ops.addRun (ops.addRun (ops.mulRun e e).1 (ops.mulRun e e).1).1
      (ops.mulRun e e).1).1
    (ops.negRun (ops.addRun (ops.mulRun (ops.mulRun e e).1 e).1
      (ops.mulRun (ops.mulRun e e).1 e).1).1).1
  simp only [newtonRun]
  omega

/-- A bounded recursion: exactly `n` Newton steps. -/
def iterateRun (ops : RingProgram C) (e : C) : ℕ → C × ℕ
  | 0 => (e, 1)
  | n + 1 =>
      let prev := iterateRun ops e n
      let out := newtonRun ops prev.1
      (out.1, prev.2 + out.2 + 1)

@[simp] theorem iterateRun_correct (ops : RepresentedRing C R) (e : C) (n : ℕ) :
    ops.decode (iterateRun ops.program e n).1 = Idempotent.iterate (ops.decode e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ops.decode (newtonRun ops.program (iterateRun ops.program e n).1).1 = _
      rw [newtonRun_correct, ih]
      rfl

theorem iterateRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (e : C) (n : ℕ) :
    (iterateRun ops e n).2 ≤ 1 + n * (7 * q + 8) := by
  induction n with
  | zero => simp [iterateRun]
  | succ n ih =>
      have h := newtonRun_cost ops hq (iterateRun ops e n).1
      simp only [iterateRun]
      nlinarith

/-- Runtime iteration count is logarithmic; no unary `t` Newton loop. -/
def liftRun (ops : RingProgram C) (e : C) (t : ℕ) : C × ℕ :=
  iterateRun ops e (Nat.clog 2 t)

theorem liftRun_correct (ops : RepresentedRing C R) (e : C) (t : ℕ) :
    ops.decode (liftRun ops.program e t).1 =
      Idempotent.iterate (ops.decode e) (Nat.clog 2 t) :=
  iterateRun_correct ops e (Nat.clog 2 t)

theorem liftRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (e : C) (t : ℕ) :
    (liftRun ops e t).2 ≤ 1 + Nat.clog 2 t * (7 * q + 8) :=
  iterateRun_cost ops hq e (Nat.clog 2 t)

theorem liftRun_idempotent (ops : RepresentedRing C R) (e : C) (t : ℕ)
    (h : R) (herr : h ∣ (ops.decode e)^2 - ops.decode e) (hnil : h^t = 0) :
    (ops.decode (liftRun ops.program e t).1)^2 =
      ops.decode (liftRun ops.program e t).1 := by
  rw [liftRun_correct]
  exact Idempotent.iterate_idempotent herr hnil (Nat.le_pow_clog (by decide) t)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
