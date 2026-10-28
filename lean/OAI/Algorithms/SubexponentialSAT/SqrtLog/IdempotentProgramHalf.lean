import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

/-- Integral half recurrence: h_0=1, h_(s+1)=3h_s-1. Thus 2h_s=3^s+1. -/
def halfValue : ℕ → A
  | 0 => 1
  | n+1 => 3*halfValue n-1

theorem twice_halfValue (n : ℕ) : (2 : A)*halfValue n = 3^n+1 := by
  induction n with
  | zero => simp [halfValue]; ring
  | succ n ih =>
      rw [halfValue, pow_succ]
      linear_combination 3*ih

/-- This computes the inverse of two modulo 3^t without dividing a natural
number or invoking an inverse oracle. It uses t iterations of four callbacks. -/
def halfRun (ops : RingProgram C) : ℕ → C × ℕ
  | 0 => ops.oneRun
  | n+1 =>
      let prev := halfRun ops n
      let one := ops.oneRun
      let twice := ops.addRun prev.1 prev.1
      let three := ops.addRun twice.1 prev.1
      let minusOne := ops.negRun one.1
      let out := ops.addRun three.1 minusOne.1
      (out.1, prev.2+one.2+twice.2+three.2+minusOne.2+out.2+5)

@[simp] theorem halfRun_correct (ops : RepresentedRing C A) (n : ℕ) :
    ops.decode (halfRun ops.program n).1 = halfValue n := by
  induction n with
  | zero => exact ops.one_correct
  | succ n ih =>
      simp only [RepresentedRing.program] at ih
      simp only [halfRun, RepresentedRing.program, ops.add_correct,
        ops.neg_correct, ops.one_correct, ih, halfValue]
      ring

theorem halfRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (n : ℕ) :
    (halfRun ops n).2 ≤ q+n*(5*q+5) := by
  induction n with
  | zero => simpa [halfRun] using hq.one
  | succ n ih =>
      have h₀ := hq.one
      have h₁ := hq.add (halfRun ops n).1 (halfRun ops n).1
      have h₂ := hq.add (ops.addRun (halfRun ops n).1 (halfRun ops n).1).1
        (halfRun ops n).1
      have h₃ := hq.neg ops.oneRun.1
      have h₄ := hq.add
        (ops.addRun (ops.addRun (halfRun ops n).1 (halfRun ops n).1).1
          (halfRun ops n).1).1 (ops.negRun ops.oneRun.1).1
      simp only [halfRun]
      nlinarith

theorem halfRun_inverse {t : ℕ} (ops : RepresentedRing C (ZMod (3^t))) :
    2*ops.decode (halfRun ops.program t).1 = 1 := by
  rw [halfRun_correct, twice_halfValue]
  have h : (3 : ZMod (3^t))^t = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (3^t)
  rw [h, zero_add]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
