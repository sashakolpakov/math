import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramTrace

namespace OAI.Algorithms

/-! Negation through multiplication by a cached negative unit. This permits
the native implementation to use only addition and multiplication services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

def binaryProgram (ops : RingProgram C) (minusOne : C) : RingProgram C :=
  { ops with negRun := fun x => ops.mulRun minusOne x }

def binaryRepresented (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) : RepresentedRing C R :=
  { ops with
    negRun := fun x => ops.mulRun minusOne x
    neg_correct := by intro x; rw [ops.mul_correct, hm]; ring }

@[simp] theorem binaryRepresented_program (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) :
    (binaryRepresented ops minusOne hm).program = binaryProgram ops.program minusOne := rfl

@[simp] theorem binaryRepresented_decode (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) :
    (binaryRepresented ops minusOne hm).decode = ops.decode := rfl

theorem binaryProgram_budget (ops : RingProgram C) (minusOne : C) {q : ℕ}
    (hq : ProgramBudget ops q) : ProgramBudget (binaryProgram ops minusOne) q := by
  exact ⟨hq.zero, hq.one, hq.add, hq.mul, fun x => hq.mul minusOne x⟩

/-- This array is constructed once and cached on the native constant port. -/
def minusOneRun (ops : RingProgram C) (t : ℕ) : (Fin (3*t) → C) × ℕ :=
  RingProgram.negRun ops (oneCode ops t)

theorem minusOneRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    evaluate ops φ t x (minusOneRun ops.program t).1 = -1 := by
  change RingProgram.denote ops φ (hadicBasis t x)
    (RingProgram.negRun ops.program (oneCode ops.program t)).1 = _
  rw [RingProgram.denote_neg]
  exact congrArg Neg.neg (evaluate_one ops φ t x ht)

def binaryArrayProgram (ops : RingProgram C) (t : ℕ) : RingProgram (Fin (3*t) → C) :=
  binaryProgram (arrayProgram ops t) (minusOneRun ops t).1

abbrev binaryArrayRepresented (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) : RepresentedRing (Fin (3*t) → C) R :=
  binaryRepresented (arrayRepresented ops φ t x ht) (minusOneRun ops.program t).1
    (minusOneRun_correct ops φ t x ht)

@[simp] theorem binaryArrayRepresented_program (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    (binaryArrayRepresented ops φ t x ht).program = binaryArrayProgram ops.program t := rfl

/-- The seven-register instruction sequence remains valid when its negation
instruction dispatches to the multiplication service with the cached unit. -/
theorem binaryArrayLift_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate (Idempotent.initialValue (φ (ops.decode u)) x) (Nat.clog 2 t) := by
  have h := liftRun_correct (binaryArrayRepresented ops φ t x ht)
    (initialRun ops.program t u).1 t
  rw [← initialRun_correct ops φ t x ht u]
  change (binaryArrayRepresented ops φ t x ht).decode
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate
      ((binaryArrayRepresented ops φ t x ht).decode (initialRun ops.program t u).1)
      (Nat.clog 2 t) at h
  change (arrayRepresented ops φ t x ht).decode
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate
      ((arrayRepresented ops φ t x ht).decode (initialRun ops.program t u).1)
      (Nat.clog 2 t) at h
  rw [arrayRepresented_decode, arrayRepresented_decode] at h
  exact h

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

theorem binaryArrayLift_indicator [DecidableEq K]
    (ops : RepresentedRing C A) (φ : A →+* R) (ρ : R →+* K)
    (t : ℕ) (u : C) (hu : 2*ops.decode u = 1)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    evaluate ops φ t x
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
      if ρ x = 0 then 1 else 0 := by
  have hH : hValue x^t = 0 := by
    simpa only [Idempotent.eval_ternaryH, hValue] using
      Idempotent.eval_H_nilpotent φ ρ q t hker hq x hx
  rw [binaryArrayLift_correct ops φ t x hH, ← coefficientRun_correct ops φ t x hH]
  exact coefficientRun_indicator ops φ ρ t u hu q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
