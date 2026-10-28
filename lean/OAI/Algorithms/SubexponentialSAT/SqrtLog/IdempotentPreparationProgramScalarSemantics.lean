import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarMachine
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramHalf

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
open SubexpLiftRing SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime]

def decode (v : Values p t) : Reg → ZMod (p^t) := fun i=>wordValue p t (v i)

def Op.algebra {A : Type*} [CommRing A] (v : Reg→A) : Op → Reg→A
  | .add o l r => Function.update v o (v l+v r)
  | .mul o l r => Function.update v o (v l*v r)

def algebra {A : Type*} [CommRing A] : List Op → (Reg→A) → Reg→A
  | [],v=>v
  | op::ops,v=>algebra ops (op.algebra v)

theorem decode_op (M : SubexpPreparedQuartic.Modulus p t) (op : Op) (v : Values p t) :
    decode p t (op.eval p t M v)=op.algebra (decode p t v) := by
  cases op with
  | add o l r =>
      funext i
      by_cases hi:i=o
      · subst i; simp [decode,Op.eval,Op.algebra,SubexpPreparedQuartic.wordAdd_correct]
      · simp [decode,Op.eval,Op.algebra,hi]
  | mul o l r =>
      funext i
      by_cases hi:i=o
      · subst i; simp [decode,Op.eval,Op.algebra,SubexpPreparedQuartic.wordMul_correct]
      · simp [decode,Op.eval,Op.algebra,hi]

theorem decode_run (M : SubexpPreparedQuartic.Modulus p t) (ops : List Op) (v : Values p t) :
    decode p t (run p t M ops v)=algebra ops (decode p t v) := by
  induction ops generalizing v with
  | nil=>rfl
  | cons a as ih=>simp only [run,algebra,ih,decode_op]

theorem constants_algebra {A : Type*} [CommRing A] (v : Reg→A)
    (h0:v 0=0) (h1:v 1=1) (hn:v 9 = -1) :
    let w:=algebra constants v
    w 0=0 ∧ w 1=1 ∧ w 2 = -2 ∧ w 3=3 ∧ w 4 = -6 ∧ w 5=7 ∧ w 8=1 ∧ w 9 = -1 := by
  simp [algebra,constants,Op.algebra,h0,h1,hn] ; norm_num

theorem halfStep_algebra {A : Type*} [CommRing A] (v : Reg→A) (hn:v 9 = -1) :
    (algebra halfStep v) 8=3*v 8-1 ∧ (algebra halfStep v) 9 = -1 ∧
    (∀ i:Reg, i≠6 → i≠7 → i≠8 → (algebra halfStep v) i=v i) := by
  constructor
  · simp [algebra,halfStep,Op.algebra,hn]; ring
  constructor
  · simp [algebra,halfStep,Op.algebra,hn]
  · intro i hi6 hi7 hi8
    simp [algebra,halfStep,Op.algebra,hi6,hi7,hi8]

theorem iterate_half (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (h8:decode p t v 8=1) (h9:decode p t v 9 = -1) (n:ℕ) :
    decode p t (iterateForward p t M v n) 8 = IdempotentProgram.halfValue n ∧
    decode p t (iterateForward p t M v n) 9 = -1 ∧
    (∀ i:Reg, i≠6 → i≠7 → i≠8 → decode p t (iterateForward p t M v n) i=decode p t v i) := by
  induction n with
  | zero => exact ⟨h8,h9,fun _ _ _ _=>rfl⟩
  | succ n ih =>
      simp only [iterateForward,decode_run]
      have hh:=halfStep_algebra (decode p t (iterateForward p t M v n)) ih.2.1
      refine ⟨?_,hh.2.1,?_⟩
      · rw [hh.1,ih.1,IdempotentProgram.halfValue]
      · intro i hi6 hi7 hi8
        exact (hh.2.2 i hi6 hi7 hi8).trans (ih.2.2 i hi6 hi7 hi8)

theorem final_algebra {A : Type*} [CommRing A] (v : Reg→A) (hn:v 9 = -1) :
    (algebra finalCoefficients v) 10=2*v 8 ∧
    (algebra finalCoefficients v) 11 = -3*v 8 ∧
    (∀ i:Reg, i≠6 → i≠10 → i≠11 → (algebra finalCoefficients v) i=v i) := by
  constructor
  · simp [algebra,finalCoefficients,Op.algebra,hn]; ring
  constructor
  · simp [algebra,finalCoefficients,Op.algebra,hn]; ring
  · intro i hi6 hi10 hi11
    simp [algebra,finalCoefficients,Op.algebra,hi6,hi10,hi11]

/-- The recurrence is reduced modulo the actual runtime modulus 3^t. -/
theorem half_inverse (M : SubexpPreparedQuartic.Modulus 3 t) (v : Values 3 t)
    (h8:decode 3 t v 8=1) (h9:decode 3 t v 9 = -1) :
    2*decode 3 t (iterateForward 3 t M v t) 8=1 := by
  rw [(iterate_half 3 t M v h8 h9 t).1,IdempotentProgram.twice_halfValue]
  have hz : (3 : ZMod (3^t))^t=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (3^t)
  rw [hz,zero_add]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
