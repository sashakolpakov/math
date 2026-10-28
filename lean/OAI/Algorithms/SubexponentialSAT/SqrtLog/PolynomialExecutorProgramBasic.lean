import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService
import OAI.Algorithms.SubexponentialSAT.SubexpDensePaddingSpec

namespace OAI.Algorithms

/-! Executable coefficient-array meaning of the row postfix interpreter.
Literal padding and all arithmetic operate on stored coefficient words. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

abbrev Coeff (B d : ℕ) := DensePolynomialProgram.Coeff B d

def addValue {C : Type*} (ops : RingProgram C) (P Q : List C) : List C :=
  (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1

def mulValue {C : Type*} (ops : RingProgram C) (J : ℕ) (P Q : List C) : List C :=
  DensePolynomialProgram.result ops J P Q

def loadValue {C : Type*} (ops : RingProgram C) (J : ℕ) (P : List C) : List C :=
  SubexponentialSAT.SubexpDensePaddingSpec.padCells ops.zeroRun.1 J P

def evaluate {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) : List C :=
  SubexponentialSAT.SubexpDensePaddingSpec.evalWith (loadValue ops J) (addValue ops) (mulValue ops J) e

theorem evaluate_eq {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) :
    letI : Add (List C) := ⟨addValue ops⟩
    letI : Mul (List C) := ⟨mulValue ops J⟩
    evaluate ops J e = (e.map (loadValue ops J)).eval := by
  let _ : Add (List C) := ⟨addValue ops⟩
  let _ : Mul (List C) := ⟨mulValue ops J⟩
  induction e with
  | lit P => rfl
  | add e f he hf => exact congrArg₂ (addValue ops) he hf
  | mul e f he hf => exact congrArg₂ (mulValue ops J) he hf

noncomputable def meaning {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (P : List C) : Polynomial R := SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode)

theorem evaluate_correct {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C)) :
    (evaluate ops.program J e).length = J ∧
      meaning ops (evaluate ops.program J e) =
        SubexponentialSAT.Truncation.trunc J ((e.map (meaning ops)).eval) := by
  apply SubexponentialSAT.SubexpDensePaddingSpec.evalWith_correct J (fun P : List C => P.length = J)
    (loadValue ops.program J) (addValue ops.program) (mulValue ops.program J)
    (meaning ops) (meaning ops)
  · intro P
    exact ⟨SubexponentialSAT.SubexpDensePaddingSpec.padCells_length _ _ _,
      SubexponentialSAT.SubexpDensePaddingSpec.denote_padCells ops.decode ops.zeroRun.1 ops.zero_correct J P⟩
  · intro P Q hP hQ
    refine ⟨?_, DensePolynomialProgram.add_correct ops P Q⟩
    change (SubexponentialSAT.SubexpDensePolynomial.addProgram ops.program P Q).1.length = J
    rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length, hP, hQ, Nat.max_self]
  · intro P Q _ _
    exact ⟨DensePolynomialProgram.result_length ops.program J P Q,
      DensePolynomialProgram.result_correct ops J P Q⟩

theorem evaluate_length {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) : (evaluate ops J e).length = J := by
  induction e with
  | lit P => exact SubexponentialSAT.SubexpDensePaddingSpec.padCells_length _ _ _
  | add e f he hf =>
      change (SubexponentialSAT.SubexpDensePolynomial.addProgram ops (evaluate ops J e) (evaluate ops J f)).1.length = J
      rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length, he, hf, Nat.max_self]
  | mul e f he hf => exact DensePolynomialProgram.result_length ops J _ _

/-- No degree restriction on intermediate expressions is required. The final
row degree bound alone restores the complete polynomial. -/
theorem evaluate_full {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C))
    (hdegree : ((e.map (meaning ops)).eval).natDegree < J) :
    meaning ops (evaluate ops.program J e) = (e.map (meaning ops)).eval := by
  rw [(evaluate_correct ops J e).2]
  ext i
  rw [SubexponentialSAT.Truncation.coeff_trunc]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega))).symm

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
