import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructorSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
abbrev Array (B degree J : ℕ) := {P : List (Coeff B degree) // P.length = J}
def encode {B degree J : ℕ} (P : Array B degree J) : List Bool := DensePolynomialProgram.encode P.1
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

def add {B degree J : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (P Q : Array B degree J) : Array B degree J :=
  ⟨(SubexponentialSAT.SubexpDensePolynomial.addProgram ops P.1 Q.1).1, by
    rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length,P.2,Q.2,Nat.max_self]⟩
def mul {B degree J : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (P Q : Array B degree J) : Array B degree J :=
  ⟨result ops J P.1 Q.1,result_length ops J P.1 Q.1⟩


def zero {B degree : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (J : ℕ) : Array B degree J := ⟨List.replicate J ops.zeroRun.1, by simp⟩
def one {B degree : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (J : ℕ) : Array B degree J :=
  ⟨Constructor.coefficients ops.zeroRun.1 ops.oneRun.1 ops.zeroRun.1 J,
    Constructor.coefficients_length _ _ _ _⟩

noncomputable def denote {B degree J : ℕ} {R : Type*} [CommRing R]
    (ops : SubexponentialSAT.SubexpSymbolicCost.RepresentedRing (Coeff B degree) R)
    (P : Array B degree J) : Polynomial R :=
  SubexponentialSAT.PolynomialAlgorithm.denote (P.1.map ops.decode)

theorem add_denote {B degree J : ℕ} {R : Type*} [CommRing R]
    (ops : SubexponentialSAT.SubexpSymbolicCost.RepresentedRing (Coeff B degree) R)
    (P Q : Array B degree J) :
    denote ops (add ops.program P Q) = denote ops P + denote ops Q :=
  DensePolynomialProgram.add_correct ops P.1 Q.1

theorem mul_denote {B degree J : ℕ} {R : Type*} [CommRing R]
    (ops : SubexponentialSAT.SubexpSymbolicCost.RepresentedRing (Coeff B degree) R)
    (P Q : Array B degree J) :
    denote ops (mul ops.program P Q) = SubexponentialSAT.Truncation.trunc J (denote ops P * denote ops Q) :=
  DensePolynomialProgram.result_correct ops J P.1 Q.1

theorem zero_denote {B degree : ℕ} {R : Type*} [CommRing R]
    (ops : SubexponentialSAT.SubexpSymbolicCost.RepresentedRing (Coeff B degree) R) (J : ℕ) :
    denote ops (zero ops.program J) = 0 := by
  change SubexponentialSAT.PolynomialAlgorithm.denote ((List.replicate J ops.zeroRun.1).map ops.decode) = 0
  rw [List.map_replicate, ops.zero_correct]
  exact SubexponentialSAT.SubexpConvolutionAlgebra.denote_replicate_zero J

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
