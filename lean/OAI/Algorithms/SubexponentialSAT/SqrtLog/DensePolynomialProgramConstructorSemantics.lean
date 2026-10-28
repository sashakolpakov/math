import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd

namespace OAI.Algorithms

/-! The constructor's bit string is precisely a padded coefficient array. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

def coefficients {C : Type*} (zero low high : C) : ℕ → List C
  | 0 => []
  | 1 => [low]
  | n+2 => low :: high :: List.replicate n zero

@[simp] theorem coefficients_length {C : Type*} (zero low high : C) (J : ℕ) :
    (coefficients zero low high J).length = J := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [coefficients]

private theorem encode_replicate {B degree : ℕ} (z : Coeff B degree)
    (hz : RingProgram.flat z = List.replicate (degree*B) false) (n : ℕ) :
    encode (List.replicate n z) = List.replicate (n*(degree*B)) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,encode_cons,hz,ih,← List.replicate_add]
      congr 1
      ring

theorem encode_coefficients {B degree : ℕ} (zero low high : Coeff B degree)
    (hz : RingProgram.flat zero = List.replicate (degree*B) false) (J : ℕ) :
    encode (coefficients zero low high J) =
      Counter.paddedBits (degree*B) (RingProgram.flat low) (RingProgram.flat high) J := by
  cases J with
  | zero => rfl
  | succ J =>
      cases J with
      | zero => simp [coefficients,Counter.paddedBits]
      | succ n => simp [coefficients,Counter.paddedBits,encode_replicate zero hz n,List.append_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
