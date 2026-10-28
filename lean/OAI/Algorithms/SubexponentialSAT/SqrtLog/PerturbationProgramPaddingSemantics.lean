import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramPaddingRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructorSemantics
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost

/-- The bit-level output is the exact homogeneous list of padded constant
polynomials required by the native polynomial Horner consumer. -/
theorem output_encode {B d : ℕ} (zero : Coeff B d)
    (hz : RingProgram.flat zero=List.replicate (d*B) false)
    (D : ℕ) (cs : List (Coeff B d)) :
    output RingProgram.flat D (d*B) cs =
      HornerProgram.encodePolynomial DensePolynomialProgram.encode
        (cs.map fun c => Constructor.coefficients zero c zero D) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [output,List.flatMap_cons,List.map_cons,HornerProgram.encodePolynomial]
      rw [Constructor.encode_coefficients zero c zero hz]
      simp only [cell,hz]
      exact congrArg (_ ++ ·) ih

private theorem denote_zeros {R : Type*} [CommRing R] (n : ℕ) :
    PolynomialAlgorithm.denote (List.replicate n (0:R))=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

/-- Padding does not change the scalar represented by a constant cell. -/
theorem constant_cell_denote {C R : Type*} [CommRing R]
    (decode : C → R) (zero c : C) (hz : decode zero=0) (D : ℕ) (hD : 0 < D) :
    PolynomialAlgorithm.denote ((Constructor.coefficients zero c zero D).map decode) =
      Polynomial.C (decode c) := by
  cases D with
  | zero => omega
  | succ D =>
      cases D with
      | zero => simp [Constructor.coefficients,PolynomialAlgorithm.denote]
      | succ n =>
          simp [Constructor.coefficients,List.map_replicate,hz,
            PolynomialAlgorithm.denote,denote_zeros]

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
