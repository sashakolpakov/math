import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramMul

namespace OAI.Algorithms

/-! Polynomial meanings of the exact coefficient-list outputs. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost

theorem add_correct {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (P Q : List C) :
    SubexponentialSAT.PolynomialAlgorithm.denote ((SubexponentialSAT.SubexpDensePolynomial.addProgram ops.program P Q).1.map ops.decode) =
      SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode) +
        SubexponentialSAT.PolynomialAlgorithm.denote (Q.map ops.decode) := by
  rw [SubexponentialSAT.SubexpDensePolynomial.addProgram_run]
  have h := SubexponentialSAT.SubexpDensePolynomial.addRun_correct ops P Q
  change ((SubexponentialSAT.SubexpDensePolynomial.addRun ops P Q).1.map ops.decode) = _ at h
  rw [h, SubexponentialSAT.PolynomialAlgorithm.denote_add]
  rfl

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
