import OAI.NumberTheory.Quaternion.Arithmetic.TangentBracket
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Matrix Scalar Restriction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarRestriction

noncomputable section

/-! Compatibility between entrywise matrix scalar action and scalar
restriction through the coefficient field. -/

variable {K A : Type*} [NormedField K] [Ring A] {d : ℕ}
  [Algebra (TangentBracket.closedPrimeSubfield K) A]

def matrixAlgHom_primeRestriction
    (f : A →ₐ[TangentBracket.closedPrimeSubfield K] Matrix (Fin d) (Fin d) K) :
    letI : Algebra (TangentBracket.closedPrimeSubfield K) (Matrix (Fin d) (Fin d) K) :=
      Algebra.ofSubsemiring (TangentBracket.closedPrimeSubfield K)
    A →ₐ[TangentBracket.closedPrimeSubfield K] Matrix (Fin d) (Fin d) K :=
  { f.toRingHom with commutes' := f.commutes }

theorem matrixAlgHom_primeRestriction_apply
    (f : A →ₐ[TangentBracket.closedPrimeSubfield K] Matrix (Fin d) (Fin d) K) (a : A) :
    matrixAlgHom_primeRestriction f a = f a := rfl

theorem matrixAlgHom_primeRestriction_isClosedEmbedding [TopologicalSpace A]
    (f : A →ₐ[TangentBracket.closedPrimeSubfield K] Matrix (Fin d) (Fin d) K)
    (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (matrixAlgHom_primeRestriction f) := hf

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarRestriction
