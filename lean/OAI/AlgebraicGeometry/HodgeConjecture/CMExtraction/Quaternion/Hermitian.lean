import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.UnitaryMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Hermitian -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Hermitian

noncomputable section

/-! The explicit quaternion matrices preserve the binary Hermitian form
up to their reduced norm. Norm-one elements therefore act by genuine
special unitary matrices. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

section Binary
variable {E : Type*} [CommRing E] [StarRing E]

def binaryHermitianForm (b : E) : Matrix (Fin 2) (Fin 2) E := !![1, 0; 0, b]

def binaryUnitaryMatrix (b x y : E) : Matrix (Fin 2) (Fin 2) E :=
  !![x, -b * y; star y, star x]

theorem binaryUnitaryMatrix_gram (b : E) (hb : star b = b) (x y : E) :
    (binaryUnitaryMatrix b x y).conjTranspose * binaryHermitianForm b * binaryUnitaryMatrix b x y =
      (binaryUnitaryMatrix b x y).det • binaryHermitianForm b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryUnitaryMatrix, binaryHermitianForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.det_fin_two, hb] <;> ring

end Binary

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [StarRing E]
  (a b : F) (δ : E) (hδ : δ ^ 2 = algebraMap F E a)
  (hreal : ∀ t : F, star (algebraMap F E t) = algebraMap F E t)
  (hstar : star δ = -δ)

include hreal hstar

theorem unitaryQuaternionMap_binary (q : ℍ[F,a,-b]) :
    UnitaryMatrix.unitaryQuaternionMap a b δ hδ q = binaryUnitaryMatrix (algebraMap F E b)
      (algebraMap F E q.re + δ * algebraMap F E q.imI)
      (algebraMap F E q.imJ + δ * algebraMap F E q.imK) := by
  rw [UnitaryMatrix.unitaryQuaternionMap_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryUnitaryMatrix, hreal, hstar] <;> ring

theorem unitaryQuaternionMap_gram (q : ℍ[F,a,-b]) :
    (UnitaryMatrix.unitaryQuaternionMap a b δ hδ q).conjTranspose * binaryHermitianForm (algebraMap F E b) *
      UnitaryMatrix.unitaryQuaternionMap a b δ hδ q =
      algebraMap F E (NumberTheory.Quaternion.Arithmetic.Norm.quaternionNorm a (-b) q) • binaryHermitianForm (algebraMap F E b) := by
  rw [← UnitaryMatrix.unitaryQuaternionMap_det a b δ hδ q, unitaryQuaternionMap_binary a b δ hδ hreal hstar q]
  exact binaryUnitaryMatrix_gram _ (hreal b) _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Hermitian
