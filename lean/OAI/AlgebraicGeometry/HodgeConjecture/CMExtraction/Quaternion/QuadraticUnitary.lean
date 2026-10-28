import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SpecialLinear
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv
import OAI.Geometry.ComplexBall.Generation

/-! # Quadratic Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary

noncomputable section

section

/-! Embed the binary norm-one quaternion group in the (0,2) coordinates
of the native rank-three Hermitian form diag(1,1,b). -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic

variable {E : Type*} [CommRing E]

def activeBinaryMatrix (A : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin 3) (Fin 3) E :=
  !![A 0 0, 0, A 0 1; 0, 1, 0; A 1 0, 0, A 1 1]

theorem activeBinaryMatrix_mul (A B : Matrix (Fin 2) (Fin 2) E) :
    activeBinaryMatrix (A * B) = activeBinaryMatrix A * activeBinaryMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [activeBinaryMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

def activeBinaryBlock : Matrix.SpecialLinearGroup (Fin 2) E →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL E where
  toFun A := ⟨activeBinaryMatrix A.val, by
    have h := A.property
    rw [Matrix.det_fin_two] at h
    simpa [activeBinaryMatrix, Matrix.det_fin_three] using h⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [activeBinaryMatrix]
  map_mul' A B := Subtype.ext (activeBinaryMatrix_mul A.val B.val)

theorem activeBinaryBlock_matrix (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    (activeBinaryBlock A).val = activeBinaryMatrix A.val := rfl

theorem activeBinaryMatrix_conjTranspose [StarRing E] (A : Matrix (Fin 2) (Fin 2) E) :
    activeBinaryMatrix A.conjTranspose = (activeBinaryMatrix A).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [activeBinaryMatrix, Matrix.conjTranspose_apply]

theorem activeBinaryMatrix_form (b : E) :
    activeBinaryMatrix (Hermitian.binaryHermitianForm b) = UnitaryMatrixEquiv.Quadratic.diagonalForm b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [activeBinaryMatrix, Hermitian.binaryHermitianForm, UnitaryMatrixEquiv.Quadratic.diagonalForm, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]

theorem activeBinaryMatrix_gram [StarRing E] (b : E)
    (A : Matrix (Fin 2) (Fin 2) E)
    (hA : A.conjTranspose * Hermitian.binaryHermitianForm b * A = Hermitian.binaryHermitianForm b) :
    (activeBinaryMatrix A).conjTranspose * UnitaryMatrixEquiv.Quadratic.diagonalForm b * activeBinaryMatrix A = UnitaryMatrixEquiv.Quadratic.diagonalForm b := by
  rw [← activeBinaryMatrix_form b, ← activeBinaryMatrix_conjTranspose,
    ← activeBinaryMatrix_mul, ← activeBinaryMatrix_mul, hA]

theorem activeBinaryBlock_gram [StarRing E] (b : E)
    (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (hA : A.val.conjTranspose * Hermitian.binaryHermitianForm b * A.val = Hermitian.binaryHermitianForm b) :
    (activeBinaryBlock A).val.conjTranspose * UnitaryMatrixEquiv.Quadratic.diagonalForm b * (activeBinaryBlock A).val =
      UnitaryMatrixEquiv.Quadratic.diagonalForm b := by
  rw [activeBinaryBlock_matrix]
  exact activeBinaryMatrix_gram b A.val hA

variable {F : Type*} [Field F] [Algebra F E] [StarRing E]
  (a b : F) (δ : E) (hδ : δ ^ 2 = algebraMap F E a)
  (hreal : ∀ t : F, star (algebraMap F E t) = algebraMap F E t)
  (hstar : star δ = -δ)

def quaternionRankThreeUnitary :
    (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker →*
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd E) (algebraMap F E b) where
  toFun q := ⟨activeBinaryBlock (SpecialLinear.unitaryQuaternionNormOneHom a b δ hδ q),
    (UnitaryMatrixEquiv.Quadratic.unitary_matrix_iff _ _).mpr
      (activeBinaryBlock_gram _ _ (SpecialLinear.unitaryQuaternionNormOneHom_gram a b δ hδ hreal hstar q))⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (activeBinaryBlock.comp (SpecialLinear.unitaryQuaternionNormOneHom a b δ hδ))
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (activeBinaryBlock.comp (SpecialLinear.unitaryQuaternionNormOneHom a b δ hδ)) q r

end

/-! The binary quaternion subgroup in the actual quadratic-algebra
unitary model, including split local quadratic algebras. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic

variable {F : Type*} [Field F]

def quadraticRoot (a : F) : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a := ⟨0, 1⟩

theorem quadraticRoot_sq (a : F) :
    quadraticRoot a ^ 2 = algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) a := by
  ext <;> simp [quadraticRoot, pow_two]

theorem quadraticRoot_star (a : F) : star (quadraticRoot a) = -quadraticRoot a := by
  ext <;> simp [quadraticRoot]

theorem quadraticScalar_star (a t : F) :
    star (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) t) = algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) t := by
  ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

def quaternionQuadraticUnitary (a b : F) :
    (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) :=
  (UnitaryMatrixEquiv.Quadratic.unitaryMatrixEquiv (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)).toMonoidHom.comp
    (quaternionRankThreeUnitary a b (quadraticRoot a) (quadraticRoot_sq a)
      (quadraticScalar_star a) (quadraticRoot_star a))

theorem quaternionQuadraticUnitary_matrix (a b : F) (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker) :
    (quaternionQuadraticUnitary a b q).val.val =
      activeBinaryMatrix (UnitaryMatrix.unitaryQuaternionMap a b (quadraticRoot a) (quadraticRoot_sq a) q.val.val) :=
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary
