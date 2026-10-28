import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

/-! # Point One -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne

noncomputable section

section

/-! Map the actual algebraic quaternion matrix points into the quadratic
special unitary group. The only parameter transport is the proved
identity between the scalar image of -b and the negative image of b. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

variable {K : Type} [Field K]

def quaternionNormOneParameterEquiv (a b c : K) (h : b = c) :
    (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a b).ker ≃* (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a c).ker := by
  subst c
  exact MulEquiv.refl _

theorem quaternionNormOneParameterEquiv_coordinates (a b c : K) (h : b = c)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a b).ker) :
    QuaternionAlgebra.equivTuple a 0 c
        (quaternionNormOneParameterEquiv a b c h q).val.val =
      QuaternionAlgebra.equivTuple a 0 b q.val.val := by
  subst c
  rfl

variable {F : Type} [Field F]

theorem quaternionMatrixPointsEquiv_symm_quaternion (a b : F) (ρ : F →+* K)
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) :
    ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a b ρ).symm g).val.val =
      NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet.quaternionFirstColumn (ρ a) (ρ b)
        (NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b) ρ g) := by
  obtain ⟨q, rfl⟩ := (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a b ρ).surjective g
  rw [MulEquiv.symm_apply_apply, NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv_matrix]
  exact (NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet.quaternionRegularMatrix_firstColumn (ρ a) (ρ b) q.val.val).symm

def quaternionPointUnitary (a b : F) (ρ : F →+* K) :
    (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap K (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K (ρ a)) (ρ b))) :=
  (QuadraticUnitary.quaternionQuadraticUnitary (ρ a) (ρ b)).comp
    ((quaternionNormOneParameterEquiv (ρ a) (ρ (-b)) (-ρ b) (map_neg ρ b)).toMonoidHom.comp
      (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) ρ).symm.toMonoidHom)

end

section

/-! The local quaternion-to-unitary map is an explicit polynomial in
the first column of the original four-dimensional matrix realization. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

variable {K : Type} [Field K]

def quaternionUnitaryCoordinateMatrix (a b : K) (x : Fin 4 → K) :
    Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a) :=
  QuadraticUnitary.activeBinaryMatrix
    !![(⟨x 0, x 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a),
       -algebraMap K (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a) b * (⟨x 2, x 3⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a);
       (⟨x 2, -x 3⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a), (⟨x 0, -x 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a)]

theorem quaternionQuadraticUnitary_matrix_tuple (a b : K)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker) :
    (QuadraticUnitary.quaternionQuadraticUnitary a b q).val.val =
      quaternionUnitaryCoordinateMatrix a b (QuaternionAlgebra.equivTuple a 0 (-b) q.val.val) := by
  rw [QuadraticUnitary.quaternionQuadraticUnitary_matrix, UnitaryMatrix.unitaryQuaternionMap_apply]
  apply congrArg QuadraticUnitary.activeBinaryMatrix
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticUnitary.quadraticRoot, QuaternionAlgebra.equivTuple_apply]

variable {F : Type} [Field F]

theorem quaternionPointUnitary_matrix (a b : F) (ρ : F →+* K)
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ) :
    (quaternionPointUnitary a b ρ g).val.val =
      quaternionUnitaryCoordinateMatrix (ρ a) (ρ b)
        (fun i => (NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) ρ g) i 0) := by
  change (QuadraticUnitary.quaternionQuadraticUnitary (ρ a) (ρ b)
    (quaternionNormOneParameterEquiv (ρ a) (ρ (-b)) (-ρ b) (map_neg ρ b)
      ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) ρ).symm g))).val.val = _
  rw [quaternionQuadraticUnitary_matrix_tuple, quaternionNormOneParameterEquiv_coordinates,
    quaternionMatrixPointsEquiv_symm_quaternion]
  apply congrArg (quaternionUnitaryCoordinateMatrix (ρ a) (ρ b))
  funext i
  fin_cases i <;> rfl

end

/-! Scalar extension of the explicit quaternion map agrees with entrywise
base change of the quadratic special unitary matrix. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

variable {F K : Type} [Field F] [Field K]

theorem quaternionUnitaryCoordinateMatrix_map (ρ : F →+* K) (a b : F) (x : Fin 4 → F) :
    (quaternionUnitaryCoordinateMatrix a b x).map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange ρ a) =
      quaternionUnitaryCoordinateMatrix (ρ a) (ρ b) (fun i => ρ (x i)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply QuadraticAlgebra.ext <;>
      simp [quaternionUnitaryCoordinateMatrix, QuadraticUnitary.activeBinaryMatrix, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

def quaternionRationalUnitary (a b : F) :
    (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) :=
  quaternionPointUnitary a b (RingHom.id F)

theorem quaternionPointUnitary_baseChange (ρ : F →+* K) (a b : F)
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints) :
    (quaternionPointUnitary a b ρ
      ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).map (RingHom.id F) ρ g)).val.val =
      (quaternionRationalUnitary a b g).val.val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange ρ a) := by
  change _ = (quaternionPointUnitary a b (RingHom.id F) g).val.val.map _
  rw [quaternionPointUnitary_matrix, quaternionPointUnitary_matrix]
  exact (quaternionUnitaryCoordinateMatrix_map ρ a b (fun i => g.val i 0)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne
