import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Split Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SplitImage

noncomputable section

/-! At a split place, the actual quaternion point map fills the binary
SL2 block after the specified quadratic projection. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

variable {F K : Type} [Field F] [Field K]

theorem quaternionPointUnitary_contains_quadratic (a b : F) (ρ : F →+* K)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm (ρ a) (-ρ b)).ker) :
    ∃ g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ,
      PointOne.quaternionPointUnitary a b ρ g = QuadraticUnitary.quaternionQuadraticUnitary (ρ a) (ρ b) q := by
  refine ⟨NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) ρ
    ((PointOne.quaternionNormOneParameterEquiv (ρ a) (ρ (-b)) (-ρ b) (map_neg ρ b)).symm q), ?_⟩
  change QuadraticUnitary.quaternionQuadraticUnitary (ρ a) (ρ b)
    (PointOne.quaternionNormOneParameterEquiv (ρ a) (ρ (-b)) (-ρ b) (map_neg ρ b)
      ((NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) ρ).symm
        (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) ρ _))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

variable [CharZero K]

theorem quaternionQuadraticUnitary_plus_matrix (a b r : K) (hr : r ^ 2 = a) (hr0 : r ≠ 0)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker) :
    (QuadraticUnitary.quaternionQuadraticUnitary a b q).val.val.map (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0) =
      QuadraticUnitary.activeBinaryMatrix (UnitaryMatrix.unitaryQuaternionMap a b r hr q.val.val) := by
  rw [PointOne.quaternionQuadraticUnitary_matrix_tuple, UnitaryMatrix.unitaryQuaternionMap_apply]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PointOne.quaternionUnitaryCoordinateMatrix, QuadraticUnitary.activeBinaryMatrix,
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.splitAlgebra, QuaternionAlgebra.equivTuple_apply,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring

theorem quaternionPointUnitary_split_image (a b : F) (ρ : F →+* K)
    (r : K) (hr : r ^ 2 = ρ a) (hr0 : r ≠ 0) (hb : b ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ,
      (PointOne.quaternionPointUnitary a b ρ g).val.val.map (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0) = QuadraticUnitary.activeBinaryMatrix A.val := by
  obtain ⟨q, hq⟩ := SpecialLinear.unitaryQuaternionNormOneHom_surjective (ρ a) (ρ b) r hr
    ((map_ne_zero ρ).mpr hb) hr0 A
  obtain ⟨g, hg⟩ := quaternionPointUnitary_contains_quadratic a b ρ q
  refine ⟨g, ?_⟩
  rw [hg, quaternionQuadraticUnitary_plus_matrix]
  exact congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K => QuadraticUnitary.activeBinaryMatrix B.val) hq

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SplitImage
