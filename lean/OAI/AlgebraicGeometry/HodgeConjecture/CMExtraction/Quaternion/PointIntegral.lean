import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne

/-! # Point Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointIntegral

noncomputable section

/-! Integral coefficient control for the explicit quaternion subgroup.
Only integrality of the Hermitian coefficient and the source matrix
entries is required for each local factor. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {K : Type} [Field K]

theorem quaternionUnitaryCoordinateMatrix_integral (a b : K) (S : Subring K)
    (hb : b ∈ S) (x : Fin 4 → K) (hx : ∀ i, x i ∈ S) (i j : Fin 3) :
    (PointOne.quaternionUnitaryCoordinateMatrix a b x i j).re ∈ S ∧
      (PointOne.quaternionUnitaryCoordinateMatrix a b x i j).im ∈ S := by
  fin_cases i <;> fin_cases j <;>
    simp [PointOne.quaternionUnitaryCoordinateMatrix, QuadraticUnitary.activeBinaryMatrix, hx, hb,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      S.zero_mem, S.one_mem, S.neg_mem, S.mul_mem]

variable {F : Type} [Field F]

theorem quaternionPointUnitary_integral (a b : F) (ρ : F →+* K) (S : Subring K)
    (hb : ρ b ∈ S) (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ)
    (hg : ∀ i j, (NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) ρ g) i j ∈ S)
    (i j : Fin 3) :
    ((PointOne.quaternionPointUnitary a b ρ g).val.val i j).re ∈ S ∧
      ((PointOne.quaternionPointUnitary a b ρ g).val.val i j).im ∈ S := by
  rw [PointOne.quaternionPointUnitary_matrix]
  exact quaternionUnitaryCoordinateMatrix_integral (ρ a) (ρ b) S hb _ (fun k => hg k 0) i j

theorem quaternionPointUnitary_inverse_integral (a b : F) (ρ : F →+* K) (S : Subring K)
    (hb : ρ b ∈ S) (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ)
    (hg : ∀ i j, (NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) ρ g⁻¹) i j ∈ S)
    (i j : Fin 3) :
    ((PointOne.quaternionPointUnitary a b ρ g).val.inv i j).re ∈ S ∧
      ((PointOne.quaternionPointUnitary a b ρ g).val.inv i j).im ∈ S := by
  have h := quaternionPointUnitary_integral a b ρ S hb g⁻¹ hg i j
  rw [map_inv] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointIntegral
