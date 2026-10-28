import OAI.NumberTheory.Quaternion.Arithmetic.FiniteOrbitCompact
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarMap

/-! # Orbit Scalar -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OrbitScalar

noncomputable section

/-! Scalar extension and rational multiplication commute with the
quaternion orbit coordinates used in the adelic reduction. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra

variable {F K : Type} [Field F] [Field K]

theorem quaternionCoefficientMap_coordinates (ρ : F →+* K) (a b : F) (r : ℍ[F,a,b]) :
    linearEquivTuple (ρ a) 0 (ρ b) (ConjugationQuaternion.quaternionCoefficientMap ρ a b r) =
      fun i => ρ (linearEquivTuple a 0 b r i) := by
  funext i
  fin_cases i <;> rfl

theorem quaternionRegularMatrix_mul_coordinates (a b : K) (q r : ℍ[K,a,b]) :
    MatrixQuaternionDet.quaternionRegularMatrix a b q *ᵥ linearEquivTuple a 0 b r =
      linearEquivTuple a 0 b (q * r) := by
  apply (linearEquivTuple a 0 b).symm.injective
  have he := MatrixGroup.quaternionRegularMatrix_coordinates_mul a b q (linearEquivTuple a 0 b r)
  change (linearEquivTuple a 0 b).symm
    (MatrixQuaternionDet.quaternionRegularMatrix a b q *ᵥ linearEquivTuple a 0 b r) =
      q * (linearEquivTuple a 0 b).symm (linearEquivTuple a 0 b r) at he
  rw [LinearEquiv.symm_apply_apply] at he ⊢
  exact he

theorem quaternionPointsOrbit_diagonal_mul (a b : F) (ρ : F →+* K)
    (r : ℍ[F,a,b]ˣ) (q : (Norm.quaternionUnitNorm a b).ker)
    (g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) :
    OrbitTopology.quaternionPointsOrbit a b ρ (FiniteOrbitCompact.quaternionScalarUnit ρ a b r)
      (g * (MatrixGroup.quaternionNormOneMatrixGroup a b).map (RingHom.id F) ρ
        (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q)) =
      g.val.val *ᵥ (fun i => ρ (linearEquivTuple a 0 b (q.val.val * r.val) i)) := by
  rw [MatrixScalarMap.quaternionMatrixPointsEquiv_coefficientMap]
  change (g.val.val * MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b)
      (ConjugationQuaternion.quaternionCoefficientMap ρ a b q.val.val)) *ᵥ
      linearEquivTuple (ρ a) 0 (ρ b) (ConjugationQuaternion.quaternionCoefficientMap ρ a b r.val) = _
  rw [← Matrix.mulVec_mulVec, quaternionRegularMatrix_mul_coordinates, ← map_mul,
    quaternionCoefficientMap_coordinates]

end

end OAI.NumberTheory.Quaternion.Arithmetic.OrbitScalar
