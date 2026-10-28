import Mathlib

/-! # Matrix Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.MatrixExtension.CM

noncomputable section

/-! Extend an actual rational coordinate equivalence to any commutative
Q-algebra by its finite matrix, retaining the inverse and continuity. -/

open scoped Classical _root_.Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem inverse_matrix (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact e.symm_apply_apply
  rw [← LinearMap.toMatrix'_comp, h, LinearMap.toMatrix'_id]

theorem matrix_inverse (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) :
    LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1 := by
  have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact e.apply_symm_apply
  rw [← LinearMap.toMatrix'_comp, h, LinearMap.toMatrix'_id]

variable (R : Type*) [CommRing R] [Algebra ℚ R]

def equivalence (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) : (I → R) ≃ₗ[R] (J → R) where
  toFun x := (LinearMap.toMatrix' e.toLinearMap).map (algebraMap ℚ R) *ᵥ x
  invFun y := (LinearMap.toMatrix' e.symm.toLinearMap).map (algebraMap ℚ R) *ᵥ y
  left_inv x := by
    dsimp only
    have h1 : (1 : Matrix I I ℚ).map (algebraMap ℚ R) = 1 :=
      Matrix.map_one (algebraMap ℚ R) (map_zero (algebraMap ℚ R)) (map_one (algebraMap ℚ R))
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, inverse_matrix, h1, Matrix.one_mulVec]
  right_inv y := by
    dsimp only
    have h1 : (1 : Matrix J J ℚ).map (algebraMap ℚ R) = 1 :=
      Matrix.map_one (algebraMap ℚ R) (map_zero (algebraMap ℚ R)) (map_one (algebraMap ℚ R))
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, matrix_inverse, h1, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

theorem rational (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) (x : I → ℚ) :
    equivalence R e (fun i => algebraMap ℚ R (x i)) = fun j => algebraMap ℚ R (e x j) := by
  funext j
  exact (RingHom.map_mulVec (algebraMap ℚ R) (LinearMap.toMatrix' e.toLinearMap) x j).symm.trans
    (congrArg (algebraMap ℚ R) (congrFun (LinearMap.toMatrix'_mulVec e.toLinearMap x) j))

variable [TopologicalSpace R] [IsTopologicalRing R]

def continuousEquivalence (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) : (I → R) ≃L[R] (J → R) where
  toLinearEquiv := equivalence R e
  continuous_toFun := by
    apply continuous_pi
    intro j
    change Continuous (fun x : I → R => ∑ i, _ * x i)
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    change Continuous (fun y : J → R => ∑ j, _ * y j)
    fun_prop

theorem continuous_rational (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) (x : I → ℚ) :
    continuousEquivalence R e (fun i => algebraMap ℚ R (x i)) = fun j => algebraMap ℚ R (e x j) :=
  rational R e x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.MatrixExtension.CM
