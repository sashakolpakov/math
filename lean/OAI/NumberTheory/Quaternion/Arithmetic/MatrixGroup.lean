import OAI.NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm

/-! # Matrix Group -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

noncomputable section

section

/-! The quaternion norm-one group as an actual polynomial matrix
algebraic group in the representation used by Arithmetic. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {F : Type} [Field F]

def quaternionNormOneMatrixGroup (a b : F) : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F 4 where
  equations := MatrixQuaternionDet.quaternionMatrixEquations a b
  subgroup K _ ρ := (MatrixQuaternionDet.quaternionRegularNormOneHom (ρ a) (ρ b)).range
  mem_iff K _ ρ M := by
    rw [MatrixQuaternionDet.quaternionRegularNormOneHom_mem_range, MatrixQuaternionDet.quaternionMatrixEquations_iff]
    constructor
    · rintro ⟨q, hn, hq⟩
      have he : MatrixQuaternionDet.quaternionFirstColumn (ρ a) (ρ b) M.val = q := by
        rw [← hq]
        exact MatrixQuaternionDet.quaternionRegularMatrix_firstColumn (ρ a) (ρ b) q
      exact ⟨he ▸ hq, he ▸ hn⟩
    · rintro ⟨hM, hn⟩
      exact ⟨MatrixQuaternionDet.quaternionFirstColumn (ρ a) (ρ b) M.val, hn, hM⟩

def quaternionMatrixPointsEquiv (a b : F) {K : Type} [Field K] (ρ : F →+* K) :
    (Norm.quaternionUnitNorm (ρ a) (ρ b)).ker ≃* (quaternionNormOneMatrixGroup a b).Points ρ :=
  MonoidHom.ofInjective (MatrixQuaternionDet.quaternionRegularNormOneHom_injective (ρ a) (ρ b))

theorem quaternionMatrixPointsEquiv_matrix (a b : F) {K : Type} [Field K] (ρ : F →+* K)
    (q : (Norm.quaternionUnitNorm (ρ a) (ρ b)).ker) :
    PolynomialGaloisNorm.matrixPointsHom (quaternionNormOneMatrixGroup a b) ρ (quaternionMatrixPointsEquiv a b ρ q) =
      MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) q.val.val := rfl

end

/-! The reduced norm is a polynomial invariant of the faithful
regular quaternion norm-one matrix representation. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra

variable {F K : Type} [Field F] [Field K]

def quaternionOfCoordinates (a b : K) (x : Fin 4 → K) : ℍ[K,a,b] :=
  (linearEquivTuple a 0 b).symm x

def quaternionNormPolynomial (a b : F) : MvPolynomial (Fin 4) F :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.C a * MvPolynomial.X 1 ^ 2 -
    MvPolynomial.C b * MvPolynomial.X 2 ^ 2 + MvPolynomial.C a * MvPolynomial.C b * MvPolynomial.X 3 ^ 2

theorem quaternionNormPolynomial_eval (ρ : F →+* K) (a b : F) (x : Fin 4 → K) :
    MvPolynomial.eval₂Hom ρ x (quaternionNormPolynomial a b) =
      Norm.quaternionNorm (ρ a) (ρ b) (quaternionOfCoordinates (ρ a) (ρ b) x) := by
  simp [quaternionNormPolynomial, Norm.quaternionNorm_formula, quaternionOfCoordinates, equivTuple_symm_apply]

theorem quaternionRegularMatrix_coordinates_mul (a b : K) (q : ℍ[K,a,b]) (x : Fin 4 → K) :
    quaternionOfCoordinates a b (MatrixQuaternionDet.quaternionRegularMatrix a b q *ᵥ x) =
      q * quaternionOfCoordinates a b x := by
  let e := linearEquivTuple a 0 b
  have h := Algebra.leftMulMatrix_mulVec_repr (basisOneIJK a 0 b) q (e.symm x)
  change MatrixQuaternionDet.quaternionRegularMatrix a b q *ᵥ e (e.symm x) = e (q * e.symm x) at h
  rw [LinearEquiv.apply_symm_apply] at h
  apply e.injective
  change e (e.symm (MatrixQuaternionDet.quaternionRegularMatrix a b q *ᵥ x)) = e (q * e.symm x)
  rw [LinearEquiv.apply_symm_apply]
  exact h

theorem quaternionMatrixPoint_preserves_normPolynomial (ρ : F →+* K) (a b : F)
    (g : (quaternionNormOneMatrixGroup a b).Points ρ) (x : Fin 4 → K) :
    MvPolynomial.eval₂Hom ρ (g.val.val *ᵥ x) (quaternionNormPolynomial a b) =
      MvPolynomial.eval₂Hom ρ x (quaternionNormPolynomial a b) := by
  obtain ⟨q, rfl⟩ := (quaternionMatrixPointsEquiv a b ρ).surjective g
  rw [quaternionNormPolynomial_eval, quaternionNormPolynomial_eval]
  change Norm.quaternionNorm (ρ a) (ρ b) (quaternionOfCoordinates (ρ a) (ρ b)
    (MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) q.val.val *ᵥ x)) = _
  rw [quaternionRegularMatrix_coordinates_mul, map_mul]
  have hq : Norm.quaternionNorm (ρ a) (ρ b) q.val.val = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp q.property)
  rw [hq, one_mul]

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup
