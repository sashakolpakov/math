import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportNew
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Quadratic Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticTensor.CM

noncomputable section

/-!
ThetaCycle: the actual AdelicSplitting tensor form in the constructed quadratic coordinates.
The skew coefficient is `-2 δ a`: the sign switches the conjugate-linear
argument, and the factor two cancels AdelicSplitting's half-trace convention.
-/

open scoped Classical Kronecker

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def quadraticHermitianMatrix (β : K) :
    Matrix (Fin 3) (Fin 3)
      (QuadraticAlgebra (NumberField.maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 0) :=
  Matrix.diagonal (fun j => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (if j = 2 then β else 1))

def quadraticSkewMatrix (a : Fin 2 → K) :
    Matrix (Fin 2) (Fin 2)
      (QuadraticAlgebra (NumberField.maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 0) :=
  Matrix.diagonal (fun i => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (-2 * δ * a i))

def quadraticTensorPosition (x : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2 :=
  fun ji => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (x ji.1 ji.2)

theorem quadratic_tensor_form
    (β : K) (hβ : NumberField.IsCMField.complexConj K β = β)
    (a : Fin 2 → K) (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i)
    (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue
      (quadraticHermitianMatrix K δ hδ hδ0 β ⊗ₖ quadraticSkewMatrix K δ hδ hδ0 a)
      (quadraticTensorPosition K δ hδ hδ0 x) (quadraticTensorPosition K δ hδ hδ0 y) =
      (-2 * (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ) *
        star ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (TransportNew.CM.tensorHermitian K β a x y)) := by
  apply (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, quadraticHermitianMatrix, quadraticSkewMatrix,
    Matrix.diagonal_kronecker_diagonal, Matrix.mulVec_diagonal, dotProduct,
    quadraticTensorPosition, ← QuadraticModel.CM.cm_quadratic_equiv_conjugation, map_sum, map_mul,
    map_neg, map_ofNat, AlgEquiv.apply_symm_apply]
  simp only [TransportNew.CM.tensorHermitian, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, map_sum, map_mul,
    NumberField.IsCMField.complexConj_apply_apply, ha, apply_ite, hβ, map_one,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The native unitary tensor pairing has exactly the original rational
symplectic trace, after the explicit scalar and coordinate conversion. -/
theorem quadratic_tensor_rational_trace
    (β : K) (hβ : NumberField.IsCMField.complexConj K β = β)
    (a : Fin 2 → K) (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i)
    (x y : TransportNew.CM.TensorPositions K) :
    Algebra.trace ℚ (NumberField.maximalRealSubfield K)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
        (quadraticHermitianMatrix K δ hδ hδ0 β) (quadraticSkewMatrix K δ hδ hδ0 a)
        (quadraticTensorPosition K δ hδ hδ0 x) (quadraticTensorPosition K δ hδ hδ0 y)) =
      Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K β a x y) := by
  have hd : star ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ) =
      -(QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ := by
    rw [← QuadraticModel.CM.cm_quadratic_equiv_conjugation, hδ, map_neg]
  rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, quadratic_tensor_form K δ hδ hδ0 β hβ a ha x y,
    QuadraticModel.CM.quadratic_skew_trace_normalization _ _ _ hd,
    QuadraticModel.CM.cm_quadratic_rational_trace K δ hδ hδ0, map_mul,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticTensor.CM
