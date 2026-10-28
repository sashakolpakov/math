import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticTensor

/-! # Unitary Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryFrame.CM

noncomputable section

/-! ThetaCycle: instantiate the native unitary frame with the constructed CM coefficients. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem quadratic_equiv_real_element (x : K)
    (hx : NumberField.IsCMField.complexConj K x = x) :
    (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm x =
      ⟨QuadraticModel.CM.cmRealElement K x hx, 0⟩ := by
  apply (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective
  rw [AlgEquiv.apply_symm_apply]
  change x = QuadraticModel.CM.cmQuadraticMap K δ hδ _
  simp only [QuadraticModel.CM.cm_quadratic_map_apply, Subfield.coe_zero, zero_mul, add_zero]
  rfl

def realHermitianCoefficients (β : K) (hβ : NumberField.IsCMField.complexConj K β = β) :
    Fin 3 → NumberField.maximalRealSubfield K :=
  fun j => if j = 2 then QuadraticModel.CM.cmRealElement K β hβ else 1

def realMultiplicityCoefficients (a : Fin 2 → K)
    (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i) :
    Fin 2 → NumberField.maximalRealSubfield K := fun i => QuadraticModel.CM.cmRealElement K (a i) (ha i)

theorem quadratic_hermitian_matrix_real (β : K)
    (hβ : NumberField.IsCMField.complexConj K β = β) :
    QuadraticTensor.CM.quadraticHermitianMatrix K δ hδ hδ0 β =
      DiagonalFrame.CM.diagonalUnitaryHermitian (QuadraticModel.CM.cmQuadraticParameter K δ hδ) (realHermitianCoefficients K β hβ) := by
  unfold QuadraticTensor.CM.quadraticHermitianMatrix DiagonalFrame.CM.diagonalUnitaryHermitian
  congr 1
  funext j
  by_cases hj : j = 2
  · simp only [realHermitianCoefficients,
      hj, ite_true, quadratic_equiv_real_element K δ hδ hδ0 β hβ]
  · simp [realHermitianCoefficients, hj]
    rfl

theorem quadratic_skew_matrix_real (a : Fin 2 → K)
    (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i) :
    QuadraticTensor.CM.quadraticSkewMatrix K δ hδ hδ0 a =
      DiagonalFrame.CM.diagonalUnitarySkew (QuadraticModel.CM.cmQuadraticParameter K δ hδ) (realMultiplicityCoefficients K a ha) := by
  unfold QuadraticTensor.CM.quadraticSkewMatrix DiagonalFrame.CM.diagonalUnitarySkew
  congr 1
  funext i
  apply (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective
  rw [AlgEquiv.apply_symm_apply]
  change -2 * δ * a i = QuadraticModel.CM.cmQuadraticMap K δ hδ _
  rw [QuadraticModel.CM.cm_quadratic_map_apply]
  change -2 * δ * a i = 0 + (-2 * a i) * δ
  ring

def cmUnitaryFrame (β : K) (hβ : NumberField.IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (a : Fin 2 → K) (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i)
    (ha0 : ∀ i, a i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
      (QuadraticTensor.CM.quadraticHermitianMatrix K δ hδ hδ0 β) (QuadraticTensor.CM.quadraticSkewMatrix K δ hδ hδ0 a) := by
  rw [quadratic_hermitian_matrix_real K δ hδ hδ0 β hβ,
    quadratic_skew_matrix_real K δ hδ hδ0 a ha]
  refine DiagonalFrame.CM.diagonalUnitaryFrame _ (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (realHermitianCoefficients K β hβ) ?_ (realMultiplicityCoefficients K a ha) ?_
  · intro j
    by_cases hj : j = 2
    · simp only [realHermitianCoefficients, hj, ite_true]
      intro hzero
      exact hβ0 (congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) hzero)
    · simp [realHermitianCoefficients, hj]
  · intro i hzero
    exact ha0 i (congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) hzero)

def lagrangianUnitaryFrame [IsGalois ℚ K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (P : Lagrangians.CM.LagrangianPair K B places d) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (QuadraticModel.CM.cmQuadraticParameter K P.delta P.delta_imaginary) 3 2
      (QuadraticTensor.CM.quadraticHermitianMatrix K P.delta P.delta_imaginary P.delta_ne_zero B.b)
      (QuadraticTensor.CM.quadraticSkewMatrix K P.delta P.delta_imaginary P.delta_ne_zero P.a) :=
  cmUnitaryFrame K P.delta P.delta_imaginary P.delta_ne_zero B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb])) P.a
    (fun i => (P.a_sign i).2.1) (fun i => (P.a_sign i).1)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryFrame.CM
