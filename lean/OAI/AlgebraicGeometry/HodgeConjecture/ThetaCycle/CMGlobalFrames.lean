import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalFrames
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryFrame

/-! # CM Global Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMGlobalFrames.CM

noncomputable section

/-! ThetaCycle: native adelic frame data from the actual CM ball and multiplicity coefficients. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

theorem real_hermitian_coefficients_ne_zero (β : K)
    (hβ : NumberField.IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    ∀ j, UnitaryFrame.CM.realHermitianCoefficients K β hβ j ≠ 0 := by
  intro j
  by_cases hj : j = 2
  · simp only [UnitaryFrame.CM.realHermitianCoefficients, hj, ite_true]
    intro hzero
    exact hβ0 (congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) hzero)
  · simp [UnitaryFrame.CM.realHermitianCoefficients, hj]

theorem real_multiplicity_coefficients_ne_zero (a : Fin 2 → K)
    (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i) (ha0 : ∀ i, a i ≠ 0) :
    ∀ i, UnitaryFrame.CM.realMultiplicityCoefficients K a ha i ≠ 0 := by
  intro i hzero
  exact ha0 i (congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) hzero)

variable (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def cmHermitianUnit (β : K)
    (hβ : NumberField.IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    (Matrix (Fin 3) (Fin 3)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (NumberField.maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  DiagonalFrame.CM.diagonalHermitianUnit _ (UnitaryFrame.CM.realHermitianCoefficients K β hβ)
    (real_hermitian_coefficients_ne_zero K β hβ hβ0)

def cmSkewUnit (a : Fin 2 → K)
    (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i) (ha0 : ∀ i, a i ≠ 0) :
    (Matrix (Fin 2) (Fin 2)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (NumberField.maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  DiagonalFrame.CM.diagonalSkewUnit _ (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (UnitaryFrame.CM.realMultiplicityCoefficients K a ha) (real_multiplicity_coefficients_ne_zero K a ha ha0)

theorem cm_hermitian_unit_val (β : K)
    (hβ : NumberField.IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    (cmHermitianUnit K δ hδ β hβ hβ0).val = QuadraticTensor.CM.quadraticHermitianMatrix K δ hδ hδ0 β :=
  (UnitaryFrame.CM.quadratic_hermitian_matrix_real K δ hδ hδ0 β hβ).symm

theorem cm_skew_unit_val (a : Fin 2 → K)
    (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i) (ha0 : ∀ i, a i ≠ 0) :
    (cmSkewUnit K δ hδ hδ0 a ha ha0).val = QuadraticTensor.CM.quadraticSkewMatrix K δ hδ hδ0 a :=
  (UnitaryFrame.CM.quadratic_skew_matrix_real K δ hδ hδ0 a ha).symm

/-- The required compatible frames are constructed over the actual maximal
real subfield, including every split and nonsplit completion. -/
def cmGlobalFrames (β : K)
    (hβ : NumberField.IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (a : Fin 2 → K) (ha : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i)
    (ha0 : ∀ i, a i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (NumberField.maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
      (cmHermitianUnit K δ hδ β hβ hβ0) (cmSkewUnit K δ hδ hδ0 a ha ha0) :=
  GlobalFrames.CM.diagonalGlobalFrames _ _ (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (UnitaryFrame.CM.realHermitianCoefficients K β hβ) (real_hermitian_coefficients_ne_zero K β hβ hβ0)
    (UnitaryFrame.CM.realMultiplicityCoefficients K a ha) (real_multiplicity_coefficients_ne_zero K a ha ha0)

def lagrangianGlobalFrames [IsGalois ℚ K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (P : Lagrangians.CM.LagrangianPair K B places d) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (NumberField.maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K P.delta P.delta_imaginary) 3 2
      (cmHermitianUnit K P.delta P.delta_imaginary B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb])))
      (cmSkewUnit K P.delta P.delta_imaginary P.delta_ne_zero P.a
        (fun i => (P.a_sign i).2.1) (fun i => (P.a_sign i).1)) :=
  cmGlobalFrames K P.delta P.delta_imaginary P.delta_ne_zero B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb])) P.a
    (fun i => (P.a_sign i).2.1) (fun i => (P.a_sign i).1)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMGlobalFrames.CM
