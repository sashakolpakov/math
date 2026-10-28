import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames

/-! # Quadratic Coefficient Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticCoefficientMaps.CM

noncomputable section

/-! ThetaCycle: the two actual CM quadratic coefficients as rational linear
maps, including their coordinatewise maps on the ball lattice. -/

open scoped _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def cmQuadraticCoefficient (s : Fin 2) : K →ₗ[ℚ] maximalRealSubfield K :=
  (LinearMap.proj s).comp
    (((QuadraticAlgebra.linearEquivTuple (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 0).toLinearMap.restrictScalars ℚ).comp
      ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toLinearMap.restrictScalars ℚ))

def cmLatticeCoefficients (s : Fin 2) : HeckeCycles.GeometricSource.CM.Vec K →ₗ[ℚ] HeckeCycles.GeometricSource.CM.Vec (maximalRealSubfield K) :=
  LinearMap.pi (fun i => (cmQuadraticCoefficient K δ hδ hδ0 s).comp (LinearMap.proj i))

theorem cm_quadratic_coefficient_re (x : K) :
    cmQuadraticCoefficient K δ hδ hδ0 0 x = ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm x).re := rfl

theorem cm_quadratic_coefficient_im (x : K) :
    cmQuadraticCoefficient K δ hδ hδ0 1 x = ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm x).im := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticCoefficientMaps.CM
