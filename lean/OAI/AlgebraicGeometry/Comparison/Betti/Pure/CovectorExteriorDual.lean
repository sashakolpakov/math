import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexTopology
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Covector Exterior Dual -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorDual.Holomorphic

noncomputable section

/-! Actual pure covectors inject canonically into the dual of the complex exterior power. -/

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

def pureCovectorExteriorDualMap (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 →ₗ[ℂ] Module.Dual ℂ (⋀[ℂ]^n E) :=
  (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (M := E) (N := ℂ)).toLinearMap.comp
    ((ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ) (A := ℂ)
      (M := E) (N := ℂ)).comp (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).toLinearMap)

theorem pureCovectorExteriorDualMap_injective (n : ℕ) :
    Function.Injective (pureCovectorExteriorDualMap E n) :=
  (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (M := E) (N := ℂ)).injective.comp
    (ContinuousAlternatingMap.toAlternatingMap_injective.comp (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).injective)

theorem pureCovectorExteriorDualMap_apply (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) (v : Fin n → E) :
    pureCovectorExteriorDualMap E n a (exteriorPower.ιMulti ℂ n v) = a.val v := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorDual.Holomorphic
