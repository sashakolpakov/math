import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexTopology
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # One Covector Dual -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.OneCovectorDual.Holomorphic

noncomputable section

/-! Actual pure one-covectors are canonically the complex cotangent dual. -/

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def pureOneCovectorDualEquiv : OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0 ≃ₗ[ℂ] Module.Dual ℂ E :=
  (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E 1).trans
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ)
      (0 : Fin 1)).toLinearEquiv.symm.trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := ℂ)).symm)

theorem pureOneCovectorDualEquiv_apply (a : OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0) (v : E) :
    pureOneCovectorDualEquiv E a v = a.val (fun _ => v) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.OneCovectorDual.Holomorphic
