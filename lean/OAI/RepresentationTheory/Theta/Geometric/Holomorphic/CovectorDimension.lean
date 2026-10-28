import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Covector Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDimension

noncomputable section

/-! Actual pure degree-one real covectors are precisely complex-linear
functionals, so their dimension is the complex tangent dimension. -/

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def holomorphicCovectorDualEquiv : OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0 ≃ₗ[ℂ] Module.Dual ℂ E where
  toFun ω := ((ContinuousAlternatingMap.ofSubsingleton ℂ E ℂ (0 : Fin 1)).symm
    (AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E 1 ω)).toLinearMap
  invFun α := ⟨OAI.Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E α.toContinuousLinearMap,
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree E α.toContinuousLinearMap⟩
  left_inv ω := by
    apply Subtype.ext
    ext v
    change ω.val (fun _ => v 0) = ω.val v
    congr 1
    funext i
    exact congrArg v (Fin.eq_zero i).symm
  right_inv α := by ext v; rfl
  map_add' ω η := by ext v; rfl
  map_smul' c ω := by ext v; rfl

theorem holomorphicCovector_finrank :
    Module.finrank ℂ (OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0) = Module.finrank ℂ E :=
  (holomorphicCovectorDualEquiv E).finrank_eq.trans Subspace.dual_finrank_eq

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDimension
