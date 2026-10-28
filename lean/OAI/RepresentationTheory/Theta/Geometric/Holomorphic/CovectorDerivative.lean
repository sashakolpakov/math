import OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorForms
import OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorPurity
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientCriterion

/-! # Covector Derivative -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDerivative

noncomputable section

/-! The exterior derivative of a holomorphic covector field on the
actual open domain has bidegree (2,0). -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def complexCovectorComplexLinear : (E →L[ℂ] ℂ) →L[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 where
  toFun := Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := Complex.CovectorForms.complexCovectorRealLinear.continuous

theorem holomorphicCovector_coefficients_contDiff (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) :
    ContDiffOn ℂ ∞ (fun z => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a z)) U :=
  (complexCovectorComplexLinear (E := E)).contDiff.comp_contDiffOn
    (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn U.isOpen ha)

theorem holomorphicCovectorManifoldForm_derivative_pure (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U 2 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Complex.CovectorForms.holomorphicCovectorManifoldForm U a ha)).val := by
  intro e he z hz
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hz]
  have hzU : z ∈ U := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hz
  have heq : (Complex.CovectorForms.holomorphicCovectorManifoldForm U a ha).val.inChart e =ᶠ[𝓝 z]
      (fun w => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a w)) := by
    filter_upwards [U.isOpen.mem_nhds hzU] with w hw
    exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart
      (fun x : U => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a x.val)) e he hw).trans
        (Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨w, hw⟩)
  rw [heq.extDeriv_eq]
  apply AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientCriterion.pureForm_extDeriv_pure_of_complex
    (((holomorphicCovector_coefficients_contDiff U a ha).contDiffAt
      (U.isOpen.mem_nhds hzU)).differentiableAt (by simp))
  exact Filter.Eventually.of_forall fun _ => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree E _

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDerivative
