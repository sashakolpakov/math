import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Curvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvature

/-! # Reality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! The actual curvature of every positive smooth Hermitian metric is imaginary valued. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem Reality.manifoldTwoMixed_sub (A B : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2)
    (hA : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 A.val) (hB : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 B.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 (A - B).val := by
  intro e he y hy z v
  change A.val.inChart e y (fun i => (z : ℂ) • v i) - B.val.inChart e y (fun i => (z : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 z * (A.val.inChart e y v - B.val.inChart e y v)
  rw [hA e he y hy z v, hB e he y hy z v, mul_sub]

theorem Data.HolomorphicLineMetricData.curvature_re_zero (h : Data.HolomorphicLineMetricData u)
    (x : M) (v : Fin 2 → TangentSpace 𝓘(ℝ, E) x) : (h.curvature x v).re = 0 := by
  have he := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) 2 =>
    (a ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩ v).re) (h.curvature_onOpen x)
  exact he.trans (RealScalarCurvature.smoothScalarOpenCurvature_re_zero (h.logFunction x) (fun y => Complex.conj_ofReal _)
    ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩ v)

theorem Data.HolomorphicLineMetricData.curvature_conjugate (h : Data.HolomorphicLineMetricData u) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm h.curvature = -h.curvature := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star (h.curvature x v) = -(h.curvature x v)
  apply Complex.ext <;> simp [h.curvature_re_zero x v]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
