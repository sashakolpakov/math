import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarPotentialFunctions

/-! # Potential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Exponentiating an actual real scalar potential changes the actual metric by its curvature. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

def Data.HolomorphicLineMetricData.withPotential (h : Data.HolomorphicLineMetricData u)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) : Data.HolomorphicLineMetricData u :=
  h.rescale (fun x => Real.exp (ScalarPotentialFunctions.realPotentialScalar f x))
    (Real.contDiff_exp.contMDiff.comp (ScalarPotentialFunctions.realPotentialScalar_smooth f)) (fun x => Real.exp_pos (ScalarPotentialFunctions.realPotentialScalar f x))

theorem Data.HolomorphicLineMetricData.withPotential_logFunction (h : Data.HolomorphicLineMetricData u)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f) (i : M) :
    (h.withPotential f).logFunction i = h.logFunction i +
      ScalarPotentialFunctions.scalarPotentialOpenFunction f (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) := by
  apply ContMDiffMap.ext
  intro x
  change (Real.log (Real.exp (ScalarPotentialFunctions.realPotentialScalar f x.val) * h.weight i x) : ℂ) =
    (Real.log (h.weight i x) : ℂ) + ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x.val
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (h.positive i x)), Real.log_exp,
    Complex.ofReal_add, ScalarPotentialFunctions.realPotentialScalar_cast f hf x.val, add_comm]

theorem Data.HolomorphicLineMetricData.withPotential_localCurvature (h : Data.HolomorphicLineMetricData u)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f) (i : M) :
    (h.withPotential f).localCurvature i = h.localCurvature i +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (Projective.ScalarPotential.globalScalarCurvature f) := by
  unfold Data.HolomorphicLineMetricData.localCurvature
  rw [h.withPotential_logFunction f hf i, ScalarOpenConnection.smoothScalarOpenCurvature_add, ScalarPotentialFunctions.scalarPotentialOpenFunction_curvature]

theorem Data.HolomorphicLineMetricData.withPotential_curvature (h : Data.HolomorphicLineMetricData u)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f) :
    (h.withPotential f).curvature = h.curvature + Projective.ScalarPotential.globalScalarCurvature f := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) (h.withPotential f).curvature =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) h.curvature +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) (Projective.ScalarPotential.globalScalarCurvature f) :=
    ((h.withPotential f).curvature_onOpen x).trans ((h.withPotential_localCurvature f hf x).trans
      (congrArg (fun a => a + Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x)
        (Projective.ScalarPotential.globalScalarCurvature f)) (h.curvature_onOpen x).symm))
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) 2 =>
    a ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩) he

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
