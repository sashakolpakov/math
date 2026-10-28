import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LogMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormMixedDerivative

/-! # Local Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LocalCurvature

noncomputable section

/-! Local connection and curvature forms from the actual logarithmic Hermitian metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def holomorphicLineLogMetricFunction (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  ⟨fun x => (LogMetric.holomorphicLineLogMetric u i x : ℂ),
    Complex.ofRealCLM.contDiff.contMDiff.comp (LogMetric.holomorphicLineLogMetric_contMDiff u i)⟩

def holomorphicLineLogMetricZeroForm (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 0 :=
  SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicLineLogMetricFunction u i)

def holomorphicLineLocalConnectionForm (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 1 :=
  Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (holomorphicLineLogMetricZeroForm u i))

def holomorphicLineLocalCurvatureForm (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (holomorphicLineLocalConnectionForm u i)

theorem holomorphicLineLocalConnectionForm_type (i : M) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 (holomorphicLineLocalConnectionForm u i) :=
  Manifold.OneFormProjection.openManifoldOnePart_holomorphic _

theorem holomorphicLineLocalCurvatureForm_type (i : M) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (holomorphicLineLocalCurvatureForm u i) :=
  OneFormMixedDerivative.openManifold_d_holomorphic_d_mixed (holomorphicLineLogMetricZeroForm u i)

theorem holomorphicLineLocalCurvatureForm_closed (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (holomorphicLineLocalCurvatureForm u i) = 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared (holomorphicLineLocalConnectionForm u i)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.LocalCurvature
