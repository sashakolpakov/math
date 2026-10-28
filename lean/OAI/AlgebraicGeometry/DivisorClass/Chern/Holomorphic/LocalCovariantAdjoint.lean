import OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictedChartReconstruction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalFrameForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.AdjointCoefficients

/-! # Local Covariant Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native local covariant adjoint reconstructed as actual smooth covectors in the original bundle frame. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.chartCovariantAdjointFrame (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n :=
  Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n (h.projectiveCovariantAdjointCoefficients V e i n
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i (n + 1) a).extension))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartCovariantAdjointFrame_smooth (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (h.chartCovariantAdjointFrame V e i n a)
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) := by
  have hform := ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) (n + 1)
    (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i (n + 1) a)
  have hc := ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (n + 1)).contDiff.restrict_scalars ℝ).comp_contDiffOn hform
  have hadj := h.projectiveCovariantAdjointCoefficients_smooth V e he i n _ hc
  exact RestrictedChartReconstruction.chartFormOfEuclideanCoefficients_smooth_onOpen V e he
    (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) n inf_le_left _
    (hadj.mono (fun _ hz => ⟨hz.1, hz.2.2⟩))

def HolomorphicMetric.Data.HolomorphicLineMetricData.chartCovariantAdjointOpen (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) n :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ (h.chartCovariantAdjointFrame V e i n a)
    (h.chartCovariantAdjointFrame_smooth V e he i n a)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartCovariantAdjointFrame_coefficients (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (h.chartCovariantAdjointFrame V e i n a) z =
      h.projectiveCovariantAdjointCoefficients V e i n
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i (n + 1) a).extension) z :=
  Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients_inverse V e he n _ z hz

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
