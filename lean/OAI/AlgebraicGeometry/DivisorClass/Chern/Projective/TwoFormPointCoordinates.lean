import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureDomination
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

/-! # Two Form Point Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TwoFormPointCoordinates

noncomputable section

/-! Actual Euclidean chart evaluation of an original two-form at an original manifold tangent vector. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem smoothForm_euclidean_at_point (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (x : V.analyticSpace) (hx : x ∈ e.source) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 F.val (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x)
      ![(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v),
        Complex.I • (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v)] =
      F x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v] := by
  calc
    _ = F.val.inChart e (e x) ![Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v, Complex.I • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x v] := by
      unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward
      rw [ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg (F.val.inChart e (e x))
      funext j
      fin_cases j
      · exact (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).apply_symm_apply _
      · exact ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul Complex.I _).trans
          (congrArg (fun w : V.analyticModel => Complex.I • w) ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).apply_symm_apply _))
    _ = _ := CurvatureDomination.smoothForm_metricInChart_at V F e he x hx v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TwoFormPointCoordinates
