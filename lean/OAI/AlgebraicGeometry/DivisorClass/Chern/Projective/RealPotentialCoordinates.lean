import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension

/-! # Real Potential Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RealPotentialCoordinates

noncomputable section

/-! Actual compact real chart potentials as original global zero-forms, with the exact original curvature in their coordinate germ. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (g : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
  (hs : tsupport g ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectiveRealScalarPotential : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  GlobalRealScalarForm.globalRealScalarForm (RealChartExtension.projectiveRealChartExtension V e g) (RealChartExtension.projectiveRealChartExtension_smooth V e he g hg hc hs)

theorem projectiveRealScalarPotential_scalar_chart {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    BasePartition.projectiveScalarChart V e ⊤ (ScalarPotentialFunctions.scalarPotentialOpenFunction (projectiveRealScalarPotential V e he g hg hc hs) ⊤) z =
      (g z : ℂ) := by
  rw [BasePartition.projectiveScalarChart_apply V e ⊤ _ (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e ⊤ from ⟨hz, trivial⟩)]
  change GlobalRealScalarForm.globalRealScalarForm _ _ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) 0 = (g z : ℂ)
  exact (GlobalRealScalarForm.globalRealScalarForm_apply _ _ _ 0).trans
    (congrArg Complex.ofReal (RealChartExtension.projectiveRealChartExtension_inverse V e g hz))

theorem projectiveRealScalarPotential_curvature_germ {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (k : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hk : ContDiff ℝ ∞ k) (hgk : g =ᶠ[𝓝 z] k) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (ScalarPotential.globalScalarCurvature (projectiveRealScalarPotential V e he g hg hc hs)).val z =
      extDeriv (fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (fderiv ℝ k y)) z := by
  let φ := projectiveRealScalarPotential V e he g hg hc hs
  have hcoord : BasePartition.projectiveScalarChart V e ⊤ (ScalarPotentialFunctions.scalarPotentialOpenFunction φ ⊤) =ᶠ[𝓝 z] fun y => (k y : ℂ) := by
    filter_upwards [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz, hgk] with y hy hgy
    exact (projectiveRealScalarPotential_scalar_chart V e he g hg hc hs hy).trans (congrArg Complex.ofReal hgy)
  have hp := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel (⊤ : Opens V.analyticSpace) 2 =>
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.extension z) (ScalarPotentialFunctions.scalarPotentialOpenFunction_curvature φ ⊤)
  exact (hp.trans (ConnectionCurvature.projectiveOpenChartForm_onOpen V e ⊤ 2 (ScalarPotential.globalScalarCurvature φ) ⟨hz, trivial⟩)).symm.trans
    (ScalarCoordinates.projectiveScalarCurvature_real_coordinates V e he ⊤ (ScalarPotentialFunctions.scalarPotentialOpenFunction φ ⊤) k ⟨hz, trivial⟩ hk hcoord)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RealPotentialCoordinates
