import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerFormula
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.CurvatureBound

/-! # Bochner Line Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original smooth Laplacian contains exactly the curvature action with the proved positive sign. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_curvatureAction (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z
    let F := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z
    let R := Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z (fun _ => w) =
      -(1 / 2 : ℂ) * (∑ j, (H (b j) (S (b.coord j).toContinuousLinearMap) (fun _ => w) +
        Complex.I * H (b j) (Complex.I • S (b.coord j).toContinuousLinearMap) (fun _ => w))) +
      (1 / 2 : ℂ) * (∑ j,
        (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) w) f) (fun _ => S (b.coord j).toContinuousLinearMap) +
          Complex.I * (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) (Complex.I • w)) f)
              (fun _ => S (b.coord j).toContinuousLinearMap)))) +
      Line.CurvatureContraction.lineCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) F f (fun _ => w) := by
  have hd := h.smoothDolbeaultLaplacianOne_bochner V e he i a hz w
  apply hd.trans
  rw [Line.CurvatureContraction.lineCurvatureAction_apply]
  simp only [AntiOneFormCoordinates.oneFormLinear_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
