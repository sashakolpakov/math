import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianMixedTrace
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RoughLaplacian

/-! # Hessian Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The mixed trace in the original bundle Hessian is a zeroth-order curvature term. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorHessian_mixed_curvature
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension
    (∑ j, Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      f z (b j) (Complex.I • S (b.coord j).toContinuousLinearMap) (fun _ => w)) =
      (1 / 2 : ℂ) * ∑ j,
        (-Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1
          (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z (b j) (Complex.I • S (b.coord j).toContinuousLinearMap)) (f z) +
          Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z ![b j, Complex.I • S (b.coord j).toContinuousLinearMap] • f z) (fun _ => w) := by
  have ha := ((h.projectiveCovectorConnection_smooth V e he U 1 a i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have ht := Line.HessianMixedTrace.lineCovectorHessian_mixed_trace (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1) (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz.1)
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) ha (fun _ => w)
  apply ht.trans
  apply congrArg (fun q : ℂ => (1 / 2 : ℂ) * q)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun q : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => q (fun _ => w))
    (h.projectiveCovectorHessian_commutator V e he U a i hz _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
