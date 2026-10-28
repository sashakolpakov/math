import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.HessianTrace
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

/-! # Rough -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original antiholomorphic rough Laplacian is half the full real rough Laplacian plus its exact curvature correction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorRough_full
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension
    Line.RoughAnti.lineCovectorRoughLaplacian b 1 B G A f z =
      (1 / 2 : ℂ) • Line.RoughAnti.lineCovectorFullRoughLaplacian b 1 B G A f z -
        (Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 (B z)
          (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (f z) := by
  have ha := ((h.projectiveCovectorConnection_smooth V e he U 1 a i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hr := Line.RoughAnti.lineCovectorRoughLaplacian_hessian (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) ha (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz.1)
  dsimp only
  apply ContinuousAlternatingMap.ext
  intro t
  have ht : t = (fun _ => t 0) := funext (fun j => congrArg t (Subsingleton.elim j 0))
  rw [ht, hr]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul,
    Line.RoughAnti.lineCovectorFullRoughLaplacian_apply, Line.RoughAnti.lineCovectorMixedCurvatureTrace_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h.projectiveCovectorHessian_mixed_curvature V e he U a i hz (t 0)]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
