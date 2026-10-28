import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerLineAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

/-! # Rough Laplacian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The Hessian term of the original smooth Laplacian is the actual covariant rough Laplacian. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_rough (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z
    let F := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z
    let R := Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z (fun _ => w) =
      Line.RoughAnti.lineCovectorRoughLaplacian b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
        (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z (fun _ => w) +
      (1 / 2 : ℂ) * (∑ j,
        (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) w) f) (fun _ => S (b.coord j).toContinuousLinearMap) +
          Complex.I * (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) (Complex.I • w)) f)
              (fun _ => S (b.coord j).toContinuousLinearMap)))) +
      Line.CurvatureContraction.lineCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) F f (fun _ => w) := by
  have hs := ((h.projectiveCovectorConnection_smooth V e he ⊤ 1 a.val i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds
      ⟨hz.1, trivial, hz.2⟩)).differentiableAt (by simp)
  have hr := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => f (fun _ => w))
    (Line.RoughAnti.lineCovectorRoughLaplacian_hessian (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) hs
      (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz.1))
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.add_apply, smul_eq_mul] at hr
  have hd := h.smoothDolbeaultLaplacianOne_curvatureAction V e he i a hz w
  exact hd.trans (congrArg₂ (fun p q : ℂ => p + q)
    (congrArg₂ (fun p q : ℂ => p + q) hr.symm rfl) rfl)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
