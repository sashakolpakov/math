import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RoughLaplacian

/-! # Bochner Decomposition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original smooth Dolbeault Laplacian equals its native rough Laplacian plus the actual base and line curvature operators. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_decomposition (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z =
      Line.RoughAnti.lineCovectorRoughLaplacian b 1 B G A f z + BaseCurvatureAction.baseCurvatureAction b (B z) G z (f z) +
        Line.CurvatureContraction.lineCurvatureAction b (B z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (f z) := by
  apply ContinuousAlternatingMap.ext
  intro t
  have ht : t = (fun _ => t 0) := funext (fun j => congrArg t (Subsingleton.elim j 0))
  rw [ht]
  simp only [ContinuousAlternatingMap.add_apply]
  have hd := h.smoothDolbeaultLaplacianOne_rough V e he i a hz (t 0)
  have hb := BaseCurvatureAction.baseCurvatureAction_apply (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) (t 0)
  exact hd.trans (congrArg₂ (fun p q : ℂ => p + q)
    (congrArg₂ (fun p q : ℂ => p + q) rfl hb.symm) rfl)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
