import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.Rough
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerDecomposition

/-! # Bochner -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original Dolbeault Laplacian has half the full real covariant rough part and the exact remaining curvature terms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_full_decomposition (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z =
      (1 / 2 : ℂ) • Line.RoughAnti.lineCovectorFullRoughLaplacian b 1 B G A f z -
        (Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 (B z)
          (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (f z) +
        BaseCurvatureAction.baseCurvatureAction b (B z) G z (f z) +
          Line.CurvatureContraction.lineCurvatureAction b (B z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (f z) := by
  have hd := h.smoothDolbeaultLaplacianOne_decomposition V e he i a hz
  have hr := h.projectiveCovectorRough_full V e he ⊤ a.val i ⟨hz.1, trivial, hz.2⟩
  exact hd.trans (congrArg₂ (fun p q : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => p + q)
    (congrArg₂ (fun p q : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => p + q) hr rfl) rfl)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
