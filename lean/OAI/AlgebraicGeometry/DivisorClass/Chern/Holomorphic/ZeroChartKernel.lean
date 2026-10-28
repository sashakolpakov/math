import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ZeroChartHolomorphic
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault
import Mathlib.Analysis.Calculus.DiffContOnCl

/-! # Zero Chart Kernel -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartKernel

noncomputable section

/-! Original global section coefficients are holomorphic wherever the original Dolbeault source vanishes on an actual manifold open. -/

open _root_.TopologicalSpace _root_.Metric
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace) (U : Opens V.analyticSpace)

include he

theorem holomorphicLineZeroChart_local_kernel (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (ha : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) = 0) :
    ContDiffOn ℂ ∞ (ZeroChartPair.holomorphicLineZeroChart V e i a)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  let b := HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) a
  have hd : HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u U b = 0 :=
    (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_restrict (le_top : U ≤ ⊤) a).symm.trans ha
  have hi : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (b.val i) = 0 :=
    congrArg (fun t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 => t.val i) hd
  have hc := Projective.ZeroChartHolomorphic.projectiveOpenZeroChart_holomorphic V e he _ (b.val i) hi
  apply hc.congr
  intro z hz
  exact (congrArg (fun T : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 => T 0)
    (Projective.BasePartition.projectiveOpenChartForm_restrict V e
      (inf_le_inf_right (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) (le_top : U ≤ ⊤))
        0 (a.val i) hz)).symm

theorem holomorphicLineZeroChart_local_kernel_ball (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (ha : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) = 0)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (R : ℝ)
    (hball : closedBall x R ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    DiffContOnCl ℂ (ZeroChartPair.holomorphicLineZeroChart V e i a) (ball x R) :=
  ((holomorphicLineZeroChart_local_kernel V e he i U a ha).differentiableOn (by simp)).diffContOnCl_ball hball

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartKernel
