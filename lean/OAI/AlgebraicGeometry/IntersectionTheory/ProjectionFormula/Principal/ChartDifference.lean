import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartFiniteSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! # Chart Difference -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartDifference

noncomputable section

/-! The original local principal-divisor pairing is the difference
of the two finite weighted sums used by the native Euler expansions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
    (hF : DescentPosition.PrimeData X k W.val g hg F)
    (hout : DescentPosition.Outside X k W.val g hg F)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (A C : IrreducibleCloseds X.carrier) (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C) :
    (ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A C) =
    (∑ z ∈ F (i, true), Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
      (ChartEquations.numerator X W.val g hg i) z *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z) A C) -
    ∑ z ∈ F (i, false), Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
      (ChartEquations.denominator X W.val g hg i) z *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z) A C := by
  rw [ChartFiniteSum.coefficient X k W g hg F hF hout i x A C hx]
  apply Finite.MultiplicitySum.Difference.split
  · intro z hz hnot
    exact hout (i, true) z (hF (i, false) z hz).2.2 hnot
  · intro z hz hnot
    exact hout (i, false) z (hF (i, true) z hz).2.2 hnot

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartDifference
