import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartDifference
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalExpansion

/-! # Chart Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEuler

noncomputable section

/-! On the simultaneously moved representative, the complete original
principal-divisor pairing is the difference of the native numerator
and denominator quotient Euler characteristics. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem equation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
    (a : X.RationalDimensionCycle p)
    (he : DescentPosition.Expansions X p k W.val g hg F a)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal ≤ x.asIdeal) :
    CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1)
      (ChartEquations.equation X W.val g hg i) A₀ x hxA hvx m =
      ∑ z ∈ F i, Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1)
        (ChartEquations.equation X W.val g hg i) z *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) z) A.val C.val := by
  apply CoveredPrincipalExpansion.coefficient X m p (k + 1) (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)
    (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1) (ChartEquations.equation X W.val g hg i)
    (F i) a (he i) (ChartSupportCover.supports X m k W g hg i)
    (ChartSupportCover.codimension X m k W g hg i)
    (ChartSupportCover.covers X m k W g hg i) A hAa A₀ hA ?_ C x hx hxA hvx
  intro B hB
  exact hp ⟨i, ⟨B, hB⟩⟩ A hAa

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
    (hF : DescentPosition.PrimeData X k W.val g hg F)
    (hout : DescentPosition.Outside X k W.val g hg F)
    (a : X.RationalDimensionCycle p)
    (he : DescentPosition.Expansions X p k W.val g hg F a)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal) :
    (ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
        (ChartEquations.numerator X W.val g hg i) A₀ x hxA hvx m -
      CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
        (ChartEquations.denominator X W.val g hg i) A₀ x hxA hvx m := by
  rw [ChartDifference.coefficient X k W g hg F hF hout i x A.val C.val hx]
  exact congrArg₂ (fun a b : ℚ => a - b)
    (equation X m p k W g hg F a he hp (i, true) A hAa A₀ hA C x hx hxA hvx).symm
    (equation X m p k W g hg F a he hp (i, false) A hAa A₀ hA C x hx hxA hvx).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEuler
