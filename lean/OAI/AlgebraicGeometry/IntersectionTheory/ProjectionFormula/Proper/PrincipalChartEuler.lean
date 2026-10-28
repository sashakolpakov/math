import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartComponentSum

/-! # Principal Chart Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalChartEuler

noncomputable section

/-! Properness against the actual chart zero loci gives the complete
principal-divisor Euler comparison. All finite prime data and native
expansions are constructed here from the principal quotients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ SupportCycles.submodule X p (Principal.ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal) :
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
        (Principal.ChartEquations.numerator X W.val g hg i) A₀ x hxA hvx m -
      CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
        (Principal.ChartEquations.denominator X W.val g hg i) A₀ x hxA hvx m := by
  have hv (j : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) :
      X.supportCodimension (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val j.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val j.1)) = k := by
    rw [Affine.ChartGerm.FiniteSupportCharts.prime_support]
    exact W.property
  choose F hF hout he using fun j : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool =>
    PrincipalExpansion.exists_data X m k (Affine.ChartGerm.FiniteSupportCharts.ring X W.val j.1) (Affine.ChartGerm.FiniteSupportCharts.chart X W.val j.1)
      (Affine.ChartGerm.FiniteSupportCharts.prime X W.val j.1) (hv j) (Principal.ChartEquations.equation X W.val g hg j) (Principal.ChartEquations.equation_avoid X W.val g hg j)
  rw [Principal.ChartDifference.coefficient X k W g hg F hF hout i x A.val C.val hx]
  have hpair (b : Bool) := he (i, b) p (Principal.ChartSupportCover.supports X m k W g hg (i, b))
    (Principal.ChartSupportCover.codimension X m k W g hg (i, b))
    (Principal.ChartSupportCover.covers X m k W g hg (i, b)) A A₀ hA
    (fun B hB => hp ⟨(i, b), ⟨B, hB⟩⟩ A hAa) C x hx hxA hvx
  exact congrArg₂ (fun u v : ℚ => u - v) (hpair true).symm (hpair false).symm

theorem component_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ SupportCycles.submodule X p (Principal.ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal) :
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      ∑ D ∈ Finite.ClosedComponents.components X.carrier
          (IsolatedGeometricComponents.intersection X.carrier W.val A.val),
        TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
          (GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
              (Principal.ChartComponentSum.germ X W.val g hg (i, true) x) D -
            GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
              (Principal.ChartComponentSum.germ X W.val g hg (i, false) x) D) := by
  refine (coefficient X m p k W g hg a hp i A hAa A₀ hA C x hx hxA hvx).trans ?_
  refine (congrArg₂ (fun u v : ℚ => u - v)
    (Principal.ChartComponentSum.equation X m p k W g hg a hp (i, true) A hAa A₀ hA C x hx hxA hvx)
    (Principal.ChartComponentSum.equation X m p k W g hg a hp (i, false) A hAa A₀ hA C x hx hxA hvx)).trans ?_
  simp only [mul_sub, Finset.sum_sub_distrib]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalChartEuler
