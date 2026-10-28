import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.DescentPosition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportRepresentative
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Principal

/-! # Chart Contributing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartContributing

noncomputable section

/-! Every principal-divisor component that contributes to a local
intersection appears in the fixed numerator or denominator prime list
of any chart containing that intersection point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem exists_prime (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
    (hout : DescentPosition.Outside X k W.val g hg F)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (A C : IrreducibleCloseds X.carrier) (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C)
    (B : X.DimensionCycleSupport (k + 1))
    (hB : B ∈ (ClosedSectionCycle.principalCycle X (k + 1) W.val g).support)
    (hI : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A C ≠ 0) :
    ∃ z : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i), z ∈ F (i, true) ∪ F (i, false) ∧
      Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z = B.val := by
  have hBC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B.val : Set X.carrier) := by
    by_contra h
    exact hI (dite_eq_right (fun hh => h hh.1))
  have hxB : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x ∈ (B.val : Set X.carrier) :=
    (congrArg (fun y : X.carrier => y ∈ (B.val : Set X.carrier)) hx).mpr hBC
  obtain ⟨z, hz, hzB, _⟩ := Affine.SupportRepresentative.exists_prime (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) B.val x hxB
  have hBW := Support.Principal.subset X k W g B hB
  have hzW : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z ∈ (W.val : Set X.carrier) :=
    (congrArg (fun y : X.carrier => y ∈ (W.val : Set X.carrier)) hz).mpr
      (hBW (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem)
  have hvz : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ z.asIdeal := by
    apply (Affine.Prime.mem_iff (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) z).mp
    exact (congrArg (fun D : IrreducibleCloseds X.carrier => Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z ∈ (D : Set X.carrier))
      (Affine.ChartGerm.FiniteSupportCharts.prime_support X W.val i)).mpr hzW
  refine ⟨z, ?_, hzB⟩
  by_contra hzout
  have hzt : z ∉ F (i, true) := fun h => hzout (Finset.mem_union_left _ h)
  have hzf : z ∉ F (i, false) := fun h => hzout (Finset.mem_union_right _ h)
  have hdim : X.supportCodimension (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z) = k + 1 :=
    (congrArg X.supportCodimension hzB).trans B.property
  have hnum : Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
      (ChartEquations.numerator X W.val g hg i) z = 0 := hout (i, true) z hdim hzt
  have hden : Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i)
      (ChartEquations.denominator X W.val g hg i) z = 0 := hout (i, false) z hdim hzf
  apply Finsupp.mem_support_iff.mp hB
  rw [ClosedSectionCycle.principalCycle_apply,
    ChartCoefficient.coefficient X W.val g hg i z hvz B.val hz, hnum, hden, sub_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartContributing
