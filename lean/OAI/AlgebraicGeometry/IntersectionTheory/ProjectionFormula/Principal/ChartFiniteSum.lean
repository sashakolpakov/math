import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartContributing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! # Chart Finite Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartFiniteSum

noncomputable section

/-! The full local pairing with the original principal-divisor
cycle is the finite difference of the chart numerator and denominator
weighted intersection sums. -/

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
    ∑ z ∈ F (i, true) ∪ F (i, false),
      (Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) (ChartEquations.numerator X W.val g hg i) z -
        Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) (ChartEquations.denominator X W.val g hg i) z) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z) A C := by
  let T := F (i, true) ∪ F (i, false)
  have hdata (z : T) : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ z.val.asIdeal ∧
      X.supportCodimension (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z.val) = k + 1 := by
    rcases Finset.mem_union.mp z.property with hz | hz
    · exact ⟨(hF (i, true) z.val hz).1, (hF (i, true) z.val hz).2.2⟩
    · exact ⟨(hF (i, false) z.val hz).1, (hF (i, false) z.val hz).2.2⟩
  let D : T → X.DimensionCycleSupport (k + 1) :=
    fun z => ⟨Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z.val, (hdata z).2⟩
  have hD : Function.Injective D := by
    intro z w he
    apply Subtype.ext
    exact Affine.PrimeCodimension.injective (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) (congrArg Subtype.val he)
  let b := ClosedSectionCycle.principalCycle X (k + 1) W.val g
  let e := fun B : X.DimensionCycleSupport (k + 1) => CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A C
  let w := fun z : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) =>
    Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) (ChartEquations.numerator X W.val g hg i) z -
      Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) (ChartEquations.denominator X W.val g hg i) z
  have hcoeff (z : T) (_ : z ∈ (Finset.univ : Finset T)) : b (D z) = w z.val := by
    rw [ClosedSectionCycle.principalCycle_apply]
    exact ChartCoefficient.coefficient X W.val g hg i z.val (hdata z).1 (D z).val
      (irreducibleSetEquivPoints.apply_symm_apply (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z.val)).symm
  have hmissing (B : X.DimensionCycleSupport (k + 1)) (hB : B ∉ Finset.univ.image D) : b B * e B = 0 := by
    by_cases hb : b B = 0
    · rw [hb, zero_mul]
    by_cases he : e B = 0
    · rw [he, mul_zero]
    obtain ⟨z, hz, hzB⟩ := ChartContributing.exists_prime X k W g hg F hout i x A C hx B
      (Finsupp.mem_support_iff.mpr hb) he
    exact (hB (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, Subtype.ext hzB⟩)).elim
  have he := Finite.MultiplicitySum.LocalCycle.reindex b e Finset.univ D hD (fun z => w z.val) hcoeff hmissing
  exact he.trans (Finset.sum_coe_sort T
    (fun z => w z * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Affine.FiltrationAvoidance.support (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) z) A C))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartFiniteSum
