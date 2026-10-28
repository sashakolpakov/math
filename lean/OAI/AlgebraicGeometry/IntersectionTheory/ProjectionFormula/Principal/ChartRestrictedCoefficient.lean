import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartComponentSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRatio
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.WeightDifference

/-! # Chart Restricted Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartRestrictedCoefficient

noncomputable section

section

/-! The fixed numerator and denominator on a moved intersection
component represent its actual restricted rational function everywhere
in the chart, through the native closed-immersion maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Function

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem germ_unit_congr (X : Scheme) (U : X.Opens) (x y : X) (h : x = y)
    (hx : x ∈ U) (hy : y ∈ U) (r : Γ(X, U)) :
    IsUnit (X.presheaf.germ U x hx r) ↔ IsUnit (X.presheaf.germ U y hy r) := by
  subst y
  rfl

theorem ratio (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (D : X.DimensionCycleSupport (p + k)) (hDA : D.val ≤ A.val) (hDW : D.val ≤ W.val)
    (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (NestedGenericRestriction.point X.carrier D.val W.val hDW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
    (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)) (hxD : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x ∈ (D.val : Set X.carrier)) :
    Support.LocalFraction.Restriction.toFunctionField X.carrier D.val (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hxD
      (ChartComponentSum.germ X W.val g hg (i, true) x) ≠ 0 ∧
    Support.LocalFraction.Restriction.toFunctionField X.carrier D.val (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hxD
      (ChartComponentSum.germ X W.val g hg (i, false) x) ≠ 0 ∧
    NestedGenericRestriction.function X.carrier D.val W.val hDW g hunit =
      Support.LocalFraction.Restriction.toFunctionField X.carrier D.val (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hxD
        (ChartComponentSum.germ X W.val g hg (i, true) x) /
      Support.LocalFraction.Restriction.toFunctionField X.carrier D.val (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hxD
        (ChartComponentSum.germ X W.val g hg (i, false) x) := by
  obtain ⟨z, hz, _, _⟩ := Affine.SupportRepresentative.exists_prime (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) D.val x hxD
  have hηD : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (D.val : Set X.carrier) :=
    (D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).mem
  have hηA := hDA hηD
  have hηW := hDW hηD
  have hηU : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ Affine.ChartGerm.FiniteSupportCharts.opens X W.val i := hz ▸ ChartComponentSum.mem_opens X W.val i z
  have hvz : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ z.asIdeal := by
    apply (Affine.Prime.mem_iff (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) z).mp
    have hzW : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z ∈ (W.val : Set X.carrier) := hz.symm ▸ hηW
    exact (congrArg (fun B : IrreducibleCloseds X.carrier => Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z ∈ (B : Set X.carrier))
      (Affine.ChartGerm.FiniteSupportCharts.prime_support X W.val i)).mpr hzW
  have hu (b : Bool) : IsUnit (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hηU
      (ChartEquations.equation X W.val g hg (i, b))) :=
    (germ_unit_congr X.carrier (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i z) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hz
      (ChartComponentSum.mem_opens X W.val i z) hηU _).mp
        (ChartComponentSum.GenericUnit.unit X m p k W g hg a hp (i, b) A hAa D z hz hηA hvz)
  have hfrac := ChartEquations.fraction X W.val g hg i (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hηW hηU
  exact NestedGenericRatio.Section.ratio X.carrier D.val W.val hDW hηD hηW g hunit
    (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) hηU (ChartEquations.numerator X W.val g hg i) (ChartEquations.denominator X W.val g hg i)
    (hu true) (hu false) hfrac.2.2 (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hxD
    (ChartComponentSum.mem_opens X W.val i x)

end Function

end

/-! On every moved intersection component, the numerator-minus-
denominator weight is exactly the divisor coefficient of the actual
restricted rational function, including points outside the support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem weight_coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (D C : IrreducibleCloseds X.carrier) (x : X.carrier) (hx : x = CycleClass.Thom.IntersectionGeometry.supportPoint C)
    (a b : X.carrier.presheaf.stalk x) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme D).functionField)
    (hfrac : ∀ hxD : x ∈ (D : Set X.carrier),
      Support.LocalFraction.Restriction.toFunctionField X.carrier D x hxD a ≠ 0 ∧ Support.LocalFraction.Restriction.toFunctionField X.carrier D x hxD b ≠ 0 ∧
      g = Support.LocalFraction.Restriction.toFunctionField X.carrier D x hxD a / Support.LocalFraction.Restriction.toFunctionField X.carrier D x hxD b) :
    GlobalParameterSum.Weights.weight X.carrier x a D - GlobalParameterSum.Weights.weight X.carrier x b D =
      CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X D g C := by
  classical
  by_cases hxD : x ∈ (D : Set X.carrier)
  · have hηD : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (D : Set X.carrier) := hx ▸ hxD
    have hf := hfrac hxD
    have he := WeightDifference.order X.carrier D x hxD a b hf.1 hf.2.1 g hf.2.2
    rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hηD]
    refine he.trans ?_
    apply congrArg (fun y => ((CycleClass.Geometric.GenericPoint.reducedSupportScheme D).ord g y : ℚ))
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι D).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact hx
  · have hηD : CycleClass.Thom.IntersectionGeometry.supportPoint C ∉ (D : Set X.carrier) := fun h => hxD (hx.symm ▸ h)
    rw [GlobalParameterSum.Weights.weight, dite_eq_right hxD, GlobalParameterSum.Weights.weight, dite_eq_right hxD, sub_self]
    rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hηD]

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (D : X.DimensionCycleSupport (p + k)) (hDA : D.val ≤ A.val) (hDW : D.val ≤ W.val)
    (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (NestedGenericRestriction.point X.carrier D.val W.val hDW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
    (C : IrreducibleCloseds X.carrier) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C) :
    GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
        (ChartComponentSum.germ X W.val g hg (i, true) x) D.val -
      GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
        (ChartComponentSum.germ X W.val g hg (i, false) x) D.val =
      CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X D.val
        (NestedGenericRestriction.function X.carrier D.val W.val hDW g hunit) C := by
  apply weight_coefficient X D.val C (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hx
  intro hxD
  exact Function.ratio X m p k W g hg a hp i A hAa D hDA hDW hunit x hxD

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartRestrictedCoefficient
