/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinates

/-! # Normal Coordinates At -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Normal coordinates for smooth closed immersions

-/

open _root_.CategoryTheory _root_.Topology Filter

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- The normal parametrization is complex analytic at its center. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  let P := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z
  exact ((ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z).comp
    (f := (ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker))
    (x := (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0))
    ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker).analyticAt _)).add
      ((P.ker.subtypeL.analyticAt _).comp
        ((ContinuousLinearMap.snd ℂ (Fin m → ℂ) P.ker).analyticAt _))

/-- The inverse normal coordinates are complex analytic as well, by the analytic inverse
function theorem applied to the invertible complex derivative. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart_symm :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z)) := by
  let P := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z
  let e := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z
  have ha := ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z
  have hd := (Analysis.Foundations.SplitDerivativeNormalChart.HasStrictFDerivAt.add_kernel ha.hasStrictFDerivAt) P
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)
  have hder : fderiv ℂ e (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) =
      ((Analysis.Foundations.SplitDerivativeNormalChart.ContinuousLinearMap.splitKernelEquiv (fderiv ℂ (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z))) P
        (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)).toContinuousLinearMap :=
    hd.hasFDerivAt.fderiv
  have h := e.analyticAt_symm'
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_source X Y i m d z)
    (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart X Y i m d z) hder
  simpa only [e, ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_apply, Submodule.coe_zero, add_zero,
    ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center] using h

theorem ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_source :
    ComplexPoint.Basic.Point.map i z ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).source :=
  ⟨⟨ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (ComplexPoint.Basic.Point.map i z),
      ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target X Y i m d z⟩,
    (ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose_spec.2.1⟩

/-- The chart flattens the whole geometric support. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_range_iff (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z y).2 = 0 :=
  (ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose_spec.2.2 y hy.2

theorem ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source :
    ComplexPoint.Basic.Point.map i z ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_source]
  exact ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_source X Y i m d z

/-- The support is exactly the zero-normal plane throughout the chart source. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z y).2 = 0 := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_source] at hy
  simpa only [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_apply, ContinuousLinearEquiv.map_eq_zero_iff] using
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_mem_range_iff X Y i m d z y hy

end

end OAI.AlgebraicGeometry
