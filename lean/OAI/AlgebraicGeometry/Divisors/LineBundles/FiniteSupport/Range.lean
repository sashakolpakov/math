import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace

/-! # Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Range.BundleCycles

noncomputable section

/-! The actual finite support cover contains every regular support
point over the complement of its omitted algebraic boundary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportSourceAnalyticPoint_mem_open (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z))
    (hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z y) ∈ Cover.BundleCycles.finiteSupportRetainedOpen f Z) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ Cover.BundleCycles.finiteSupportSourceOpen f Z :=
  Cover.BundleCycles.finiteSupportSourcePoint_mem_open f Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y) hy

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetAnalyticPoint_mem_open (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)))
    (hy : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) y ∈ Cover.BundleCycles.finiteSupportRetainedOpen f Z) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ Cover.BundleCycles.finiteSupportGoodOpen f Z :=
  Cover.BundleCycles.finiteSupportTargetPoint_mem_open f Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y) hy

theorem finiteSupportSourceRegular_range (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hL : L ⊆ Cover.BundleCycles.finiteSupportRetainedOpen f Z) :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z ⁻¹' (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' L) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceToRegular f Z)) := by
  have hr := CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_range X Z (Cover.BundleCycles.finiteSupportSourceOpen f Z)
    (Cover.BundleCycles.finiteSupportSourceOpen_smoothLocus f Z)
  change Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceToRegular f Z)) = _ at hr
  rw [hr]
  intro x hx
  apply finiteSupportSourceAnalyticPoint_mem_open f Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z) x)
  have he : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z) x) = CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x := by
    have h := congrArg (fun k : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z ⟶ X => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x) (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport_ambient X Z)
    exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z) x).symm.trans h
  rw [he]
  exact hL hx

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetRegular_range (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hL : L ⊆ Cover.BundleCycles.finiteSupportRetainedOpen f Z) :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) ⁻¹' L ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetToRegular f Z)) := by
  have hr := CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_range Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (Cover.BundleCycles.finiteSupportGoodOpen f Z)
    (Cover.BundleCycles.finiteSupportTargetOpen_smoothLocus f Z)
  change Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetToRegular f Z)) = _ at hr
  rw [hr]
  intro x hx
  apply finiteSupportTargetAnalyticPoint_mem_open f Z
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) x)
  have he : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) x) = CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) x := by
    have h := congrArg (fun k : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) ⟶ Y => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x)
      (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport_ambient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z))
    exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z))
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) x).symm.trans h
  rw [he]
  exact hL hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Range.BundleCycles
