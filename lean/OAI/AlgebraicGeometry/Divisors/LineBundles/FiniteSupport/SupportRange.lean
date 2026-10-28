import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Range

/-! # Support Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.SupportRange.BundleCycles

noncomputable section

/-! The actual finite support cover contains every point of the full support over the retained ambient open, including all branches. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {S Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType S.hom] [LocallyOfFiniteType Y.hom]
  (g : S ⟶ Y) [IsFinite g.left] (Z : IrreducibleCloseds S.left)

theorem finiteSupportSourceAmbientMap_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Cover.BundleCycles.finiteSupportSourceOver g Z)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) x =
      CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S Z)
          (Cover.BundleCycles.finiteSupportSourceOpen g Z)) x) := by
  have h := congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (Cover.BundleCycles.finiteSupportSourceToRegular_ambient g Z)
  exact h.trans (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S Z) (Cover.BundleCycles.finiteSupportSourceOpen g Z))
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S Z) x)

theorem finiteSupportSourceAmbientMap_range_subset_support : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceAmbientMap g Z)) ⊆
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S Z)
    (Cover.BundleCycles.finiteSupportSourceOpen g Z)) x, (finiteSupportSourceAmbientMap_point g Z x).symm⟩

theorem finiteSupportFullSupport_point_mem_cover_range (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z))
    (hU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g y ∈ Cover.BundleCycles.finiteSupportRetainedOpen g Z) :
    y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceAmbientMap g Z)) := by
  obtain ⟨t, rfl⟩ := hy
  have ht := Range.BundleCycles.finiteSupportSourceAnalyticPoint_mem_open g Z t hU
  let i := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S Z) (Cover.BundleCycles.finiteSupportSourceOpen g Z)
  have hr : t ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion i]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t ∈ Set.range ((Cover.BundleCycles.finiteSupportSourceOpen g Z).ι)
    rw [Scheme.Opens.range_ι]
    exact ht
  obtain ⟨x, hx⟩ := hr
  refine ⟨x, ?_⟩
  exact (finiteSupportSourceAmbientMap_point g Z x).trans
    (congrArg (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z) hx)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.SupportRange.BundleCycles
