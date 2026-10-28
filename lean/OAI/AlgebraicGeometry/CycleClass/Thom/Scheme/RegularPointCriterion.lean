import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen

/-! # Regular Point Criterion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularPointCriterion.Constructions

noncomputable section

/-! A point of an actual reduced support lies in its regular analytic image exactly when its underlying support point is in the genuine smooth locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

local instance : LocallyOfFinitePresentation (RegularSupport.Constructions.supportOver X Z).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Geometric.SupportFiniteType.supportStructureMap Z X.hom))

theorem regularToSupport_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SmoothSupportOpen.Constructions.regularToSupport X Z)) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' ((RegularSupport.Constructions.supportOver X Z).hom.smoothLocus : Set (RegularSupport.Constructions.supportOver X Z).left) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.supportOver X Z) → Geometric.GenericPoint.reducedSupportScheme Z) ⁻¹'
    Set.range (Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap Z X.hom)) = _
  rw [Geometric.SmoothStratum.range_smoothStratumι]
  rfl

theorem regularToSupport_point (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X Z)) :
    RegularSupport.Constructions.supportInclusion X Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SmoothSupportOpen.Constructions.regularToSupport X Z) x) = RegularSupport.Constructions.regularInclusion X Z x :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (SmoothSupportOpen.Constructions.regularToSupport X Z) (RegularSupport.Constructions.supportToAmbient X Z) x).symm.trans
    (congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (SmoothSupportOpen.Constructions.regularToSupport_ambient X Z))

theorem supportPoint_regular_iff (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.supportOver X Z)) :
    RegularSupport.Constructions.supportInclusion X Z x ∈ Set.range (RegularSupport.Constructions.regularInclusion X Z) ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (RegularSupport.Constructions.supportOver X Z).hom.smoothLocus := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SmoothSupportOpen.Constructions.regularToSupport X Z) t = x :=
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (RegularSupport.Constructions.supportToAmbient X Z)).injective
        ((regularToSupport_point X Z t).trans ht)
    exact (Set.ext_iff.mp (regularToSupport_range X Z) x).mp ⟨t, he⟩
  · intro hx
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp (regularToSupport_range X Z) x).mpr hx
    exact ⟨t, (regularToSupport_point X Z t).symm.trans (congrArg (RegularSupport.Constructions.supportInclusion X Z) ht)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularPointCriterion.Constructions
