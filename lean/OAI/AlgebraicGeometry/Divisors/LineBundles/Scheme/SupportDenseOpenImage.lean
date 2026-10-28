import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen

/-! # Support Dense Open Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportDenseOpenImage.BundleCycles

noncomputable section

/-! A genuine support open has the full original analytic support
image outside its actual omitted algebraic boundary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

omit [LocallyOfFiniteType X.hom] in
theorem schemeSupportOpenBoundary_preimage (W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens) :
    CycleClass.Geometric.GenericPoint.reducedSupportι Z ⁻¹' (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W : Set X.left) = (W : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))ᶜ := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [LocallyOfFiniteType X.hom] in
theorem schemeSupportPoint_mem_goodOpen (W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z))
    (hx : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z x ∈ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W).compl) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := by
  by_contra hn
  exact hx ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hn, rfl⟩

variable {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (j : T ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) [IsOpenImmersion j.left]
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z j.left.opensRange).compl)

include hU in
omit [LocallyOfFiniteType X.hom] in
theorem schemeSupportOpenImmersion_range :
    ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (j ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z))) =
      (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j x, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp j (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z) x).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    have hxb : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z x ∈ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z j.left.opensRange).compl :=
      hx.symm ▸ hU y.property
    have hxW := schemeSupportPoint_mem_goodOpen X Z j.left.opensRange x hxb
    have hr : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) := by
      rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion j]
      exact hxW
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, ?_⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hz]
    exact hx

include hU in
theorem schemeSupportOpenImmersion_regularImage [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (hR : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) :
    ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (j ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z))) =
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hR) :=
  (schemeSupportOpenImmersion_range X Z j U hU).trans (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_range X Z U hR).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportDenseOpenImage.BundleCycles
