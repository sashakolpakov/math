import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum

/-! # Support Open -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SupportOpen

noncomputable section

/-! The actual smooth open of an integral support has its native
support dimension and contains its generic point in the ambient image. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (W : IrreducibleCloseds X)

abbrev space : Scheme := CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)

abbrev base : space f W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Geometric.SmoothStratum.smoothStratumToBase (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)

abbrev inclusion : space f W ⟶ X := CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι W (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)

theorem over_base : inclusion f W ≫ f = base f W := Category.assoc _ _ _

theorem dimension : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (base f W) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f :=
  Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)

instance relativeDimension : SmoothOfRelativeDimension (Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f) (base f W) := by
  have he : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (base f W) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f :=
    (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension (base f W)).symm.trans (dimension f W)
  have h := Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension (base f W)
  rw [he] at h
  exact h

theorem generic_in_range : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ Set.range (inclusion f W) := by
  have hx := (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f).genericPoint_mem_smoothLocus_of_perfectField
  refine ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), hx⟩, ?_⟩
  exact CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W

theorem range_subset : Set.range (inclusion f W) ⊆ (W : Set X) := by
  rintro _ ⟨x, rfl⟩
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f) x, rfl⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SupportOpen
