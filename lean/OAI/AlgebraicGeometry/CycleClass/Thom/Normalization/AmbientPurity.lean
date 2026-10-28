import OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupportDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ClosedSupportPurity

/-! # Ambient Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientPurity.Constructions

noncomputable section

/-! The singular image of the normalization can be removed from the
ambient variety without changing cohomology in the principal-divisor degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open
  NestedSupportDimension.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

def normalizationExceptionalClosed : Closeds V.carrier :=
  ⟨Geometric.GenericPoint.reducedSupportι W '' SmoothLocus.Constructions.Open.normalizationSingularImage (Geometric.GenericPoint.reducedSupportScheme W)
      (Geometric.SupportFiniteType.supportStructureMap W V.structureMap),
    (Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.isClosedMap _
      (SmoothLocus.Constructions.Open.normalizationSingularImage (Geometric.GenericPoint.reducedSupportScheme W)
        (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)).isClosed⟩

theorem normalizationExceptional_codimension (Z : IrreducibleCloseds V.carrier)
    (hZ : (Z : Set V.carrier) ⊆ normalizationExceptionalClosed V W) :
    Geometric.DimensionCycles.dimensionCodimension V W + 2 ≤ Geometric.DimensionCycles.dimensionCodimension V Z := by
  let S := Geometric.GenericPoint.reducedSupportScheme W
  let f := Geometric.SupportFiniteType.supportStructureMap W V.structureMap
  let : IsFinite (Scheme.Constructions.normalizationMap S) := Scheme.Constructions.normalizationMap_isFinite S f
  have hz : irreducibleSetEquivPoints Z ∈ (Z : Set V.carrier) := by
    have h := subset_closure (Set.mem_singleton (irreducibleSetEquivPoints Z))
    change irreducibleSetEquivPoints Z ∈
      (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z) : Set V.carrier) at h
    simpa only [OrderIso.symm_apply_apply] using h
  obtain ⟨x, hx, he⟩ := hZ hz
  obtain ⟨y, hy, hey⟩ := hx
  have hheight : 1 < coheight x := hey ▸
    SmoothLocus.Constructions.normalization_singular_image_coheight_gt_one S f y hy
  have hd := NestedSupportDimension.Constructions.supportPoint_dimension_add_two_le V.structureMap W x hheight
  rw [he, OrderIso.symm_apply_apply] at hd
  have hw := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V W
  have hzdim := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
  omega

/-- The actual ordinary cohomology restriction is invertible in degree
twice the codimension of a principal divisor on W. -/
theorem normalizationExceptional_cohomologyRestriction_isIso :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹'
        (normalizationExceptionalClosed V W : Set V.carrier))ᶜ
      ((Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1))) := by
  apply ProperImage.ClosedSupportPurity.Constructions.Construction.closedComplement_cohomologyRestriction_isIso
  intro Z hZ
  have h := normalizationExceptional_codimension V W Z hZ
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientPurity.Constructions
