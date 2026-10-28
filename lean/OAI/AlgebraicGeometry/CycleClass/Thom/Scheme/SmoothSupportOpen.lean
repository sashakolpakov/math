import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open

/-! # Smooth Support Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

noncomputable section

/-! Smooth support opens in arbitrary finite-type complex schemes, with
their actual native charts and the actual omitted algebraic boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

local instance : IsIntegral (RegularSupport.Constructions.supportOver X Z).left :=
  inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme Z))

def regularToSupport : RegularSupport.Constructions.regularOver X Z ⟶ RegularSupport.Constructions.supportOver X Z :=
  Over.homMk (Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap Z X.hom)) rfl

instance regularToSupport_open : IsOpenImmersion (regularToSupport X Z).left :=
  inferInstanceAs (IsOpenImmersion (Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap Z X.hom)))

theorem regularToSupport_ambient :
    regularToSupport X Z ≫ RegularSupport.Constructions.supportToAmbient X Z = RegularSupport.Constructions.regularToAmbient X Z := by
  apply Over.OverMorphism.ext
  rfl

def smoothOpenToRegular (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : U ≤ (Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus) :
    ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (RegularSupport.Constructions.supportOver X Z) U ⟶ RegularSupport.Constructions.regularOver X Z :=
  Over.homMk ((Geometric.GenericPoint.reducedSupportScheme Z).homOfLE hU) (by
    change (Geometric.GenericPoint.reducedSupportScheme Z).homOfLE hU ≫
      ((Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus.ι ≫ Geometric.SupportFiniteType.supportStructureMap Z X.hom) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

instance smoothOpenToRegular_open (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : U ≤ (Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus) :
    IsOpenImmersion (smoothOpenToRegular X Z U hU).left :=
  inferInstanceAs (IsOpenImmersion ((Geometric.GenericPoint.reducedSupportScheme Z).homOfLE hU))

theorem smoothOpenToRegular_inclusion (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : U ≤ (Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus) :
    smoothOpenToRegular X Z U hU ≫ regularToSupport X Z = ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (RegularSupport.Constructions.supportOver X Z) U := by
  apply Over.OverMorphism.ext
  exact (Geometric.GenericPoint.reducedSupportScheme Z).homOfLE_ι hU

theorem smoothOpenToRegular_ambient (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : U ≤ (Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus) :
    smoothOpenToRegular X Z U hU ≫ RegularSupport.Constructions.regularToAmbient X Z =
      ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (RegularSupport.Constructions.supportOver X Z) U ≫ RegularSupport.Constructions.supportToAmbient X Z := by
  rw [← regularToSupport_ambient, ← Category.assoc, smoothOpenToRegular_inclusion]

theorem supportOpen_dimension (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens) [Nonempty U] :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (RegularSupport.Constructions.supportOver X Z) U).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (RegularSupport.Constructions.regularOver X Z).hom := by
  let : IsIntegral (RegularSupport.Constructions.supportOver X Z).left := inferInstanceAs (IsIntegral (Geometric.GenericPoint.reducedSupportScheme Z))
  let : IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (RegularSupport.Constructions.supportOver X Z) U).left := inferInstanceAs (IsIntegral U.toScheme)
  let : LocallyOfFiniteType (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (RegularSupport.Constructions.supportOver X Z) U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Geometric.SupportFiniteType.supportStructureMap Z X.hom))
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ Geometric.SupportFiniteType.supportStructureMap Z X.hom) = _
  rw [Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open, RegularSupport.Constructions.regularDimension_eq]
  rfl

theorem smoothOpenToRegular_range (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : U ≤ (Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus) :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothOpenToRegular X Z U hU)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToSupport X Z) ⁻¹'
        (ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen (RegularSupport.Constructions.supportOver X Z) U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.supportOver X Z))) := by
  have hcomp (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (RegularSupport.Constructions.supportOver X Z) U)) :
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToSupport X Z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothOpenToRegular X Z U hU) x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (RegularSupport.Constructions.supportOver X Z) U) x := by
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, smoothOpenToRegular_inclusion]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToSupport X Z)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothOpenToRegular X Z U hU) z) ∈
        (ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen (RegularSupport.Constructions.supportOver X Z) U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.supportOver X Z)))
    rw [hcomp]
    exact (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph (RegularSupport.Constructions.supportOver X Z) U z).property
  · intro hx
    let z := (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph (RegularSupport.Constructions.supportOver X Z) U).symm
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToSupport X Z) x, hx⟩
    refine ⟨z, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
      (regularToSupport X Z)).injective ?_⟩
    rw [hcomp]
    exact congrArg Subtype.val ((ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph (RegularSupport.Constructions.supportOver X Z) U).apply_symm_apply
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToSupport X Z) x, hx⟩)

/-- The part of the actual reduced support omitted by the chosen open. -/
def supportOpenBoundary (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens) : Closeds X.left :=
  ⟨Geometric.GenericPoint.reducedSupportι Z '' (U : Set (Geometric.GenericPoint.reducedSupportScheme Z))ᶜ,
    (Geometric.GenericPoint.reducedSupportι Z).isClosedMap _ U.isOpen.isClosed_compl⟩

omit [LocallyOfFiniteType X.hom] in
theorem supportOpenBoundary_subset (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens) :
    (supportOpenBoundary X Z U : Set X.left) ⊆ Z := by
  rintro x ⟨z, _, rfl⟩
  rw [← Geometric.GenericPoint.range_reducedSupportι Z]
  exact Set.mem_range_self z

omit [LocallyOfFiniteType X.hom] in
theorem genericPoint_not_mem_boundary (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : genericPoint (Geometric.GenericPoint.reducedSupportScheme Z) ∈ U) :
    irreducibleSetEquivPoints Z ∉ supportOpenBoundary X Z U := by
  rintro ⟨z, hz, he⟩
  have he' : z = genericPoint (Geometric.GenericPoint.reducedSupportScheme Z) :=
    (Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.injective (he.trans (Geometric.GenericPoint.reducedSupport_genericPoint_eq Z).symm)
  exact hz (he'.symm ▸ hU)

theorem supportOpenBoundary_dimension_lt (U : (Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (hU : genericPoint (Geometric.GenericPoint.reducedSupportScheme Z) ∈ U)
    (A : IrreducibleCloseds X.left) (hA : (A : Set X.left) ⊆ supportOpenBoundary X Z U) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom := by
  have hle : A ≤ Z := hA.trans (supportOpenBoundary_subset X Z U)
  have hne : A ≠ Z := by
    intro he
    subst A
    have hη : irreducibleSetEquivPoints Z ∈ (Z : Set X.left) := by
      rw [← Geometric.GenericPoint.reducedSupport_genericPoint_eq Z, ← Geometric.GenericPoint.range_reducedSupportι Z]
      exact Set.mem_range_self _
    exact genericPoint_not_mem_boundary X Z U hU
      (hA hη)
  exact Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt A Z X.hom (lt_of_le_of_ne hle hne)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions
