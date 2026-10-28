import OAI.AlgebraicGeometry.Cycles.Functoriality.BoundaryContainment
import OAI.AlgebraicGeometry.Cycles.Functoriality.CycleProjection

/-! # Support -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.Support.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem supportImageOverMap_inclusion {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    ImageOpen.Construction.supportImageOverMap f hf p q hdeg Z hdim ≫ (ImageOpen.Construction.imageCycleSupport f p q hdeg Z hdim).toAmbient =
      Z.toAmbient ≫ f := by
  apply Over.OverMorphism.ext
  exact SupportMap.Construction.supportImageMap_inclusion f hf Z

theorem regularAmbientMap_eq_schemeMap {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    CycleProjection.Construction.regularAmbientMap Z = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Z.regularToSupport ≫ Z.toAmbient) := by
  ext x
  rfl

/-- The map from a smooth support open to the ambient variety factors
through its canonical regular locus by the actual scheme morphisms. -/
theorem smoothSupportOpen_ambient_map {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ImageOpen.Construction.smoothSupportOpenToRegular Z U hU) ≫ CycleProjection.Construction.regularAmbientMap Z =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (AnalyticRestriction.Construction.openSchemeInclusion Z.toOver U ≫ Z.toAmbient) := by
  have h : ImageOpen.Construction.smoothSupportOpenToRegular Z U hU ≫ (Z.regularToSupport ≫ Z.toAmbient) =
      AnalyticRestriction.Construction.openSchemeInclusion Z.toOver U ≫ Z.toAmbient := by
    rw [← Category.assoc, ImageOpen.Construction.smoothSupportOpenToRegular_inclusion]
  rw [regularAmbientMap_eq_schemeMap]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map_comp (ImageOpen.Construction.smoothSupportOpenToRegular Z U hU)
    (Z.regularToSupport ≫ Z.toAmbient)).symm.trans
    (congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map k) h)

/-- The native analytic covering square is the realization of the
restriction square for the actual support morphism. -/
theorem restricted_support_cover_square
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.toOver ⟶ T.toOver)
    (hi : i ≫ T.toAmbient = Z.toAmbient ≫ f)
    (U : T.scheme.Opens) (hT : U ≤ T.structureMap.smoothLocus)
    (hZ : i.left ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus) :
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ImageOpen.Construction.smoothSupportOpenToRegular Z (i.left ⁻¹ᵁ U) hZ) ≫
        CycleProjection.Construction.regularAmbientMap Z) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (AnalyticRestriction.Construction.restrictedSchemeMap i U) ≫
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ImageOpen.Construction.smoothSupportOpenToRegular T U hT) ≫ CycleProjection.Construction.regularAmbientMap T) := by
  have h : (AnalyticRestriction.Construction.openSchemeInclusion Z.toOver (i.left ⁻¹ᵁ U) ≫ Z.toAmbient) ≫ f =
      AnalyticRestriction.Construction.restrictedSchemeMap i U ≫ (AnalyticRestriction.Construction.openSchemeInclusion T.toOver U ≫ T.toAmbient) := by
    rw [Category.assoc, ← hi, ← Category.assoc, ← AnalyticRestriction.Construction.restrictedSchemeMap_inclusion, Category.assoc]
  rw [smoothSupportOpen_ambient_map, smoothSupportOpen_ambient_map]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map_comp
    (AnalyticRestriction.Construction.openSchemeInclusion Z.toOver (i.left ⁻¹ᵁ U) ≫ Z.toAmbient) f).symm.trans
    ((congrArg (fun k => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map k) h).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map_comp (AnalyticRestriction.Construction.restrictedSchemeMap i U)
        (AnalyticRestriction.Construction.openSchemeInclusion T.toOver U ≫ T.toAmbient)))

/-- The smooth support open contains the entire regular preimage of
a compact set retained in the ambient boundary complement. -/
theorem regularPreimage_subset_smoothSupportOpen_range
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus)
    (L : Set V.analyticSpace) (hL : L ⊆ TraceDetection.Construction.algebraicComplementOpen V (ImageOpen.Construction.supportOpenBoundary Z U)) :
    CycleProjection.Construction.regularAmbientMap Z ⁻¹' L ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageOpen.Construction.smoothSupportOpenToRegular Z U hU)) := by
  rw [ImageOpen.Construction.smoothSupportOpenToRegular_range]
  intro x hx
  exact BoundaryContainment.Construction.supportPoint_mem_open_of_boundaryComplement Z U (Z.regularAnalyticInclusion x) (hL hx)

/-- The same containment for the source, using the commuting support map. -/
theorem sourceRegularPreimage_subset_smoothSupportOpen_range
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.toOver ⟶ T.toOver)
    (hi : i ≫ T.toAmbient = Z.toAmbient ≫ f)
    (U : T.scheme.Opens) (hZ : i.left ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus)
    (L : Set Y.analyticSpace) (hL : L ⊆ TraceDetection.Construction.algebraicComplementOpen Y (ImageOpen.Construction.supportOpenBoundary T U)) :
    CycleProjection.Construction.regularAmbientMap Z ⁻¹' (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' L) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageOpen.Construction.smoothSupportOpenToRegular Z (i.left ⁻¹ᵁ U) hZ)) := by
  rw [ImageOpen.Construction.smoothSupportOpenToRegular_range]
  intro x hx
  have hpoint : T.analyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Z.regularAnalyticInclusion x)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (CycleProjection.Construction.regularAmbientMap Z x) := by
    exact congrArg (fun k : Z.toOver ⟶ Y.toOver => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (Z.regularAnalyticInclusion x)) hi
  have hmem := BoundaryContainment.Construction.supportPoint_mem_open_of_boundaryComplement T U
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Z.regularAnalyticInclusion x)) (by rw [hpoint]; exact hL hx)
  exact hmem

end

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The whole integral variety as an actual irreducible closed support. -/
def fullIrreducibleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IrreducibleCloseds V.carrier :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ V.carrier, isClosed_univ⟩

instance fullIrreducibleSupport_inclusion_isIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIso (CycleClass.Geometric.GenericPoint.reducedSupportι (fullIrreducibleSupport V)) := by
  let : Surjective (CycleClass.Geometric.GenericPoint.reducedSupportι (fullIrreducibleSupport V)) := ⟨by
    apply Set.range_eq_univ.mp
    exact CycleClass.Geometric.GenericPoint.range_reducedSupportι (fullIrreducibleSupport V)⟩
  exact isIso_of_isClosedImmersion_of_surjective _

theorem fullIrreducibleSupport_codimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    CycleClass.Geometric.DimensionCycles.dimensionCodimension V (fullIrreducibleSupport V) = 0 := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (CycleClass.Geometric.GenericPoint.reducedSupportι (fullIrreducibleSupport V)) V.structureMap
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.GenericPoint.reducedSupportι (fullIrreducibleSupport V) ≫ V.structureMap) = 0
  rw [h, Nat.sub_self]

/-- The full variety as a codimension-zero cycle support. -/
def fullCycleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 0 :=
  ⟨fullIrreducibleSupport V, fullIrreducibleSupport_codimension V⟩

instance fullCycleSupport_inclusion_isIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIso (fullCycleSupport V).inclusion :=
  inferInstanceAs (IsIso (CycleClass.Geometric.GenericPoint.reducedSupportι (fullIrreducibleSupport V)))

instance fullCycleSupport_toAmbient_isIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIso (fullCycleSupport V).toAmbient := by
  let : IsIso (fullCycleSupport V).inclusion := fullCycleSupport_inclusion_isIso V
  let e : (fullCycleSupport V).scheme ≅ V.carrier := asIso (fullCycleSupport V).inclusion
  exact (Over.isoMk (f := (fullCycleSupport V).toOver) (g := V.toOver)
    e rfl).isIso_hom

instance fullCycleSupport_structureMap_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Smooth (fullCycleSupport V).structureMap := by
  let : Smooth V.structureMap := V.presentation.smooth
  change Smooth ((fullCycleSupport V).inclusion ≫ V.structureMap)
  infer_instance

instance fullCycleSupport_regularToSupport_isIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIso (fullCycleSupport V).regularToSupport := by
  let Z := fullCycleSupport V
  let : Surjective (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap) := ⟨by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial⟩
  let : IsIso (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let : IsIso Z.regularToSupport.left := inferInstanceAs (IsIso (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap))
  exact (Over.isoMk (f := Z.regularOver) (g := Z.toOver)
    (asIso (CycleClass.Geometric.SmoothStratum.smoothStratumι Z.structureMap)) rfl).isIso_hom

instance fullCycleSupport_regularAmbientMap_isIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIso (CycleProjection.Construction.regularAmbientMap (fullCycleSupport V)) := by
  rw [regularAmbientMap_eq_schemeMap]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.mapIso
    (asIso ((fullCycleSupport V).regularToSupport ≫ (fullCycleSupport V).toAmbient))).isIso_hom

theorem fullCycleSupport_regularAmbientOpen_eq_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (fullCycleSupport V).regularAmbientOpen = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CycleProjection.Construction.regularAmbientMap (fullCycleSupport V))).2 x
  exact hz ▸ ((fullCycleSupport V).regularComplementInclusion z).property

theorem fullCycleSupport_regularDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (fullCycleSupport V).regularComplexDimension = V.complexDimension := by
  have h := (fullCycleSupport V).regularComplexDimension_add_codimension
  simpa only [Nat.add_zero] using h

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.Support.Construction
