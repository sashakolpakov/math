import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportDenseOpenImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover

/-! # Good -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Good.BundleCycles

noncomputable section

section

/-! The actual degree-one normalization cover of a general integral
support retains the original support image and dimension on its good open. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

local instance normalizationGenericSupportIntegral : IsIntegral (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z).left :=
  inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))

local instance normalizationGenericSupportFiniteType : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z).hom :=
  inferInstanceAs (LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom))

abbrev schemeNormalizationGoodOpen := CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)
abbrev schemeNormalizationCoverSource := CycleClass.Thom.Normalization.GenericCover.Constructions.sourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)
abbrev schemeNormalizationCoverTarget := CycleClass.Thom.Normalization.GenericCover.Constructions.targetOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)
abbrev schemeNormalizationGenericCover := CycleClass.Thom.Normalization.GenericCover.Constructions.coverMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)

def schemeNormalizationTargetToSupport : schemeNormalizationCoverTarget X Z ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) (schemeNormalizationGoodOpen X Z)

instance schemeNormalizationTargetToSupport_open : IsOpenImmersion (schemeNormalizationTargetToSupport X Z).left :=
  inferInstanceAs (IsOpenImmersion (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) (schemeNormalizationGoodOpen X Z)).left)

def schemeNormalizationGoodTargetToAmbient : schemeNormalizationCoverTarget X Z ⟶ X :=
  schemeNormalizationTargetToSupport X Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z

instance schemeNormalizationGoodTargetToAmbient_immersion : IsImmersion (schemeNormalizationGoodTargetToAmbient X Z).left := by
  change IsImmersion ((schemeNormalizationTargetToSupport X Z).left ≫ (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z).left)
  infer_instance

def schemeNormalizationOmittedBoundary : Closeds X.left := CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z (schemeNormalizationGoodOpen X Z)
def schemeNormalizationGoodAmbient : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (schemeNormalizationOmittedBoundary X Z).compl

theorem schemeNormalizationGoodAmbient_regular :
    (schemeNormalizationGoodAmbient X Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z := by
  intro x hx hbad
  obtain ⟨y, hy, he⟩ := hbad
  exact hx ⟨y, fun h => hy (CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen_subset_smoothLocus (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) h), he⟩

theorem schemeNormalizationTargetToSupport_opensRange :
    (schemeNormalizationTargetToSupport X Z).left.opensRange = schemeNormalizationGoodOpen X Z :=
  Scheme.Opens.opensRange_ι _

theorem schemeNormalizationCoverSource_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (schemeNormalizationCoverSource X Z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z).hom := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (((CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)).left ⁻¹ᵁ schemeNormalizationGoodOpen X Z).ι ≫
      (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom)) = _
  rw [Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open]
  exact (CycleClass.Thom.Normalization.Field.Constructions.finiteNormalization_dimension (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom)).trans
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq X Z).symm

theorem schemeNormalizationGenericCover_degree :
    (schemeNormalizationGenericCover X Z).left.residueDegree
      (genericPoint (schemeNormalizationCoverSource X Z).left) = 1 :=
  CycleClass.Thom.Normalization.GenericCover.Constructions.coverMap_residueDegree (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)

theorem schemeNormalizationGenericCover_fiber (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (schemeNormalizationCoverTarget X Z)) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (schemeNormalizationCoverSource X Z) |
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeNormalizationGenericCover X Z) y = x} = 1 :=
  CycleClass.Thom.Normalization.GenericCover.Constructions.coverMap_complexFiber_card (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) x

variable [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem schemeNormalizationGoodTargetToAmbient_range (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ schemeNormalizationGoodAmbient X Z) :
    ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeNormalizationGoodTargetToAmbient X Z))) =
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U (hU.trans (schemeNormalizationGoodAmbient_regular X Z))) := by
  have hU' : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X
      (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z (schemeNormalizationTargetToSupport X Z).left.opensRange).compl := by
    rw [schemeNormalizationTargetToSupport_opensRange]
    exact hU
  exact LineBundles.Scheme.SupportDenseOpenImage.BundleCycles.schemeSupportOpenImmersion_regularImage X Z (schemeNormalizationTargetToSupport X Z) U hU'
    (hU.trans (schemeNormalizationGoodAmbient_regular X Z))

end

section

/-! The constructed generic normalization cover lies in the actual
smooth normalization used for divisor computations, with the same ambient map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open

theorem normalizationGoodOpen_subset_smoothBase (S : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral S.left] [LocallyOfFiniteType S.hom] :
    CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen S ≤ CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase S.left S.hom := by
  let : IsFinite (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S.left) := CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap_isFinite S.left S.hom
  let : LocallyOfFiniteType (CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOver S).hom := by
    change LocallyOfFiniteType (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S.left ≫ S.hom)
    infer_instance
  let : Smooth (((CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap S).left ⁻¹ᵁ CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen S).ι ≫ (CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOver S).hom) :=
    (CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen_spec S).2.2.2.2
  have hs := CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus (CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOver S).hom ((CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap S).left ⁻¹ᵁ CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen S)
  intro x hx
  rintro ⟨y, hy, hyx⟩
  have hyy : y ∈ (CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap S).left ⁻¹ᵁ CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen S := by
    change CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S.left y ∈ CycleClass.Thom.Normalization.GenericCover.Constructions.goodOpen S
    exact hyx.symm ▸ hx
  exact hy (hs hyy)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

local instance normalizationGoodSmoothSupportIntegral : IsIntegral (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z).left :=
  inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))
local instance normalizationGoodSmoothSupportFiniteType : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z).hom :=
  inferInstanceAs (LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom))

theorem schemeNormalizationGoodSource_le_smooth :
    ((CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)).left ⁻¹ᵁ schemeNormalizationGoodOpen X Z) ≤
      (AmbientMap.BundleCycles.schemeNormalizationToAmbient X Z).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X Z := by
  rw [AmbientMap.BundleCycles.schemeNormalization_preimage_ambientOpen]
  exact fun _ hx => normalizationGoodOpen_subset_smoothBase (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) hx

def schemeNormalizationSourceToSmooth : schemeNormalizationCoverSource X Z ⟶ AmbientMap.BundleCycles.schemeSmoothNormalizationOver X Z :=
  Over.homMk ((CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE (schemeNormalizationGoodSource_le_smooth X Z)) (by
    change (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE (schemeNormalizationGoodSource_le_smooth X Z) ≫
      (((AmbientMap.BundleCycles.schemeNormalizationToAmbient X Z).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X Z).ι ≫
        (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom)) =
      ((CycleClass.Thom.Normalization.GenericCover.Constructions.normalizationOverMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z)).left ⁻¹ᵁ schemeNormalizationGoodOpen X Z).ι ≫
        (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom)
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom))
        ((CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE_ι (schemeNormalizationGoodSource_le_smooth X Z))))

instance schemeNormalizationSourceToSmooth_open : IsOpenImmersion (schemeNormalizationSourceToSmooth X Z).left := by
  have ho (T : Scheme) (U V : T.Opens) (hUV : U ≤ V) : IsOpenImmersion (T.homOfLE hUV) := inferInstance
  exact ho (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) _ _ (schemeNormalizationGoodSource_le_smooth X Z)

theorem schemeNormalizationSourceToSmooth_ambient :
    schemeNormalizationSourceToSmooth X Z ≫ LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z =
      schemeNormalizationGenericCover X Z ≫ schemeNormalizationGoodTargetToAmbient X Z := by
  apply Over.OverMorphism.ext
  change (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE (schemeNormalizationGoodSource_le_smooth X Z) ≫
    (LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z).left = _
  rw [LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap_left]
  change (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE (schemeNormalizationGoodSource_le_smooth X Z) ≫
      (((AmbientMap.BundleCycles.schemeNormalizationToAmbient X Z).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X Z).ι ≫
        (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z)) =
    (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ∣_ schemeNormalizationGoodOpen X Z) ≫
      ((schemeNormalizationGoodOpen X Z).ι ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z)
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z))
      ((CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE_ι (schemeNormalizationGoodSource_le_smooth X Z)))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z)
        (morphismRestrict_ι (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) (schemeNormalizationGoodOpen X Z)).symm).trans
        (Category.assoc _ _ _)))

end

/-! The generic cover contains precisely the smooth-normalization
points above the actual retained ambient open. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

theorem schemeNormalizationFullAmbientMap_apply (y : (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X Z).left) :
    (LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z).left y = CycleClass.Geometric.GenericPoint.reducedSupportι Z (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) y.val) := by
  rw [LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap_left]
  rfl

theorem schemeNormalizationSourceToSmooth_mem_range (y : (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X Z).left) :
    y ∈ Set.range (schemeNormalizationSourceToSmooth X Z).left ↔
      CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) y.val ∈ schemeNormalizationGoodOpen X Z := by
  constructor
  · rintro ⟨x, rfl⟩
    have he := (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE_apply (schemeNormalizationGoodSource_le_smooth X Z) x
    change CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)
      (((CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE (schemeNormalizationGoodSource_le_smooth X Z)) x).val ∈
        schemeNormalizationGoodOpen X Z
    exact (congrArg (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) he).symm ▸ x.property
  · intro hy
    let x : (schemeNormalizationCoverSource X Z).left := ⟨y.val, hy⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)).homOfLE_apply (schemeNormalizationGoodSource_le_smooth X Z) x

theorem schemeNormalizationSourceToSmooth_range :
    Set.range (schemeNormalizationSourceToSmooth X Z).left =
      (LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z).left ⁻¹' (schemeNormalizationOmittedBoundary X Z : Set X.left)ᶜ := by
  ext y
  rw [schemeNormalizationSourceToSmooth_mem_range]
  change _ ↔ ¬ (LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z).left y ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z (schemeNormalizationGoodOpen X Z)
  rw [schemeNormalizationFullAmbientMap_apply]
  have he := Set.ext_iff.mp (LineBundles.Scheme.SupportDenseOpenImage.BundleCycles.schemeSupportOpenBoundary_preimage X Z (schemeNormalizationGoodOpen X Z))
    (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) y.val)
  exact ((not_congr he).trans not_not).symm

theorem schemeNormalizationSourceToSmooth_analytic_range :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeNormalizationSourceToSmooth X Z)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X Z) ⁻¹'
        (schemeNormalizationGoodAmbient X Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion, schemeNormalizationSourceToSmooth_range]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Good.BundleCycles
