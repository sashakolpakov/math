import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.AmbientMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology

/-! # Topology -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Topology.BundleCycles

noncomputable section

/-! The constructed smooth normalization source is integral and
Noetherian, preserves the support dimension, and is metrizable for a
separated ambient complex scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (W : IrreducibleCloseds X.left)

instance schemeFullNormalization_integral : IsIntegral (AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left :=
  inferInstanceAs (IsIntegral (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)))

instance schemeSmoothNormalization_integral : IsIntegral (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left := by
  change IsIntegral (((AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W) : Scheme)
  rw [AmbientMap.BundleCycles.schemeNormalization_preimage_ambientOpen]
  exact inferInstanceAs (IsIntegral ((CycleClass.Thom.SmoothNormalizationDivisor.Constructions.normalizedSmoothOpen (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)) : Scheme))

instance schemeFullNormalization_noetherian [AlgebraicGeometry.IsNoetherian X.left] :
    AlgebraicGeometry.IsNoetherian (AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left :=
  CycleClass.Thom.Normalization.Field.Constructions.finiteNormalization_noetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)

instance schemeSmoothNormalization_noetherian [AlgebraicGeometry.IsNoetherian X.left] :
    AlgebraicGeometry.IsNoetherian (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left := by
  let U := (AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W
  exact @Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian U.toScheme (AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left
    (schemeFullNormalization_noetherian X W) U.ι inferInstance

instance schemeSmoothNormalization_separated [IsSeparated X.hom] :
    IsSeparated (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom := by
  let n := CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
  let g := CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom
  let U := (AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W
  let : IsFinite n := CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap_isFinite (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)
  have hg : IsSeparated g := IsSeparated.stableUnderComposition.comp_mem (CycleClass.Geometric.GenericPoint.reducedSupportι W) X.hom
    inferInstance inferInstance
  have hng : IsSeparated (n ≫ g) := IsSeparated.stableUnderComposition.comp_mem n g inferInstance hg
  exact IsSeparated.stableUnderComposition.comp_mem U.ι (n ≫ g) inferInstance hng

instance schemeSmoothNormalization_quasiCompact [AlgebraicGeometry.IsNoetherian X.left] :
    QuasiCompact (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom := inferInstance

instance schemeSmoothNormalization_metrizable [AlgebraicGeometry.IsNoetherian X.left] [IsSeparated X.hom] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)) :=
  CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)

theorem schemeSmoothNormalization_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom := by
  let U := (AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W
  let : IsIntegral (U : Scheme) := schemeSmoothNormalization_integral X W
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion U.ι
    (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)
  exact h.trans (CycleClass.Thom.Normalization.Field.Constructions.finiteNormalization_dimension (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Topology.BundleCycles
