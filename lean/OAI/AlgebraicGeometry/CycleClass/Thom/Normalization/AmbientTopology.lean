import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor

/-! # Ambient Topology -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions

noncomputable section

/-! The constructed smooth normalization source is integral and metrizable,
with the dimension of the original support and compact inverse images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
  SmoothNormalizationDivisor.Constructions SeparatedSchemeTopology.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

instance smoothNormalization_integral : IsIntegral (AmbientMap.Constructions.smoothNormalizationOver V W).left := by
  change IsIntegral (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme)
  rw [AmbientMap.Constructions.preimage_ambientOpen]
  exact inferInstanceAs (IsIntegral ((SmoothNormalizationDivisor.Constructions.normalizedSmoothOpen (Geometric.GenericPoint.reducedSupportScheme W)
    (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)) : Scheme))

instance smoothNormalization_noetherian :
    AlgebraicGeometry.IsNoetherian (AmbientMap.Constructions.smoothNormalizationOver V W).left := by
  let : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)) :=
    Field.Constructions.finiteNormalization_noetherian (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  let : AlgebraicGeometry.IsNoetherian (AmbientMap.Constructions.fullNormalizationOver V W).left :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)))
  change AlgebraicGeometry.IsNoetherian
    (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme)
  exact Open.Principal.Constructions.openScheme_isNoetherian _ _

local instance fullNormalization_integral : IsIntegral (AmbientMap.Constructions.fullNormalizationOver V W).left :=
  inferInstanceAs (IsIntegral (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)))

theorem smoothNormalization_separated : IsSeparated (AmbientMap.Constructions.smoothNormalizationOver V W).hom := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)) :=
    Normalization.Scheme.Constructions.normalizationMap_isFinite (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  let : IsProper (Geometric.SupportFiniteType.supportStructureMap W V.structureMap) :=
    V.presentation.projective.reducedSupport_isProper W
  change IsSeparated (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι ≫
    (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.SupportFiniteType.supportStructureMap W V.structureMap))
  rw [AmbientMap.Constructions.preimage_ambientOpen]
  let n := Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)
  let g := Geometric.SupportFiniteType.supportStructureMap W V.structureMap
  let U := SmoothLocus.Constructions.Open.normalizationSmoothBase (Geometric.GenericPoint.reducedSupportScheme W) g
  let : IsSeparated n := inferInstance
  let : IsSeparated g := inferInstance
  let : IsSeparated (n ⁻¹ᵁ U).ι := inferInstance
  let : IsSeparated (n ≫ g) := inferInstance
  exact inferInstanceAs (IsSeparated ((n ⁻¹ᵁ U).ι ≫ (n ≫ g)))

theorem smoothNormalization_quasiCompact : QuasiCompact (AmbientMap.Constructions.smoothNormalizationOver V W).hom := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)) :=
    Normalization.Scheme.Constructions.normalizationMap_isFinite (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  let : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)) :=
    Field.Constructions.finiteNormalization_noetherian (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  let : IsProper (Geometric.SupportFiniteType.supportStructureMap W V.structureMap) :=
    V.presentation.projective.reducedSupport_isProper W
  change QuasiCompact (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι ≫
    (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.SupportFiniteType.supportStructureMap W V.structureMap))
  rw [AmbientMap.Constructions.preimage_ambientOpen]
  let n := Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)
  let g := Geometric.SupportFiniteType.supportStructureMap W V.structureMap
  let U := SmoothLocus.Constructions.Open.normalizationSmoothBase (Geometric.GenericPoint.reducedSupportScheme W) g
  let : QuasiCompact n := inferInstance
  let : QuasiCompact g := inferInstance
  let : QuasiCompact (n ⁻¹ᵁ U).ι := inferInstance
  let : QuasiCompact (n ≫ g) := inferInstance
  exact inferInstanceAs (QuasiCompact ((n ⁻¹ᵁ U).ι ≫ (n ≫ g)))

theorem smoothNormalization_metrizable :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V W)) := by
  let : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W
  let : IsSeparated (AmbientMap.Constructions.smoothNormalizationOver V W).hom := smoothNormalization_separated V W
  let : QuasiCompact (AmbientMap.Constructions.smoothNormalizationOver V W).hom := smoothNormalization_quasiCompact V W
  exact SeparatedSchemeTopology.Constructions.schemePoints_metrizable (AmbientMap.Constructions.smoothNormalizationOver V W)

theorem smoothNormalization_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (AmbientMap.Constructions.smoothNormalizationOver V W).hom =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W V.structureMap := by
  let U := (AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W
  let : IsIntegral (U : Scheme) := smoothNormalization_integral V W
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion U.ι
    (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  exact h.trans (Field.Constructions.finiteNormalization_dimension (Geometric.GenericPoint.reducedSupportScheme W)
    (Geometric.SupportFiniteType.supportStructureMap W V.structureMap))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions
