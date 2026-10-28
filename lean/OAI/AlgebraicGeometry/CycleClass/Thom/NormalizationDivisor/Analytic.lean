import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open
import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCoveringTrace

/-! # Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic

noncomputable section

/-! The constructed normalization divisor cover has the genuine analytic
topology, native dimensions, and exact algebraic covering multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Open.Constructions.Map Open.Constructions.Etale Open.Constructions.Regular
  SchemeDivisor.Purity.Constructions Scheme.RegularSupport.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)) :=
  Normalization.AmbientTopology.Constructions.smoothNormalization_metrizable V W
local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)
local instance : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := inferInstanceAs (T2Space V.analyticSpace)
local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) :=
  inferInstanceAs (SecondCountableTopology V.analyticSpace)
local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)) := by
  let : QuasiCompact (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)

variable (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

def sourceAmbientMap : Open.Constructions.Etale.sourceOpen V W z ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W :=
  Open.Constructions.Regular.sourceToRegular V W z ≫ Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)

instance sourceAmbientMap_immersion : IsImmersion (sourceAmbientMap V W z).left := by
  change IsImmersion ((Open.Constructions.Regular.sourceToRegular V W z).left ≫
    (Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)).left)
  infer_instance

def targetAmbientMap : Open.Constructions.Etale.targetOpen V W z ⟶ V.toOver :=
  Open.Constructions.Regular.targetToSupport V W z ≫ Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z)

instance targetAmbientMap_immersion : IsImmersion (targetAmbientMap V W z).left := by
  change IsImmersion ((Open.Constructions.Regular.targetToSupport V W z).left ≫
    (Scheme.RegularSupport.Constructions.supportToAmbient V.toOver (Image.Constructions.imageSupport V W z)).left)
  infer_instance

instance sourceOpen_t2 : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (sourceAmbientMap V W z)).t2Space

instance sourceOpen_secondCountable : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (sourceAmbientMap V W z)).secondCountableTopology

instance targetOpen_t2 : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.targetOpen V W z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (targetAmbientMap V W z)).t2Space

instance targetOpen_secondCountable : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.targetOpen V W z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (targetAmbientMap V W z)).secondCountableTopology

theorem sourceOpen_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension
        (Scheme.RegularSupport.Constructions.regularOver (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)).hom :=
  Scheme.SmoothSupportOpen.Constructions.supportOpen_dimension (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
    (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z) ((Open.Constructions.Map.finiteSupportMap V W z).left ⁻¹ᵁ Open.Constructions.Etale.goodOpen V W z)

theorem targetOpen_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.targetOpen V W z).hom =
      (Image.Constructions.imageCycleSupport V W z).regularComplexDimension := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (Open.Constructions.Regular.targetToSupport V W z).left (Open.Constructions.Map.targetSupport V W z).hom
  have hw : (Open.Constructions.Regular.targetToSupport V W z).left ≫ (Open.Constructions.Map.targetSupport V W z).hom = (Open.Constructions.Etale.targetOpen V W z).hom :=
    (Open.Constructions.Regular.targetToSupport V W z).w
  rw [hw] at h
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  exact h.trans (Image.Constructions.imageCycleSupport V W z).regularComplexDimension_eq_supportDimension.symm

theorem cover_dimensions_eq :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.targetOpen V W z).hom := by
  have h := Integral.MapDimension.Constructions.integral_dominant_dimension (Open.Constructions.Etale.coverMap V W z).left
    (Open.Constructions.Etale.coverMap_genericPoint V W z) (Open.Constructions.Etale.targetOpen V W z).hom
  have hw : (Open.Constructions.Etale.coverMap V W z).left ≫ (Open.Constructions.Etale.targetOpen V W z).hom = (Open.Constructions.Etale.sourceOpen V W z).hom := (Open.Constructions.Etale.coverMap V W z).w
  rw [hw, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension] at h
  exact h.symm

theorem cover_fiber_degree (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.targetOpen V W z)) :
    Nat.card (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) ⁻¹' {y}) =
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val :=
  (ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree (Open.Constructions.Etale.coverMap V W z) (Open.Constructions.Etale.coverMap_genericPoint V W z) y).trans
    (Open.Constructions.Etale.coverMap_residueDegree V W z)

theorem cover_localDiffeomorph :
    IsLocalDiffeomorph
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.targetOpen V W z).hom) → ℂ)
      ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z)) :=
  ProperImage.IntrinsicEtale.Constructions.Construction.isLocalDiffeomorph_nativeScheme_affineEtale (Open.Constructions.Etale.coverMap V W z)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic
