import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage

/-! # Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions

noncomputable section

/-! The constructed degree-one normalization cover of an actual cycle has its full support image and the original cycle dimension on the retained ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)

def targetToSupport : GenericCover.Constructions.targetOpen D.toOver ⟶ D.toOver := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion D.toOver (GenericCover.Constructions.goodOpen D.toOver)

instance targetToSupport_open : IsOpenImmersion (targetToSupport D).left :=
  inferInstanceAs (IsOpenImmersion (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion D.toOver (GenericCover.Constructions.goodOpen D.toOver)).left)

def targetToAmbient : GenericCover.Constructions.targetOpen D.toOver ⟶ V.toOver := targetToSupport D ≫ D.toAmbient

instance targetToAmbient_immersion : IsImmersion (targetToAmbient D).left := by
  let : IsClosedImmersion D.toAmbient.left := D.inclusion_isClosedImmersion
  change IsImmersion ((targetToSupport D).left ≫ D.toAmbient.left)
  infer_instance

def omittedBoundary : Closeds V.carrier := ProperImage.Open.Constructions.Construction.supportOpenBoundary D (GenericCover.Constructions.goodOpen D.toOver)

def goodAmbient : Opens V.analyticSpace := ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (omittedBoundary D)

theorem goodAmbient_regular : (goodAmbient D : Set V.analyticSpace) ⊆ D.regularAmbientOpen :=
  ProperImage.Open.Constructions.Construction.boundaryComplement_subset_regularAmbient D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_subset_smoothLocus D.toOver)

theorem targetToSupport_opensRange : (targetToSupport D).left.opensRange = GenericCover.Constructions.goodOpen D.toOver :=
  Scheme.Opens.opensRange_ι _

theorem sourceOpen_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (GenericCover.Constructions.sourceOpen D.toOver).hom = D.regularComplexDimension := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (((GenericCover.Constructions.normalizationOverMap D.toOver).left ⁻¹ᵁ GenericCover.Constructions.goodOpen D.toOver).ι ≫
      (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.structureMap)) = _
  rw [Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open, Field.Constructions.finiteNormalization_dimension]
  exact D.regularComplexDimension_eq_supportDimension.symm

theorem sourceGraph_codimension (d : ℕ) :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (GenericCover.Constructions.sourceOpen D.toOver).hom) → ℂ)
      (V.analyticModel × (Fin d → ℂ)) = p + d := by
  change Module.finrank ℂ (V.analyticModel × (Fin d → ℂ)) -
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (GenericCover.Constructions.sourceOpen D.toOver).hom) → ℂ) = p + d
  simp only [Module.finrank_prod, Module.finrank_fin_fun, sourceOpen_dimension]
  have hd := D.regularComplexDimension_add_codimension
  omega

theorem targetToAmbient_range (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ goodAmbient D) :
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (targetToAmbient D))) =
      Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion D U (hU.trans (goodAmbient_regular D))) := by
  have hU' : (U : Set V.analyticSpace) ⊆
      ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (ProperImage.Open.Constructions.Construction.supportOpenBoundary D (targetToSupport D).left.opensRange) := by
    rw [targetToSupport_opensRange]
    exact hU
  exact Cycle.DenseOpenImage.Constructions.supportOpenImmersion_regularImage D (targetToSupport D) U hU' (hU.trans (goodAmbient_regular D))

theorem omittedBoundary_codimension (Z : IrreducibleCloseds V.carrier)
    (hZ : (Z : Set V.carrier) ⊆ omittedBoundary D) : p < Geometric.DimensionCycles.dimensionCodimension V Z :=
  ProperImage.Open.Constructions.Construction.supportOpenBoundary_codimension D (GenericCover.Constructions.goodOpen D.toOver) (GenericCover.Constructions.goodOpen_spec D.toOver).1 Z hZ

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions
