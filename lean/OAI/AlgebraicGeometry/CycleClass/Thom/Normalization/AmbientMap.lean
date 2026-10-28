import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper
import OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology

/-! # Ambient Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions

noncomputable section

/-! The normalization over the actual ambient complement is finite,
smooth over the complex base, and analytically proper. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientPurity.Constructions
  Integral.SchemeProper.Constructions SeparatedSchemeTopology.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

def fullNormalizationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.SupportFiniteType.supportStructureMap W V.structureMap)

def normalizationToAmbient : fullNormalizationOver V W ⟶ V.toOver :=
  Over.homMk (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W)
    (Category.assoc (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W))
      (Geometric.GenericPoint.reducedSupportι W) V.structureMap)

def ambientOpen : V.carrier.Opens := (AmbientPurity.Constructions.normalizationExceptionalClosed V W).compl

theorem preimage_ambientOpen :
    (normalizationToAmbient V W).left ⁻¹ᵁ ambientOpen V W =
      Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ⁻¹ᵁ
        SmoothLocus.Constructions.Open.normalizationSmoothBase (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap) := by
  ext y
  change (¬ Geometric.GenericPoint.reducedSupportι W (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) y) ∈
    Geometric.GenericPoint.reducedSupportι W '' (SmoothLocus.Constructions.Open.normalizationSingularImage (Geometric.GenericPoint.reducedSupportScheme W)
      (Geometric.SupportFiniteType.supportStructureMap W V.structureMap) : Set (Geometric.GenericPoint.reducedSupportScheme W))) ↔ _
  constructor
  · intro h hy
    exact h ⟨Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) y, hy, rfl⟩
  · rintro h ⟨x, hx, he⟩
    exact h ((Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective he ▸ hx)

def smoothNormalizationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (fullNormalizationOver V W)
    ((normalizationToAmbient V W).left ⁻¹ᵁ ambientOpen V W)

def smoothNormalizationToAmbient : smoothNormalizationOver V W ⟶ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (ambientOpen V W) :=
  ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (normalizationToAmbient V W) (ambientOpen V W)

theorem smoothNormalization_smooth : Smooth (smoothNormalizationOver V W).hom := by
  change Smooth (((normalizationToAmbient V W).left ⁻¹ᵁ ambientOpen V W).ι ≫
    (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.SupportFiniteType.supportStructureMap W V.structureMap))
  rw [preimage_ambientOpen]
  exact SmoothLocus.Constructions.Open.normalizationSmoothBase_preimage_smooth (Geometric.GenericPoint.reducedSupportScheme W)
    (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)

theorem smoothNormalization_finite : IsFinite (smoothNormalizationToAmbient V W).left := by
  let : IsFinite (Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)) :=
    Scheme.Constructions.normalizationMap_isFinite (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)
  change IsFinite ((Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W) ∣_ ambientOpen V W)
  infer_instance

theorem smoothNormalization_analytic_proper :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothNormalizationToAmbient V W)) := by
  let : IsFinite (smoothNormalizationToAmbient V W).left := smoothNormalization_finite V W
  let : LocallyOfFiniteType (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver (ambientOpen V W)).hom :=
    inferInstanceAs (LocallyOfFiniteType ((ambientOpen V W).ι ≫ V.structureMap))
  exact Integral.SchemeProper.Constructions.isProperMap_integral (smoothNormalizationToAmbient V W)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
