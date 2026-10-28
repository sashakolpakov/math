import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Boundary
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper

/-! # Ambient Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.AmbientMap.BundleCycles

noncomputable section

/-! The normalization of an integral closed support over its actual
ambient complement is finite, smooth, and analytically proper. The
ambient scheme need not be projective. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open
open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (W : IrreducibleCloseds X.left)

def schemeFullNormalizationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)

def schemeNormalizationToAmbient : schemeFullNormalizationOver X W ⟶ X :=
  Over.homMk (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)
    (Category.assoc (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (CycleClass.Geometric.GenericPoint.reducedSupportι W) X.hom)

def schemeNormalizationAmbientOpen : X.left.Opens := (Boundary.BundleCycles.schemeNormalizationExceptional X W).compl

theorem schemeNormalization_preimage_ambientOpen :
    (schemeNormalizationToAmbient X W).left ⁻¹ᵁ schemeNormalizationAmbientOpen X W =
      CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ⁻¹ᵁ
        CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom) := by
  ext y
  change (¬ CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) y) ∈
    CycleClass.Geometric.GenericPoint.reducedSupportι W '' (CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSingularImage (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
      (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom) : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) ↔ _
  constructor
  · intro h hy
    exact h ⟨CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) y, hy, rfl⟩
  · rintro h ⟨x, hx, he⟩
    exact h ((CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective he ▸ hx)

def schemeSmoothNormalizationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (schemeFullNormalizationOver X W)
    ((schemeNormalizationToAmbient X W).left ⁻¹ᵁ schemeNormalizationAmbientOpen X W)

def schemeSmoothNormalizationToAmbient : schemeSmoothNormalizationOver X W ⟶
    CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (schemeNormalizationAmbientOpen X W) :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (schemeNormalizationToAmbient X W) (schemeNormalizationAmbientOpen X W)

instance schemeSmoothNormalization_smooth : Smooth (schemeSmoothNormalizationOver X W).hom := by
  change Smooth (((schemeNormalizationToAmbient X W).left ⁻¹ᵁ schemeNormalizationAmbientOpen X W).ι ≫
    (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom))
  rw [schemeNormalization_preimage_ambientOpen]
  exact CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase_preimage_smooth (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)

instance schemeSmoothNormalization_finite : IsFinite (schemeSmoothNormalizationToAmbient X W).left := by
  let : IsFinite (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :=
    CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap_isFinite (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)
  change IsFinite ((CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W) ∣_ schemeNormalizationAmbientOpen X W)
  infer_instance

theorem schemeSmoothNormalization_analytic_proper :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeSmoothNormalizationToAmbient X W)) := by
  let : LocallyOfFiniteType (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (schemeNormalizationAmbientOpen X W)).hom :=
    inferInstanceAs (LocallyOfFiniteType ((schemeNormalizationAmbientOpen X W).ι ≫ X.hom))
  exact CycleClass.Thom.Integral.SchemeProper.Constructions.isProperMap_integral (schemeSmoothNormalizationToAmbient X W)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.AmbientMap.BundleCycles
