import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Topology
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison

/-! # Normalized Function -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction.BundleCycles

noncomputable section

/-! Actual rational functions and their canonical principal boundaries
on the constructed smooth normalization open of a general support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedPrincipalDivisor.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (W : IrreducibleCloseds X.left)

def schemeNormalizedOpen : (SchemeNormalization.AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left.Opens :=
  (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizedOpen X W

local instance : IsIntegral ((U) : Scheme) := SchemeNormalization.Topology.BundleCycles.schemeSmoothNormalization_integral X W
local instance : Nonempty U := inferInstanceAs (Nonempty ((U) : Scheme))

def schemeNormalizedFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.functionField :=
  CycleClass.Thom.RationalOrderTransport.Constructions.openFunctionFieldMap (U).ι ((CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)).hom g)

theorem schemeNormalizedFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    schemeNormalizedFunction X W g ≠ 0 := by
  unfold schemeNormalizedFunction
  apply (map_ne_zero_iff _ (CycleClass.Thom.RationalOrderTransport.Constructions.openFunctionFieldMap (U).ι).hom.injective).mpr
  exact (map_ne_zero_iff _ (CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)).hom.hom.injective).mpr hg

def schemeNormalizedUnitRepresentative [AlgebraicGeometry.IsNoetherian X.left]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (schemeNormalizedFunction X W g) :=
  CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.rationalUnitRepresentative _ _ (schemeNormalizedFunction_ne_zero X W g hg)

def schemeNormalizationFullAmbientMap : SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W ⟶ X :=
  SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W ≫ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)

theorem schemeNormalizationFullAmbientMap_left : (schemeNormalizationFullAmbientMap X W).left =
    (U).ι ≫ (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W) :=
  morphismRestrict_ι (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)

theorem schemeNormalizationOpen_divisorPoint (y : (SchemeNormalization.AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left)
    (hy : Order.coheight y = 1) : y ∈ U := by
  change y ∈ (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W
  rw [SchemeNormalization.AmbientMap.BundleCycles.schemeNormalization_preimage_ambientOpen]
  exact CycleClass.Thom.SmoothNormalizationDivisor.Constructions.normalizedSmoothOpen_divisorPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom) y hy

theorem schemeNormalizedPrincipal_absolute_zero [AlgebraicGeometry.IsNoetherian X.left] [IsSeparated X.hom]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    let D := schemeNormalizedUnitRepresentative X W g hg
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)))
      (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W) D.domain) 2
      (CycleClass.Thom.Scheme.SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W) D.domain (schemeNormalizedFunction X W g)) = 0 :=
  CycleClass.Thom.Scheme.PrincipalDivisorComparison.Constructions.principalDivisorSupportedClass_absolute_zero
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W) (schemeNormalizedUnitRepresentative X W g hg)
    (schemeNormalizedFunction_ne_zero X W g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction.BundleCycles
