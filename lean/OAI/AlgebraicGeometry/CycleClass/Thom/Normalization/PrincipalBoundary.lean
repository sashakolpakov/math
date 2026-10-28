import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalNormalization

/-! # Principal Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary

noncomputable section

/-! The actual pulled-back rational function on the constructed smooth
normalization has zero absolute divisor Thom class and recovers the exact
ThomClass principal-divisor coefficients under the original scheme map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
  Fields.Constructions Field.Constructions SmoothNormalizationDivisor.Constructions RationalOrderTransport.Constructions
  Thom.Scheme.SectionEvaluation.Constructions Thom.Scheme.SupportedPrincipalDivisor.Constructions
  Point.Constructions Open.Principal.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : IsIntegral (AmbientMap.Constructions.fullNormalizationOver V W).left :=
  inferInstanceAs (IsIntegral (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)))

local instance : AlgebraicGeometry.IsNoetherian (AmbientMap.Constructions.fullNormalizationOver V W).left :=
  Field.Constructions.finiteNormalization_noetherian (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V W)) :=
  AmbientTopology.Constructions.smoothNormalization_metrizable V W

local instance : IsIntegral (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme) :=
  AmbientTopology.Constructions.smoothNormalization_integral V W

local instance : Nonempty ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) :=
  inferInstanceAs (Nonempty (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme))

/-- Pull back through the actual normalization field isomorphism and open inclusion. -/
def normalizedFunction (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (AmbientMap.Constructions.smoothNormalizationOver V W).left.functionField :=
  RationalOrderTransport.Constructions.openFunctionFieldMap ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι
    ((Fields.Constructions.normalizationFieldIso (Geometric.GenericPoint.reducedSupportScheme W)).hom g)

theorem normalizedFunction_ne_zero (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    normalizedFunction V W g ≠ 0 := by
  unfold normalizedFunction
  apply (map_ne_zero_iff _ (RationalOrderTransport.Constructions.openFunctionFieldMap
    ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι).hom.injective).mpr
  exact (map_ne_zero_iff _ (Fields.Constructions.normalizationFieldIso (Geometric.GenericPoint.reducedSupportScheme W)).hom.hom.injective).mpr hg

def normalizedUnitRepresentative (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative (AmbientMap.Constructions.smoothNormalizationOver V W).left (normalizedFunction V W g) :=
  RationalFunctionBoundary.Constructions.Principal.rationalUnitRepresentative _ _ (normalizedFunction_ne_zero V W g hg)

/-- Vanishing of the canonical divisor Thom class on the actual smooth normalization open. -/
theorem normalizedPrincipal_absolute_zero (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    let D := normalizedUnitRepresentative V W g hg
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V W)))
      (Thom.Scheme.SectionEvaluation.Constructions.analyticOpen (AmbientMap.Constructions.smoothNormalizationOver V W) D.domain) 2
      (Thom.Scheme.SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass (AmbientMap.Constructions.smoothNormalizationOver V W) D.domain (normalizedFunction V W g)) = 0 :=
  Thom.Scheme.PrincipalDivisorComparison.Constructions.principalDivisorSupportedClass_absolute_zero
    (AmbientMap.Constructions.smoothNormalizationOver V W) (normalizedUnitRepresentative V W g hg) (normalizedFunction_ne_zero V W g hg)

/-- The finite normalization map over the complement, followed by its actual ambient inclusion. -/
def fullAmbientMap : AmbientMap.Constructions.smoothNormalizationOver V W ⟶ V.toOver :=
  AmbientMap.Constructions.smoothNormalizationToAmbient V W ≫ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver (AmbientMap.Constructions.ambientOpen V W)

theorem fullAmbientMap_left : (fullAmbientMap V W).left =
    ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι ≫
      (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W) :=
  morphismRestrict_ι (AmbientMap.Constructions.normalizationToAmbient V W).left (AmbientMap.Constructions.ambientOpen V W)

/-- Every divisor point is retained in precisely this ambiently restricted normalization. -/
theorem normalizationOpen_divisorPoint (y : (AmbientMap.Constructions.fullNormalizationOver V W).left)
    (hy : Order.coheight y = 1) : y ∈ (AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W := by
  rw [AmbientMap.Constructions.preimage_ambientOpen]
  exact SmoothNormalizationDivisor.Constructions.normalizedSmoothOpen_divisorPoint (Geometric.GenericPoint.reducedSupportScheme W) (Geometric.SupportFiniteType.supportStructureMap W V.structureMap) y hy

/-- All poles and branches are included, with the actual residue-field degrees. -/
theorem normalizedPrincipal_coefficient (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (C : IrreducibleCloseds V.carrier) :
    Point.Constructions.pointPushforward (fullAmbientMap V W).left
      (Point.Constructions.rationalPrincipalPointDivisor (AmbientMap.Constructions.smoothNormalizationOver V W).left (normalizedFunction V W g))
      (IntersectionGeometry.supportPoint C) = IntersectionGeometry.principalDivisorCoefficient V.presentation W g C := by
  have ho := Open.Principal.Constructions.principalDivisor_open_pushforward (AmbientMap.Constructions.fullNormalizationOver V W).left
    ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) (normalizationOpen_divisorPoint V W)
    ((Fields.Constructions.normalizationFieldIso (Geometric.GenericPoint.reducedSupportScheme W)).hom g)
  rw [fullAmbientMap_left, Point.Constructions.pointPushforward_comp, LinearMap.comp_apply]
  change Point.Constructions.pointPushforward (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W)
    (Point.Constructions.pointPushforward ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι
      (Point.Constructions.rationalPrincipalPointDivisor (AmbientMap.Constructions.smoothNormalizationOver V W).left (normalizedFunction V W g)))
    (IntersectionGeometry.supportPoint C) = _
  have ht := congrArg (fun a : (AmbientMap.Constructions.fullNormalizationOver V W).left →₀ ℚ =>
    Point.Constructions.pointPushforward (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W) a
      (IntersectionGeometry.supportPoint C)) ho
  exact ht.trans (PrincipalNormalization.Constructions.principalDivisorCoefficient_eq_normalizationPushforward
    V.presentation W g hg C)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary
