import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction

/-! # Regular Open Thom -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpenThom.BundleCycles

noncomputable section

/-! On every actual open in the regular ambient locus, the full
supported cycle class restricts to the canonical restricted Thom class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)

def schemeCycleRegularOpenToRegular : TopCat.of U ⟶ TopCat.of (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) :=
  CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U) (RegularOpen.BundleCycles.schemeCycleRegularOpenHomeomorph X Z U hU)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenToRegular_mapsTo : Set.MapsTo (schemeCycleRegularOpenToRegular X Z U hU)
    (Set.range (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU))ᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ :=
  CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U) (RegularOpen.BundleCycles.schemeCycleRegularOpenHomeomorph X Z U hU)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenToRegular_factor :
    schemeCycleRegularOpenToRegular X Z U hU ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := rfl

variable (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local instance e13SchemeCycleRegularOpenThom_local1 : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance e13SchemeCycleRegularOpenThom_local2 : MetrizableSpace (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) := MetrizableSpace.subtype _

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleRegularOpenThom_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeCycleRegularOpenToRegular X Z U hU)
      (schemeCycleRegularOpenToRegular_mapsTo X Z U hU) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp) =
    CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_analytic X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_differential_injective X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_closedEmbedding X Z U hU) p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp) :=
  CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U) (RegularOpen.BundleCycles.schemeCycleRegularOpenHomeomorph X Z U hU)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    ((RegularOpen.BundleCycles.schemeCycleRegularOpenHomeomorph_analytic X Z U hU).mdifferentiable (by simp))
    ((RegularOpen.BundleCycles.schemeCycleRegularOpenHomeomorph_symm_analytic X Z U hU).mdifferentiable (by simp))
    (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_analytic X Z U hU)
    (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_differential_injective X Z U hU)
    p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp) (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp)

theorem schemeSupportedCycleClass_regularOpen_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) =
    CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_analytic X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_differential_injective X Z U hU)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_closedEmbedding X Z U hU) p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp) := by
  let g := schemeCycleRegularOpenToRegular X Z U hU
  let A := (Set.range (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion X Z U hU))ᶜ
  have hg := schemeCycleRegularOpenToRegular_mapsTo X Z U hU
  have h := NormalRestriction.BundleCycles.schemeSupportedCycleClass_regularPairPullback X Z p hp g A hg
  have he := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr (schemeCycleRegularOpenToRegular_factor X Z U hU)
      ((CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
        (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ
        (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)).comp hg)
      (RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo X Z U hU) (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)
  exact he.symm.trans (h.trans (schemeCycleRegularOpenThom_pullback X Z U hU p hp))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpenThom.BundleCycles
