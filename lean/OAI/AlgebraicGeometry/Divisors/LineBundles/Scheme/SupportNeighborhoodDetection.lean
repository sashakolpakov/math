import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Support Neighborhood Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection.BundleCycles

noncomputable section

/-! Supported classes in the cycle degree are determined on arbitrary
ambient neighborhoods of all regular support points. The passage across
the singular boundary uses the proved support-purity isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.SupportDetection

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "S" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
local notation "J" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ

def schemeSupportRegularNeighborhood (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : Opens G :=
  ⟨Subtype.val ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)), U.isOpen.preimage continuous_subtype_val⟩

def schemeSupportRegularNeighborhoodMap (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :
    TopCat.of (schemeSupportRegularNeighborhood X Z U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨y.val.val, y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportRegularNeighborhood_mapsTo (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :
    Set.MapsTo (schemeSupportRegularNeighborhoodMap X Z U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of G) J (schemeSupportRegularNeighborhood X Z U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) S U) := by
  intro y hy
  exact CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T S G J (SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z) hy

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportNeighborhood_square (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (p : ℕ) :
    SupportedCycleClass.BundleCycles.schemeCycleSupportRestriction X Z p ≫
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of G) J
        (schemeSupportRegularNeighborhood X Z U) (2 * p) =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T S U (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeSupportRegularNeighborhoodMap X Z U)
        (schemeSupportRegularNeighborhood_mapsTo X Z U) (2 * p) := by
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)
  let k := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) (schemeSupportRegularNeighborhood X Z U : Set G)
  let l := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (U : Set T)
  have hj : Set.MapsTo j J S := CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T S G J (SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)
  have hk : Set.MapsTo k
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of G) J (schemeSupportRegularNeighborhood X Z U)) J := fun _ hy => hy
  have hl : Set.MapsTo l (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) S U) S := fun _ hy => hy
  have he : k ≫ j = schemeSupportRegularNeighborhoodMap X Z U ≫ l := by
    ext y
    rfl
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k j hk hj (2 * p)
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (schemeSupportRegularNeighborhoodMap X Z U) l
    (schemeSupportRegularNeighborhood_mapsTo X Z U) hl (2 * p)
  have hm := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr he (hj.comp hk)
    (hl.comp (schemeSupportRegularNeighborhood_mapsTo X Z U)) (2 * p)
  exact h₁.trans (hm.trans h₂.symm)

theorem schemeSupportedClass_eq_of_regular_neighborhoods (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (U : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z) → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hU : ∀ x, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x ∈ U x)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T S (2 * p))
    (hab : ∀ x, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T S (U x) (2 * p) a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T S (U x) (2 * p) b) : a = b := by
  let := SupportedCycleClass.BundleCycles.schemeCycleSupportRestriction_isIso X Z p hp
  apply (asIso (SupportedCycleClass.BundleCycles.schemeCycleSupportRestriction X Z p)).toLinearEquiv.injective
  apply CycleClass.Thom.Immersion.SheafPurity.Constructions.SupportDetection.relativeClass_eq_of_neighborhoods (SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp)
    (fun x => schemeSupportRegularNeighborhood X Z (U x)) (fun x => hU x)
  intro x
  have ha := ConcreteCategory.congr_hom (schemeSupportNeighborhood_square X Z (U x) p) a
  have hb := ConcreteCategory.congr_hom (schemeSupportNeighborhood_square X Z (U x) p) b
  exact ha.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (schemeSupportRegularNeighborhoodMap X Z (U x)) (schemeSupportRegularNeighborhood_mapsTo X Z (U x))
    (2 * p)) (hab x)).trans hb.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection.BundleCycles
