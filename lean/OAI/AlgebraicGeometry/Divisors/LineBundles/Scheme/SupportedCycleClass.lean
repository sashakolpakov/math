import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget

/-! # Supported Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass.BundleCycles

noncomputable section

/-! Canonical supported cycle classes in every codimension on genuine
smooth integral complex schemes. The regular-locus Thom class extends
uniquely across the actual singular boundary by proved purity. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "B" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ

include hp in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeRegularSupportCodimension : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) E = p := by
  change Module.finrank ℂ E - Module.finrank ℂ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) = p
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq]
  have h := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
  omega

local instance : MetrizableSpace G := MetrizableSpace.subtype _

def schemeRegularSupportThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ (2 * p) :=
  CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    p (schemeRegularSupportCodimension X Z p hp)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeRegularSupportComplement_eq : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) B G = (Set.range j)ᶜ := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_range]
  rfl

def schemeCycleSupportRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B (2 * p) ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
    (CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (schemeRegularSupportComplement_eq X Z)) (2 * p)

include hp in
theorem schemeCycleSupportRestriction_isIso : IsIso (schemeCycleSupportRestriction X Z p) := by
  let := SupportPurity.BundleCycles.schemeSupportRegularRestriction_isIso X Z p hp
  change IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
    (CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (schemeRegularSupportComplement_eq X Z)) (2 * p))
  rw [← CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestriction_change_target T B G (Set.range j)ᶜ (schemeRegularSupportComplement_eq X Z) (2 * p)]
  infer_instance

def schemeSupportedCycleClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B (2 * p) := by
  let := schemeCycleSupportRestriction_isIso X Z p hp
  exact (asIso (schemeCycleSupportRestriction X Z p)).toLinearEquiv.symm (schemeRegularSupportThomClass X Z p hp)

theorem schemeSupportedCycleClass_restrict :
    schemeCycleSupportRestriction X Z p (schemeSupportedCycleClass X Z p hp) = schemeRegularSupportThomClass X Z p hp := by
  let := schemeCycleSupportRestriction_isIso X Z p hp
  exact (asIso (schemeCycleSupportRestriction X Z p)).toLinearEquiv.apply_symm_apply _

theorem schemeSupportedCycleClass_unique (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B (2 * p))
    (ha : schemeCycleSupportRestriction X Z p a = schemeRegularSupportThomClass X Z p hp) :
    a = schemeSupportedCycleClass X Z p hp := by
  let := schemeCycleSupportRestriction_isIso X Z p hp
  apply (asIso (schemeCycleSupportRestriction X Z p)).toLinearEquiv.injective
  exact ha.trans (schemeSupportedCycleClass_restrict X Z p hp).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass.BundleCycles
