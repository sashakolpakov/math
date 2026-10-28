import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget

/-! # Module -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module

noncomputable section

/-! Canonical supported prime-divisor Thom classes on general smooth integral
complex schemes. Extension across the actual singular boundary is proved
invertible by stratified purity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

private def modulePreimage {A C : ModuleCat ℚ} (f : A ⟶ C) [IsIso f] (a : C) : A :=
  (asIso f).toLinearEquiv.symm a

private theorem moduleIso_apply_symm {A C : ModuleCat ℚ} (f : A ⟶ C) [IsIso f] (a : C) :
    f (modulePreimage f a) = a :=
  (asIso f).toLinearEquiv.apply_symm_apply a

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "B" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
private theorem primeRegularCodimension : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (Scheme.RegularSupport.Constructions.regularModel X Z) E = 1 := by
  change Module.finrank ℂ E - Module.finrank ℂ (Scheme.RegularSupport.Constructions.regularModel X Z) = 1
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  have h := Purity.Constructions.primeRegularDimension_add_one X z
  omega

local instance : MetrizableSpace G := MetrizableSpace.subtype _

/-- The normalized class of the actual closed complex regular-locus immersion. -/
def regularDivisorThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ 2 :=
  Degree.Constructions.ThomClass.complexThomClassInDegree j (Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    1 (primeRegularCodimension X z)

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem regularDivisorThomClass_restrict (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X Z))
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Scheme.RegularSupport.Constructions.regularModel X Z) (Fin 1 → ℂ) j x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, Scheme.RegularSupport.Constructions.regularModel X Z × (Fin 1 → ℂ))) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ
      P.openNeighborhood 2 (regularDivisorThomClass X z) = P.rationalClassFin :=
  Degree.Constructions.ThomClass.complexThomClassInDegree_restrict j (Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    1 (primeRegularCodimension X z) x P hP

omit [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
/-- The regular-locus complement is the genuine restricted ambient support complement. -/
theorem regularDivisorComplement_eq : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) B G = (Set.range j)ᶜ := by
  rw [Scheme.RegularSupport.Constructions.regularComplementInclusion_range]
  rfl

/-- Restriction is the pair pullback along the actual open inclusion. -/
def divisorSupportRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B 2 ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
    (Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (regularDivisorComplement_eq X z)) 2

instance divisorSupportRestriction_isIso : IsIso (divisorSupportRestriction X z) := by
  let := Purity.Constructions.primeRegularRestriction_isIso X z
  change IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
    (Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (regularDivisorComplement_eq X z)) 2)
  rw [← Open.RestrictionTarget.Constructions.openRestriction_change_target T B G (Set.range j)ᶜ (regularDivisorComplement_eq X z) 2]
  infer_instance

/-- Extend the actual regular-locus Thom class uniquely across its singular boundary. -/
def supportedDivisorClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B 2 :=
  modulePreimage (divisorSupportRestriction X z) (regularDivisorThomClass X z)

theorem supportedDivisorClass_restrict :
    divisorSupportRestriction X z (supportedDivisorClass X z) = regularDivisorThomClass X z :=
  moduleIso_apply_symm (divisorSupportRestriction X z) (regularDivisorThomClass X z)

theorem supportedDivisorClass_unique (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B 2)
    (ha : divisorSupportRestriction X z a = regularDivisorThomClass X z) :
    a = supportedDivisorClass X z := by
  apply (ModuleCat.mono_iff_injective (divisorSupportRestriction X z)).mp inferInstance
  exact ha.trans (supportedDivisorClass_restrict X z).symm

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module
