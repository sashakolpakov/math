import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedNormalRestriction

/-! # Rational Regular Normal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalRegularNormal

noncomputable section

/-! The actual rational boundary equals its integer order times the canonical
supported prime-divisor class on genuine regular normal neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions
  RationalBoundary.Constructions.LocalMultiplicity RationalBoundary.Constructions.Restriction
  RegularSupport.Constructions SchemeDivisor.Purity.Constructions SchemeDivisor.Module.Constructions SupportedNormalRestriction.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

def cycleWithUnitComplement
    (hO : (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) ⊆ (Set.range (RegularSupport.Constructions.supportInclusion X Z))ᶜ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T) hO 2 (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)

variable (U : X.left.Opens) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z)) (Fin 1 → ℂ) (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x)
  (hPU : ∀ y ∈ P.neighborhood, y.val ∈ SectionEvaluation.Constructions.analyticOpen X U)

def regularPairSectionMap : TopCat.of P.neighborhood ⟶ TopCat.of (SectionEvaluation.Constructions.analyticOpen X U) :=
  TopCat.ofHom ⟨fun y => ⟨y.val.val, hPU y.val y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

local notation "A" => (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x P) ⁻¹' (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set T)

theorem rationalGlobalBoundary_regularNormal [Nonempty U]
    (hO : (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) ⊆ (Set.range (RegularSupport.Constructions.supportInclusion X Z))ᶜ)
    (p : Γ(X.left, U)) (hp : p ≠ 0) (v : Γ(X.left, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g = X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)
    (hmd : P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z) × (Fin 1 → ℂ)))
    (hcoord : ∀ y : P.neighborhood, P.normalCoordinate y 0 =
      SectionEvaluation.Constructions.sectionEvaluationOn X U p (regularPairSectionMap X z U x P hPU y)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x P)
      («A» := A) (fun _ hy => hy) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
    m • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x P)
      («A» := A) (fun _ hy => hy) 2 (cycleWithUnitComplement X z D hO) := by
  let Q := ModuleCat.of ℚ ℚ
  let j := regularPairSectionMap X z U x P hPU
  let k := SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x P
  let F := RationalBoundary.Constructions.LocalMultiplicity.lineMap (Y := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (SectionEvaluation.Constructions.sectionEvaluationOn X U p)
  have hj : Set.MapsTo j A (RationalUnitEvaluation.Constructions.referenceLocus X D U) := fun _ hy => hy
  have hk : Set.MapsTo k A (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) := fun _ hy => hy
  have hA : A ⊆ P.relativeComplement := by
    intro y hy
    change y.val ∉ Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))
    rw [RegularSupport.Constructions.regularComplementInclusion_range]
    exact hO hy
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm
  have hF : Set.MapsTo F (RationalUnitEvaluation.Constructions.referenceLocus X D U) PrincipalBoundary.Constructions.puncturedComplexLine := RationalBoundary.Constructions.LocalMultiplicity.parameterMap_mapsTo X D U p hp'
  have hmap : j ≫ F = P.normalCoordinate := by
    ext y i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (hcoord y).symm
  have hC : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 (RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary X D U) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j (RationalBoundary.Constructions.Restriction.localAmbientMap X U) hj (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2
    have hv := (ConcreteCategory.congr_hom hc (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)).symm
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (RationalBoundary.Constructions.Restriction.localAmbientMap X U) (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2
          (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)) at hv
    rw [RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_localRestriction] at hv
    exact hv
  have hparam : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 (RationalBoundary.Constructions.LocalMultiplicity.parameterSupportedClass X D U p hp') =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        (P.normalCohomologyMap Q 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j F hj hF 2
    simp only [hmap] at hc
    have hn := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q (𝟙 (TopCat.of P.neighborhood))
      P.normalCoordinate hA P.normalCoordinate_mapsTo 2
    simp only [Category.id_comp] at hn
    exact ConcreteCategory.congr_hom (hc.trans hn.symm) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  have hS : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (cycleWithUnitComplement X z D hO) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        (P.normalCohomologyMap Q 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q k (𝟙 T) hk hO 2
    have hv := ConcreteCategory.congr_hom hc (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)
    have hs := SupportedNormalRestriction.Constructions.supportedDivisorClass_normalRestriction X z x P A hA
    rw [SchemeDivisor.Module.Constructions.regularDivisorThomClass_restrict X z x P hmd, P.rationalClassFin_eq_normalPullback] at hs
    exact hv.trans hs
  apply hC.trans
  rw [RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary_power X D U p hp v m hm he, map_zsmul, hparam]
  exact congrArg (fun a => m • a) hS.symm

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalRegularNormal
