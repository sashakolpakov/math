import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module

/-! # Supported Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedNormalRestriction

noncomputable section

/-! The actual prime-divisor class restricts to its canonical regular Thom
class on every normal neighborhood, with arbitrary enlargement of support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

variable (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (RegularSupport.Constructions.regularModel X (SchemeDivisor.Purity.Constructions.primeSupport X z)) (Fin 1 → ℂ) (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x)

def regularPairAmbientMap : TopCat.of P.neighborhood ⟶ T :=
  TopCat.ofHom ⟨fun y => y.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

omit [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem regularPairAmbientMap_mapsTo (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement) :
    Set.MapsTo (regularPairAmbientMap X z x P) A (Set.range (RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro y hy
  have h := hA hy
  change y.val ∉ Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) at h
  rw [RegularSupport.Constructions.regularComplementInclusion_range] at h
  exact h

theorem supportedDivisorClass_normalRestriction (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularPairAmbientMap X z x P)
      (regularPairAmbientMap_mapsTo X z x P A hA) 2 (SchemeDivisor.Module.Constructions.supportedDivisorClass X z) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P.neighborhood)) hA 2
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of G)
        (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ P.openNeighborhood 2 (SchemeDivisor.Module.Constructions.regularDivisorThomClass X z)) := by
  let Q := ModuleCat.of ℚ ℚ
  let k := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)
  have hk : Set.MapsTo k P.relativeComplement (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ := fun _ hy => hy
  have hkA : Set.MapsTo k A (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ := fun _ hy => hA hy
  have hj : Set.MapsTo j (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ
      (Set.range (RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
    intro y hy
    rw [RegularSupport.Constructions.regularComplementInclusion_range] at hy
    exact hy
  have hr : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hkA 2 =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of G) (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ
        P.openNeighborhood 2 ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2 :=
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q (𝟙 (TopCat.of P.neighborhood)) k hA hk 2).symm
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (regularPairAmbientMap X z x P)
      (regularPairAmbientMap_mapsTo X z x P A hA) 2 =
      SchemeDivisor.Module.Constructions.divisorSupportRestriction X z ≫
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of G) (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ
          P.openNeighborhood 2 ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2 :=
    (Geometric.RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp Q k j hkA hj 2).trans
      (congrArg (fun a => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 ≫ a) hr)
  have hv := ConcreteCategory.congr_hom hc (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)
  change _ = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of G) (Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ
      P.openNeighborhood 2 (SchemeDivisor.Module.Constructions.divisorSupportRestriction X z (SchemeDivisor.Module.Constructions.supportedDivisorClass X z))) at hv
  rw [SchemeDivisor.Module.Constructions.supportedDivisorClass_restrict] at hv
  exact hv

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedNormalRestriction
