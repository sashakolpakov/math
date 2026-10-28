import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Open Regular Map -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions.Restriction

/-! On every analytic neighborhood, actual supported cycle-degree classes are determined after removing the support's singular boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace)

local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

theorem cycleOpen_regularRestriction_isIso :
    IsIso (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) (2 * p)) := by
  have hc (Z : IrreducibleCloseds V.carrier)
      (hZ : (Z : Set V.carrier) ⊆ Geometric.StratumDimension.supportSingularBoundary D.val V.structureMap) :
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + (p + 1) ≤
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
    have h := D.codimension_lt_of_subset_singularBoundary Z hZ
    have hdim := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
    omega
  exact Scheme.OpenSupportRemoval.Constructions.open_relativeRestriction_isIso V.toOver
    ⟨Geometric.StratumDimension.supportSingularBoundary D.val V.structureMap, Geometric.StratumDimension.isClosed_supportSingularBoundary D.val V.structureMap⟩
    (p + 1) hc U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)
    (fun _ hx => D.analyticSupportComplement_subset_regularAmbient hx) (2 * p) (by omega)

theorem cycleOpen_regularRestriction_injective :
    Function.Injective (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) (2 * p)) := by
  let := cycleOpen_regularRestriction_isIso D U
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions.Restriction

namespace AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions

/-! The actual pullback from an analytic open to its regular support neighborhood is injective in cycle degree and takes the original cycle class to its regular Thom class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem triple_pairMap {X Y : TopCat.{0}} (A B : Set X) (f : Y ⟶ TopCat.of A)
    (C : Set Y) (hf : Set.MapsTo f C (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace X A B)) (n : ℕ) :
    Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) X A B n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n =
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (f ≫ Geometric.LocalHomology.Cycles.subspaceInclusion X A)
          (fun _ hx => hf hx) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) f (Geometric.LocalHomology.Cycles.subspaceInclusion X A) hf (fun _ hx => hx) n

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Opens V.analyticSpace)

def regularSwapHomeomorph :
    RegularNeighborhoodDetection.Constructions.regularNeighborhood D U ≃ₜ ({x : U | x.val ∈ D.analyticSingularBoundary}ᶜ : Set U) where
  toFun z := ⟨⟨z.val.val, z.property⟩, z.val.property⟩
  invFun z := ⟨⟨z.val.val, z.property⟩, z.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem regularSwap_complement (x : RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) :
    x ∈ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) ↔
    regularSwapHomeomorph D U x ∈ Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U)
      {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) :=
  D.mem_regularThomComplement_iff x.val

def regularSwapMap : TopCat.of (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) ⟶
    TopCat.of ({x : U | x.val ∈ D.analyticSingularBoundary}ᶜ : Set U) :=
  TopCat.ofHom ⟨regularSwapHomeomorph D U, (regularSwapHomeomorph D U).continuous⟩

theorem regularSwap_mapsTo : Set.MapsTo (regularSwapMap D U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))
    (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)) :=
  fun x hx => (regularSwap_complement D U x).mp hx

def regularSwapCohomologyIso (n : ℕ) :=
  AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))
    (Y := TopCat.of ({x : U | x.val ∈ D.analyticSingularBoundary}ᶜ : Set U))
    (regularSwapHomeomorph D U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))
    (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U))
    (regularSwap_complement D U) n

theorem regularSwapCohomologyIso_hom (n : ℕ) :
    (regularSwapCohomologyIso D U n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularSwapMap D U) (regularSwap_mapsTo D U) n := rfl

def regularOpenPullback (n : ℕ) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (RegularNeighborhoodDetection.Constructions.regularNeighborhoodMap D U)
    (RegularNeighborhoodDetection.Constructions.regularNeighborhood_mapsTo D U) n

theorem regularSwap_map_factor :
    regularSwapMap D U ≫
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of U) {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ =
        RegularNeighborhoodDetection.Constructions.regularNeighborhoodMap D U := rfl

theorem regularOpenPullback_factor (n : ℕ) :
    Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ D.analyticSingularBoundary}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) n ≫
        (regularSwapCohomologyIso D U n).hom = regularOpenPullback D U n := by
  rw [regularSwapCohomologyIso_hom]
  have h := triple_pairMap (X := TopCat.of U) (Y := TopCat.of (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))
    ({x : U | x.val ∈ D.analyticSingularBoundary}ᶜ : Set U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)
    (regularSwapMap D U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))
    (regularSwap_mapsTo D U) n
  exact h.trans (ThomOpenRestriction.Constructions.pairMap_congr (regularSwap_map_factor D U)
    (fun _ hx => regularSwap_mapsTo D U hx) (RegularNeighborhoodDetection.Constructions.regularNeighborhood_mapsTo D U) n)

theorem regularOpenPullback_injective : Function.Injective (regularOpenPullback D U (2 * p)) := by
  let := Restriction.cycleOpen_regularRestriction_isIso D U
  have : IsIso (regularOpenPullback D U (2 * p)) := by
    rw [← regularOpenPullback_factor]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem regularOpenPullback_cycleClass :
    regularOpenPullback D U (2 * p)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) (2 * p) D.regularThomClass := by
  have h := ConcreteCategory.congr_hom (RegularNeighborhoodDetection.Constructions.neighborhood_square D U) D.rationalSupportedCycleClass
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (Set.range D.regularComplementInclusion)ᶜ (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) (2 * p)
      (D.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) D.rationalSupportedCycleClass) = _ at h
  rw [D.rationalSupportedCycleClass_regularPullback] at h
  exact h.symm

end AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions

end

end OAI
