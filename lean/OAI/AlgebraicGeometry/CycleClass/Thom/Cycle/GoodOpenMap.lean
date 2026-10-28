import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph

/-! # Good Open Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenMap.Constructions

noncomputable section

/-! On every analytic ambient open, actual cycle-degree supported classes are detected by the actual inclusion of its intersection with a dense algebraic support open's retained ambient complement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (W : D.scheme.Opens) (U : Opens V.analyticSpace)

def goodNeighborhood : Opens V.analyticSpace := U ⊓ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (ProperImage.Open.Constructions.Construction.supportOpenBoundary D W)

def goodNeighborhoodMap : TopCat.of (goodNeighborhood D W U) ⟶ TopCat.of U :=
  Open.SubsetHomeomorph.Constructions.smallerOpenMap U (goodNeighborhood D W U) inf_le_left

theorem goodNeighborhood_mapsTo : Set.MapsTo (goodNeighborhoodMap D W U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) := fun _ hx => hx

def goodSwapHomeomorph : goodNeighborhood D W U ≃ₜ
    ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ : Set U) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def goodSwapMap : TopCat.of (goodNeighborhood D W U) ⟶
    TopCat.of ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ : Set U) :=
  TopCat.ofHom ⟨goodSwapHomeomorph D W U, (goodSwapHomeomorph D W U).continuous⟩

theorem goodSwap_mapsTo : Set.MapsTo (goodSwapMap D W U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U))
    (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)) := fun _ hx => hx

def goodSwapCohomologyIso (n : ℕ) := AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
  (X := TopCat.of (goodNeighborhood D W U))
  (Y := TopCat.of ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ : Set U))
  (goodSwapHomeomorph D W U)
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U))
  (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)) (fun _ => Iff.rfl) n

def goodOpenPullback (n : ℕ) := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
  (goodNeighborhoodMap D W U) (goodNeighborhood_mapsTo D W U) n

theorem goodOpenPullback_factor (n : ℕ) :
    Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) n ≫
      (goodSwapCohomologyIso D W U n).hom = goodOpenPullback D W U n := by
  have hh : (goodSwapCohomologyIso D W U n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (goodSwapMap D W U) (goodSwap_mapsTo D W U) n := rfl
  rw [hh]
  exact OpenRegularMap.Constructions.triple_pairMap (X := TopCat.of U) (Y := TopCat.of (goodNeighborhood D W U))
    ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ : Set U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)
    (goodSwapMap D W U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U))
    (goodSwap_mapsTo D W U) n

theorem goodOpenPullback_injective (hW : genericPoint D.scheme ∈ W) : Function.Injective (goodOpenPullback D W U (2 * p)) := by
  let := GoodOpenRestriction.Constructions.cycleOpen_goodRestriction_isIso D W hW U
  have : IsIso (goodOpenPullback D W U (2 * p)) := by
    rw [← goodOpenPullback_factor]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem goodOpenPullback_restriction (n : ℕ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range D.analyticInclusion)ᶜ U n ≫ goodOpenPullback D W U n =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U) n := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (goodNeighborhoodMap D W U)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (goodNeighborhood_mapsTo D W U) (fun _ hx => hx) n
  exact h.trans (ThomOpenRestriction.Constructions.pairMap_congr
    (Open.SubsetHomeomorph.Constructions.smallerOpenMap_comp U (goodNeighborhood D W U) inf_le_left)
    (fun _ hx => goodNeighborhood_mapsTo D W U hx) (fun _ hx => hx) n)

theorem goodOpenPullback_cycleClass :
    goodOpenPullback D W U (2 * p)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ (goodNeighborhood D W U) (2 * p) D.rationalSupportedCycleClass :=
  ConcreteCategory.congr_hom (goodOpenPullback_restriction D W U (2 * p)) D.rationalSupportedCycleClass

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenMap.Constructions
