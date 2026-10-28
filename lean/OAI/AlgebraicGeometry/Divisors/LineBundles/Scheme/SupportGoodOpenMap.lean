import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenPurity
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction

/-! # Support Good Open Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenMap.BundleCycles

noncomputable section

/-! On every analytic ambient open, actual cycle-degree supported classes are detected by the actual inclusion of its intersection with a dense algebraic support open's retained ambient complement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

def schemeSupportGoodNeighborhood : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := U ⊓ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W).compl

def schemeSupportGoodNeighborhoodMap : TopCat.of (schemeSupportGoodNeighborhood X Z W U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportGoodNeighborhood_mapsTo : Set.MapsTo (schemeSupportGoodNeighborhoodMap X Z W U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (schemeSupportGoodNeighborhood X Z W U))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U) := fun _ hx => hx

def schemeSupportGoodSwapHomeomorph : schemeSupportGoodNeighborhood X Z W U ≃ₜ
    ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ : Set U) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def schemeSupportGoodSwapMap : TopCat.of (schemeSupportGoodNeighborhood X Z W U) ⟶
    TopCat.of ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ : Set U) :=
  TopCat.ofHom ⟨schemeSupportGoodSwapHomeomorph X Z W U, (schemeSupportGoodSwapHomeomorph X Z W U).continuous⟩

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportGoodSwap_mapsTo : Set.MapsTo (schemeSupportGoodSwapMap X Z W U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (schemeSupportGoodNeighborhood X Z W U))
    (CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U)) := fun _ hx => hx

def schemeSupportGoodSwapCohomologyIso (n : ℕ) := AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
  (X := TopCat.of (schemeSupportGoodNeighborhood X Z W U))
  (Y := TopCat.of ({x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ : Set U))
  (schemeSupportGoodSwapHomeomorph X Z W U)
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (schemeSupportGoodNeighborhood X Z W U))
  (CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U)) (fun _ => Iff.rfl) n

def schemeSupportGoodOpenPullback (n : ℕ) := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
  (schemeSupportGoodNeighborhoodMap X Z W U) (schemeSupportGoodNeighborhood_mapsTo X Z W U) n

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportGoodOpenPullback_factor (n : ℕ) :
    CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U) n ≫
      (schemeSupportGoodSwapCohomologyIso X Z W U n).hom = schemeSupportGoodOpenPullback X Z W U n := by
  have hh : (schemeSupportGoodSwapCohomologyIso X Z W U n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeSupportGoodSwapMap X Z W U) (schemeSupportGoodSwap_mapsTo X Z W U) n := rfl
  rw [hh]
  exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (schemeSupportGoodSwapMap X Z W U) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ)
    (schemeSupportGoodSwap_mapsTo X Z W U) (fun _ hx => hx) n
theorem schemeSupportGoodOpenPullback_injective (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) (hW : genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ∈ W) : Function.Injective (schemeSupportGoodOpenPullback X Z W U (2 * p)) := by
  let := SupportGoodOpenPurity.BundleCycles.schemeSupport_goodRestriction_isIso X Z W U p hp hW
  have : IsIso (schemeSupportGoodOpenPullback X Z W U (2 * p)) := by
    rw [← schemeSupportGoodOpenPullback_factor]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportGoodOpenPullback_restriction (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U n ≫ schemeSupportGoodOpenPullback X Z W U n =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (schemeSupportGoodNeighborhood X Z W U) n := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (schemeSupportGoodNeighborhoodMap X Z W U)
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (schemeSupportGoodNeighborhood_mapsTo X Z W U) (fun _ hx => hx) n
  exact h.trans (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (show schemeSupportGoodNeighborhoodMap X Z W U ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (schemeSupportGoodNeighborhood X Z W U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) from rfl)
    (fun _ hx => schemeSupportGoodNeighborhood_mapsTo X Z W U hx) (fun _ hx => hx) n)

theorem schemeSupportGoodOpenPullback_cycleClass (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    schemeSupportGoodOpenPullback X Z W U (2 * p)
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (schemeSupportGoodNeighborhood X Z W U) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) :=
  ConcreteCategory.congr_hom (schemeSupportGoodOpenPullback_restriction X Z W U (2 * p)) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenMap.BundleCycles
