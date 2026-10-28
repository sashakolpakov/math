import OAI.AlgebraicGeometry.CycleClass.Thom.ComposedRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity

/-! # Composed -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Composed.Constructions.ThomClass

noncomputable section

/-! Supported Thom pushforward takes the inner canonical Thom class
to the canonical Thom class of the actual composite closed complex
immersion. This holds for arbitrary nested closed complex immersions. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.Support
  Open.RestrictionNormalPair.Constructions ThomOpenRestriction.Constructions ComposedSupport.Constructions ComposedRestriction.Constructions
  Immersion.SheafPurity.Constructions.SupportDetection NestedNormalNeighborhood.Constructions ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem composedThomGysinIso_innerThom {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ}
    (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass) :
    (ComposedSupport.Constructions.composedThomGysinIso Z C a ha).hom C.regularThomClass = (Open.ClosedImmersionComposition.Constructions.compose Z C).regularThomClass := by
  let D := Open.ClosedImmersionComposition.Constructions.compose Z C
  apply Immersion.SheafPurity.Constructions.SupportDetection.relativeClass_eq_of_neighborhoods D (fun z => (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood)
    (fun z => (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).point_mem_neighborhood)
  intro z
  let U := (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
  let e := eqToIso (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of U) A (2 * (p + q))) (Closed.ImmersionOpenRestriction.Constructions.Support.restricted_complement D U))
  apply e.toLinearEquiv.injective
  have hmap (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range D.regularComplementInclusion)ᶜ (2 * (p + q))) :
      e.hom (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (Set.range D.regularComplementInclusion)ᶜ U (2 * (p + q)) b) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
        (Open.RestrictionNormalPair.Constructions.restriction_mapsTo D U) (2 * (p + q)) b :=
    ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
      (Closed.ImmersionOpenRestriction.Constructions.Support.restricted_complement D U) (fun _ hx => hx) (Open.RestrictionNormalPair.Constructions.restriction_mapsTo D U) (2 * (p + q)) b
  change e.hom (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range D.regularComplementInclusion)ᶜ U (2 * (p + q))
      ((ComposedSupport.Constructions.composedThomGysinIso Z C a ha).hom C.regularThomClass)) =
    e.hom (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range D.regularComplementInclusion)ᶜ U (2 * (p + q)) D.regularThomClass)
  rw [hmap, hmap]
  exact (ComposedRestriction.Constructions.composedThomGysinIso_innerThom_restriction Z C z a ha).trans
    (ThomOpenRestriction.Constructions.regularThomClass_open_restriction D U).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Composed.Constructions.ThomClass
