import OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalSource

/-! # Nested Local Composition -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedLocalComposition.Constructions

noncomputable section

/-! For arbitrary nested closed complex immersions, the original
local supported Thom map carries the inner canonical Thom class to
the canonical Thom class of the actual composite on a constructed
normal neighborhood of every source point. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions
  NestedNormalNeighborhood.Constructions NestedNormalEquation.Constructions NestedNormalSource.Constructions.Class
  Normal.Retraction.Constructions Normal.RetractionComparison.Constructions Immersion.IntersectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)

abbrev nestedParameter := NestedNormalEquation.Constructions.parameter Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
  (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)

abbrev nestedEquationOpen := Normal.RetractionComparison.Constructions.sourceEquationOpen Z (C.regularComplementInclusion z)
  (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (nestedParameter Z C z)

theorem localComposition_support :
    (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).relativeComplement ∪
      (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) ⁻¹'
        (nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)) =
    (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularComplementInclusion)ᶜ :=
  Normal.RetractionComparison.Constructions.thomSupport_eq Z (C.regularComplementInclusion z) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z)
    (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) (nestedParameter Z C z)
    (NestedNormalEquation.Constructions.composite_restriction_range Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z))

theorem localThom_composition
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass) :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood) A (2 * (p + q))) (localComposition_support Z C z))
      (eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
        ((NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).relativeComplement ∪
          (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) ⁻¹'
            (nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding))) n)
        (Nat.mul_add 2 p q).symm)
        ((Normal.Retraction.Constructions.normalRetractionThomIso Z a ha (C.regularComplementInclusion z) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z)
          (nestedEquationOpen Z C z) (2 * q)).hom
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
            (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
              (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
            (NestedNormalSource.Constructions.Class.parameterSource_mapsTo Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
              (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)) (2 * q) C.regularThomClass))) =
      (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularThomClass := by
  rw [NestedNormalSource.Constructions.Class.sourceThomClass_eq_parameter Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
    (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z) (C.regularFixedNormalPair_ambientChart_mdifferentiable z)]
  exact Normal.RetractionComparison.Constructions.normalRetractionThomIso_eq_Thom Z (C.regularComplementInclusion z) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z)
    (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) (nestedParameter Z C z)
    (NestedNormalEquation.Constructions.composite_restriction_range Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z))
    (NestedNormalNeighborhood.Constructions.nestedOuterPair_mdifferentiable Z C z) (NestedNormalNeighborhood.Constructions.nestedOuterPair_analytic Z C z) (NestedNormalNeighborhood.Constructions.nestedOuterPair_symm_analytic Z C z)
    (NestedNormalEquation.Constructions.parameter_analytic Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z) (Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff C z))
    (fun y _ => NestedNormalEquation.Constructions.parameter_submersion Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z) (C.regularFixedNormalPair_ambientChart_mdifferentiable z)
      (Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff C z) y) a ha

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedLocalComposition.Constructions
