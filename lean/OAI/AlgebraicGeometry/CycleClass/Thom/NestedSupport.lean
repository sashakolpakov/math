import OAI.AlgebraicGeometry.CycleClass.Thom.NestedLocalComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.ComposedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionNormalPair

/-! # Nested Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupport.Constructions

noncomputable section

/-! The constructed nested normal equations have the same actual
source and target supports as the original globally supported Gysin map. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  Closed.ImmersionOpenRestriction.Constructions Closed.ImmersionOpenRestriction.Constructions.Support Open.RestrictionNormalPair.Constructions
  ComposedSupport.Constructions NestedNormalNeighborhood.Constructions NestedNormalEquation.Constructions
  NestedLocalComposition.Constructions Immersion.Retraction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)

theorem nestedSourceComplement :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Z.regularAnalyticSpace)
      (((Opens.map (Immersion.SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj (ComposedSupport.Constructions.composedComplement Z C)) : Set Z.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) =
    (NestedLocalComposition.Constructions.nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)) := by
  ext y
  change y.val ∈ Z.regularComplementInclusion ⁻¹' (ComposedSupport.Constructions.composedComplement Z C : Set V.analyticSpace) ↔
    NestedLocalComposition.Constructions.nestedParameter Z C z y ≠ 0
  rw [ComposedSupport.Constructions.composedSourceComplement]
  exact not_congr (NestedNormalEquation.Constructions.parameter_zero_iff Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
    (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z) y).symm

theorem nestedTargetComplement :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
      ((Z.regularThomComplementOpen ⊔ ComposedSupport.Constructions.composedComplement Z C : Opens V.analyticSpace) : Set V.analyticSpace)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood =
    (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).relativeComplement ∪
      (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) ⁻¹'
        (NestedLocalComposition.Constructions.nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)) := by
  rw [ComposedSupport.Constructions.composedTargetComplement, Closed.ImmersionOpenRestriction.Constructions.Support.restricted_complement]
  exact (NestedLocalComposition.Constructions.localComposition_support Z C z).symm

theorem nestedCylinder_le_composedComplement :
    HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := V.analyticSpace) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
      (Immersion.Retraction.Constructions.retractionOpen Z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
        (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)
        (NestedLocalComposition.Constructions.nestedEquationOpen Z C z)) ≤ ComposedSupport.Constructions.composedComplement Z C := by
  intro y hy
  change y ∈ Subtype.val '' (Immersion.Retraction.Constructions.retractionOpen Z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
    (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)
      (NestedLocalComposition.Constructions.nestedEquationOpen Z C z) : Set (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) at hy
  obtain ⟨w, hw, rfl⟩ := hy
  have hc : w ∈ (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).relativeComplement ∪
      (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) ⁻¹'
        (NestedLocalComposition.Constructions.nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)) :=
    Or.inr hw
  rw [NestedLocalComposition.Constructions.localComposition_support] at hc
  exact Open.RestrictionNormalPair.Constructions.restriction_mapsTo (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood hc

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupport.Constructions
