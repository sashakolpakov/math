import OAI.AlgebraicGeometry.CycleClass.Thom.ComposedLocalIso
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.MapDegreeSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality

/-! # Composed Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComposedRestriction.Constructions

noncomputable section

/-! The original global supported Gysin map restricts to the
coefficient-one local composition map on each constructed normal
neighborhood, with all source, target, and degree transports explicit. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  Closed.ImmersionOpenRestriction.Constructions Open.RestrictionNormalPair.Constructions ComposedSupport.Constructions
  ComposedLocalIso.Constructions NestedNormalNeighborhood.Constructions NestedLocalComposition.Constructions
  NestedSupport.Constructions NestedNormalSource.Constructions.Class Relative.MapDegreeSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem composedThomGysinIso_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
      (NestedNormalSource.Constructions.Class.parameterSource_mapsTo Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
        (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)) (2 * q) ≫
      (ComposedLocalIso.Constructions.originalLocalGysinIso Z C z a ha).hom =
    (ComposedSupport.Constructions.composedThomGysinIso Z C a ha).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace ((NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood : Set V.analyticSpace))
        (Open.RestrictionNormalPair.Constructions.restriction_mapsTo (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) (2 * (p + q)) := by
  let U := (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
  let W := ComposedSupport.Constructions.composedComplement Z C
  let s₁ := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr Z.regularAnalyticSpace (ComposedSupport.Constructions.composedSourceComplement Z C) (2 * q)
  let s₂ := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding))
    (NestedSupport.Constructions.nestedSourceComplement Z C z) (2 * q)
  let t₁ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (ComposedSupport.Constructions.composedTargetComplement Z C) (2 * (p + q))
  let t₂ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) U) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U) (ComposedLocalIso.Constructions.nestedTargetEquality Z C z) (2 * (p + q))
  have hs := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality
    (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
    (NestedSupport.Constructions.nestedSourceComplement Z C z) (ComposedSupport.Constructions.composedSourceComplement Z C) (fun _ hx => hx)
    (NestedNormalSource.Constructions.Class.parameterSource_mapsTo Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)) (2 * q)
  have ht := Relative.MapDegreeSupport.Constructions.relativePairMap_degreeSupport
    (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
    (ComposedLocalIso.Constructions.nestedTargetEquality Z C z) (ComposedSupport.Constructions.composedTargetComplement Z C) (fun _ hx => hx)
    (Open.RestrictionNormalPair.Constructions.restriction_mapsTo (Open.ClosedImmersionComposition.Constructions.compose Z C) U) (Nat.mul_add 2 p q).symm
  have hn := Immersion.GlobalSourceOpenNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_open_naturality Z a ha W U (2 * q)
  have h := Immersion.SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality s₁ s₂
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q))
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha W U (2 * q)) t₁ t₂ _ _ _ _ hs hn ht
  simpa only [s₁, s₂, t₁, t₂, U, W, ComposedSupport.Constructions.composedThomGysinIso, ComposedLocalIso.Constructions.originalLocalGysinIso,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, Iso.trans_hom, Iso.symm_hom, Category.assoc] using h

theorem composedThomGysinIso_innerThom_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace ((NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood : Set V.analyticSpace))
      (Open.RestrictionNormalPair.Constructions.restriction_mapsTo (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) (2 * (p + q))
      ((ComposedSupport.Constructions.composedThomGysinIso Z C a ha).hom C.regularThomClass) =
    (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularThomClass := by
  have h := ConcreteCategory.congr_hom (composedThomGysinIso_restriction Z C z a ha) C.regularThomClass
  change (ComposedLocalIso.Constructions.originalLocalGysinIso Z C z a ha).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
          (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
        (NestedNormalSource.Constructions.Class.parameterSource_mapsTo Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
          (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)) (2 * q) C.regularThomClass) = _ at h
  exact h.symm.trans (ComposedLocalIso.Constructions.originalLocalGysinIso_innerThom Z C z a ha)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComposedRestriction.Constructions
