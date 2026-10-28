import OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RetractionComparison

/-! # Composed Local Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComposedLocalIso.Constructions

noncomputable section

/-! On the constructed normal neighborhoods, the original global
supported Thom construction has the coefficient-one local composition
law already proved through the actual normal retraction. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  Closed.ImmersionOpenRestriction.Constructions ComposedSupport.Constructions NestedNormalNeighborhood.Constructions
  NestedLocalComposition.Constructions NestedSupport.Constructions Normal.Retraction.Constructions
  Immersion.Retraction.Constructions Immersion.RetractionComparison.Constructions NestedNormalSource.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)

theorem nestedTargetEquality :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
      ((Z.regularThomComplementOpen ⊔ ComposedSupport.Constructions.composedComplement Z C : Opens V.analyticSpace) : Set V.analyticSpace)
      (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood =
    (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularComplementInclusion)ᶜ :=
  (NestedSupport.Constructions.nestedTargetComplement Z C z).trans (NestedLocalComposition.Constructions.localComposition_support Z C z)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def originalLocalGysinIso :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding))
      (NestedLocalComposition.Constructions.nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)) (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
      (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularComplementInclusion)ᶜ
      (2 * (p + q)) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding))
    (NestedSupport.Constructions.nestedSourceComplement Z C z) (2 * q)).symm ≪≫
    Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha (ComposedSupport.Constructions.composedComplement Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood (2 * q) ≪≫
    eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        ((Z.regularThomComplementOpen ⊔ ComposedSupport.Constructions.composedComplement Z C : Opens V.analyticSpace) : Set V.analyticSpace)
        (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood) n) (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
      (nestedTargetEquality Z C z) (2 * (p + q))

theorem originalLocalGysinIso_eq_retraction :
    originalLocalGysinIso Z C z a ha =
    Normal.Retraction.Constructions.normalRetractionThomIso Z a ha (C.regularComplementInclusion z) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z)
      (NestedLocalComposition.Constructions.nestedEquationOpen Z C z) (2 * q) ≪≫
      eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
        ((NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).relativeComplement ∪
          (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding) ⁻¹'
            (NestedLocalComposition.Constructions.nestedEquationOpen Z C z : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding))) n)
        (Nat.mul_add 2 p q).symm) ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).neighborhood)
        (NestedLocalComposition.Constructions.localComposition_support Z C z) (2 * (p + q)) := by
  have hr := Immersion.RetractionComparison.Constructions.retractionThomIso_eq_original Z a ha (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood
    (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)
    (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding)
    (NestedLocalComposition.Constructions.nestedEquationOpen Z C z) (ComposedSupport.Constructions.composedComplement Z C)
    (NestedSupport.Constructions.nestedCylinder_le_composedComplement Z C z) (NestedSupport.Constructions.nestedSourceComplement Z C z) (NestedSupport.Constructions.nestedTargetComplement Z C z) (2 * q)
  unfold Normal.Retraction.Constructions.normalRetractionThomIso
  rw [hr]
  apply Iso.ext
  simp only [originalLocalGysinIso, Iso.trans_hom, Iso.symm_hom, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans]

theorem originalLocalGysinIso_innerThom :
    (originalLocalGysinIso Z C z a ha).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
          (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
        (NestedNormalSource.Constructions.Class.parameterSource_mapsTo Z C z (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z) (C.regularFixedNormalPair z)
          (NestedNormalNeighborhood.Constructions.nestedOuterPair_source_subset Z C z)) (2 * q) C.regularThomClass) =
    (Closed.ImmersionOpenRestriction.Constructions.restrict (Open.ClosedImmersionComposition.Constructions.compose Z C) (NestedNormalNeighborhood.Constructions.nestedOuterPair Z C z).openNeighborhood).regularThomClass := by
  rw [originalLocalGysinIso_eq_retraction]
  exact NestedLocalComposition.Constructions.localThom_composition Z C z a ha

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComposedLocalIso.Constructions
