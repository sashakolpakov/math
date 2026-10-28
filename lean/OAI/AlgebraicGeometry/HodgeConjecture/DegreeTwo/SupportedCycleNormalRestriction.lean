import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorRegular
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Supported Cycle Normal Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions

noncomputable section

/-!
# DegreeTwo: restrict the actual extended supported cycle class

The class extended through the singular boundary restricts in every actual
regular normal neighborhood to the global regular Thom class. Enlarging
support commutes with this restriction by actual pair-map composition.
-/

open _root_.CategoryTheory

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
    Z.regularComplementInclusion x)

/-- The actual map from the regular normal neighborhood to the whole
ambient variety, through both open inclusions. -/
def regularPairAmbientMap : TopCat.of P.neighborhood ⟶ TopCat.of V.analyticSpace :=
  CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) P.neighborhood ≫
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ

theorem regularPairAmbientMap_mapsTo (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement) :
    Set.MapsTo (regularPairAmbientMap Z x P) A (Set.range Z.analyticInclusion)ᶜ :=
  fun y hy => (Z.mem_regularThomComplement_iff y.val).mp (hA hy)

/-- Actual restriction of the canonical supported extension, including
enlargement to any chosen local support containing this divisor. -/
theorem rationalSupportedCycleClass_normalRestriction
    (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularPairAmbientMap Z x P)
        (regularPairAmbientMap_mapsTo Z x P A hA) 2 Z.rationalSupportedCycleClass =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P.neighborhood)) hA 2
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
          P.openNeighborhood 2 Z.regularThomClass) := by
  let Q := ModuleCat.of ℚ ℚ
  let k := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) P.neighborhood
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ
  have hk : Set.MapsTo k P.relativeComplement (Set.range Z.regularComplementInclusion)ᶜ :=
    fun _ hy => hy
  have hkA : Set.MapsTo k A (Set.range Z.regularComplementInclusion)ᶜ :=
    fun _ hy => hA hy
  have hj : Set.MapsTo j (Set.range Z.regularComplementInclusion)ᶜ
      (Set.range Z.analyticInclusion)ᶜ :=
    fun y hy => (Z.mem_regularThomComplement_iff y).mp hy
  have hr : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hkA 2 =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood 2 ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2 :=
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q (𝟙 (TopCat.of P.neighborhood)) k hA hk 2).symm
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (regularPairAmbientMap Z x P)
      (regularPairAmbientMap_mapsTo Z x P A hA) 2 =
      Z.regularThomCohomologyRestriction Q 2 ≫
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood 2 ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2 :=
    (CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp Q k j hkA hj 2).trans
      (congrArg (fun a => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 ≫ a) hr)
  have hv := ConcreteCategory.congr_hom hc Z.rationalSupportedCycleClass
  change _ = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood 2
      (Z.regularThomCohomologyRestriction Q 2 Z.rationalSupportedCycleClass)) at hv
  rw [Z.rationalSupportedCycleClass_regularPullback] at hv
  exact hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions
