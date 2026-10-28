import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RegularNormalStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit

/-! # Regular Normal Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RegularNormalComparison.Constructions.Construction

noncomputable section

/-! The global source–Thom comparison agrees with the independently constructed normal-chart supported Gysin isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
variable (hP : P.ambientChart.MDifferentiable
  𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))

include hP in
theorem regularNormalSourceThomStageIso_eq_native
    (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso Z a ha x P K q).hom =
      ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K q).toLinearMap := by
  let hf := Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  let B := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P hf K
  let r := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
    (A := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen Z x P))ᶜ)
    (fun _ hx => hx) q
  let f := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
    (A := (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹' HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K)
    (B := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (fun _ hx => hx) q
  let s := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen Z x P)) S q) (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement_source P hf K))
  let o := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of P.neighborhood) S ((2 * p)+q)) (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P hf K))
  let g := ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) B.isOpen (2 * p) q P.rationalClassFin)
  have hc := LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso_cup Z a ha P.openNeighborhood B q
  have hn := CupStalk.Constructions.Construction.regularThomCocycle_normalPair Z a ha x P hP
  rw [EvenCupShiftSections.Constructions.relativeEvenCocycleOpenRestriction_class, ha] at hn
  rw [hn] at hc
  have hstage : (RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso Z a ha x P K q).hom = r ≫ g ≫ o.hom :=
    HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions.splitSourceIso_cup r f s (LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood B q) o g
      (HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions.normalPairRelativeRetraction_split_raw P hf K q) hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso Z a ha x P K q).hom b =
    HodgeConjecture.DegreeTwo.SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q b
  rw [hstage]
  exact (HodgeConjecture.DegreeTwo.NormalRetractionCup.Constructions.normalPairSourceSupportedCohomologyIso_eq_retraction_cup P hf K q b).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RegularNormalComparison.Constructions.Construction
