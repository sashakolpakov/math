import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit

/-! # Regular Normal Thom Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison.Constructions

noncomputable section

/-! The global source–Thom comparison agrees with the independently constructed normal-chart supported Gysin isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
variable (hP : P.ambientChart.MDifferentiable
  𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))

include hP in
theorem regularNormalSourceThomStageIso_eq_native
    (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso Z a ha x P K q).hom =
      ModuleCat.ofHom (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K q).toLinearMap := by
  let hf := Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  let B := NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P hf K
  let r := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
    (A := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (B := (K : Set (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P))ᶜ)
    (fun _ hx => hx) q
  let f := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
    (A := (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹' NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K)
    (B := NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (fun _ hx => hx) q
  let s := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) S q) (NormalSupportRelative.Constructions.normalPairRetractionComplement_source P hf K))
  let o := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of P.neighborhood) S (2+q)) (NormalSupportRelative.Constructions.normalPairRetraction_union_complement P hf K))
  let g := ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement
    (NormalSupportRelative.Constructions.normalPairRetractionComplement P hf K) (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) B.isOpen 2 q P.rationalClassFin)
  have hc := LocalSupportCup.Constructions.regularSourceThomLocalSupportIso_cup Z a ha P.openNeighborhood B q
  have hn := RegularThomCupStalk.Constructions.regularThomCocycle_normalPair Z a ha x P hP
  rw [RelativeCupShiftSections.Constructions.relativeTwoCocycleOpenRestriction_class, ha] at hn
  rw [hn] at hc
  have hstage : (RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso Z a ha x P K q).hom = r ≫ g ≫ o.hom :=
    NormalRetractionSplit.Constructions.splitSourceIso_cup r f s (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood B q) o g
      (NormalRetractionSplit.Constructions.normalPairRelativeRetraction_split_raw P hf K q) hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso Z a ha x P K q).hom b =
    SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q b
  rw [hstage]
  exact (NormalRetractionCup.Constructions.normalPairSourceSupportedCohomologyIso_eq_retraction_cup P hf K q b).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison.Constructions
