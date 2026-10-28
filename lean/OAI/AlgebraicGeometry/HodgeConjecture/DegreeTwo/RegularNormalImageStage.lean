import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality

/-! # Regular Normal Image Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalImageStage.Constructions

noncomputable section

/-! Replacing the normal retraction complement by the exact compact image gives the same supported Gysin map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

def regularNormalSourceImageStageIso (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P))
      (K : Set (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ (2+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) S q)
      (NormalSupportRelative.Constructions.normalPairImageComplement_source P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))).symm ≪≫
    LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood
      (NormalSupportRelative.Constructions.normalPairImageComplementOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) S (2+q))
      (NormalSupportRelative.Constructions.normalPairImage_union_complement P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))

theorem regularNormalSourceImageStageIso_eq_retraction (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso Z a ha x P K q).hom =
      (regularNormalSourceImageStageIso Z a ha x P K q).hom := by
  let hf := Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  let h := NormalSupportRelative.Constructions.normalPairRetractionComplement_le_image P hf K
  exact LocalSupportNaturality.Constructions.relativeNormalizedSupportIso_eq
    (TopCat.of (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (TopCat.of P.neighborhood) q (2+q)
    (fun _ hx => h hx) (Set.union_subset_union_right P.relativeComplement h)
    (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood (NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P hf K) q)
    (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood (NormalSupportRelative.Constructions.normalPairImageComplementOpen P hf K) q)
    (NormalSupportRelative.Constructions.normalPairRetractionComplement_source P hf K) (NormalSupportRelative.Constructions.normalPairImageComplement_source P hf K)
    (NormalSupportRelative.Constructions.normalPairRetraction_union_complement P hf K) (NormalSupportRelative.Constructions.normalPairImage_union_complement P hf K)
    (LocalSupportNaturality.Constructions.regularSourceThomLocalSupportIso_support_naturality Z a ha P.openNeighborhood h q)

theorem regularNormalSourceImageStageIso_eq_native
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))
    (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (regularNormalSourceImageStageIso Z a ha x P K q).hom =
      ModuleCat.ofHom (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K q).toLinearMap :=
  (regularNormalSourceImageStageIso_eq_retraction Z a ha x P K q).symm.trans
    (RegularNormalThomComparison.Constructions.regularNormalSourceThomStageIso_eq_native Z a ha x P hP K q)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalImageStage.Constructions
