import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Regular Normal Thom Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions

noncomputable section

/-! The global source–Thom comparison evaluated at an exact compact support inside a normal chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

abbrev regularNormalSourceOpen := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding

def regularNormalSourceThomStageIso (K : Compacts (regularNormalSourceOpen Z x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (regularNormalSourceOpen Z x P))
      (K : Set (regularNormalSourceOpen Z x P))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ (2+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (regularNormalSourceOpen Z x P)) S q)
      (NormalSupportRelative.Constructions.normalPairRetractionComplement_source P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))).symm ≪≫
    LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood
      (NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) S (2+q))
      (NormalSupportRelative.Constructions.normalPairRetraction_union_complement P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions
