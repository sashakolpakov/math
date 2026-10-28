import OAI.AlgebraicGeometry.CycleClass.Thom.Local.SupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Normal Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.NormalStage.Constructions.HigherThom

noncomputable section

/-! The global source–Thom comparison evaluated at an exact compact support inside a normal chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

abbrev regularNormalSourceOpen := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding

def regularNormalSourceThomStageIso (K : Compacts (regularNormalSourceOpen Z x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (regularNormalSourceOpen Z x P))
      (K : Set (regularNormalSourceOpen Z x P))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (regularNormalSourceOpen Z x P)) S q)
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement_source P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))).symm ≪≫
    Local.SupportCup.Constructions.HigherThom.regularSourceThomLocalSupportIso Z a ha P.openNeighborhood
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) S ((2 * p)+q))
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.NormalStage.Constructions.HigherThom
