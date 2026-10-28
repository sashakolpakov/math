import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.FixedNormalCover
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RegularNormalComparison

/-! # Fixed Normal Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.FixedNormalComparison

noncomputable section

/-! Every compact stage of the actual supported Thom comparison has the original coefficient-one trace in a fixed algebraic normal chart. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = D.regularThomClass)
variable (x : D.regularAnalyticSpace)

theorem regularFixedNormalThomStage_compact (K : Compacts (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)) (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x))
      (K : Set (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x))ᶜ q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (D.regularFixedNormalPair x).neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap (D.regularFixedNormalPair x)
        D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) ((2 * p)+q)
      ((RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso D a ha x (D.regularFixedNormalPair x) K q).hom b) =
    HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin (D.regularFixedNormalPair x)
      D.isClosedEmbedding_regularComplementInclusion.isEmbedding q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.Constructions.Construction.regularFixedSourceOpen D x)) K q b) := by
  have hc := ConcreteCategory.congr_hom (RegularNormalComparison.Constructions.Construction.regularNormalSourceThomStageIso_eq_native D a ha x
    (D.regularFixedNormalPair x) (D.regularFixedNormalPair_ambientChart_mdifferentiable x) K q) b
  have hg := HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin_stage_supported (D.regularFixedNormalPair x)
    D.isClosedEmbedding_regularComplementInclusion.isEmbedding K q b
  exact (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
    (TopCat.of (D.regularFixedNormalPair x).neighborhood)
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap (D.regularFixedNormalPair x)
      D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) ((2 * p)+q)) hc).trans hg.symm

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.FixedNormalComparison
