import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalStageComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactOpenStage

/-! # Normal Open Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalOpenStage

noncomputable section

/-! Exact extension of a normal-chart compact Thom stage to the global
compact pushforward. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin p → ℂ) D.regularComplementInclusion x)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = D.regularThomClass)

theorem regularNormalSourceThomStageIso_eq_local (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) (q : ℕ) :
    RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso D a ha x P K q =
      CompactStageRestriction.Constructions.Construction.regularSourceLocalCompactThomStageIso D P.openNeighborhood a ha K q := by
  rw [NormalStageComparison.Constructions.Construction.regularNormalSourceThomStageIso_eq_global]
  rfl

theorem regularSourceCompactThomPushforward_normal_stage
    (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) K q ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace) (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P) q ≫
      SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward D a ha q =
    (RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso D a ha x P K q).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
          D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) (2 * p + q) ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood (2 * p + q) := by
  rw [regularNormalSourceThomStageIso_eq_local]
  exact CompactOpenStage.Constructions.Construction.regularSourceCompactThomPushforward_open_stage D a ha P.openNeighborhood K q

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalOpenStage
