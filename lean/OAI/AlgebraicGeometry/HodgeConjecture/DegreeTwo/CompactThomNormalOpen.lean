import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomOpenStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactNormalStageComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin

/-! # Compact Thom Normal Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomNormalOpen.Constructions

noncomputable section

/-! On a smooth normal source neighborhood, the global compact Thom pushforward is the independent local Gysin map followed by ambient open extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

theorem regularSourceCompactThomPushforward_normal_open
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace) (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P) q ≫
      CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha q =
    ModuleCat.ofHom (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q) ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood (2+q) := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) q
  intro K
  have hs := CompactThomOpenStage.Constructions.regularSourceCompactThomPushforward_open_stage Z a ha P.openNeighborhood K q
  rw [CompactNormalStageComparison.Constructions.regularSourceLocalCompactThomStageIso_normalPair_eq_native Z a ha x P hP K q] at hs
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have he := ConcreteCategory.congr_hom hs b
  have hg := SourceCompactGysin.Constructions.normalPairSourceCompactGysin_stage_supported P
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K q b
  exact he.trans (congrArg
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood (2+q)) hg.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomNormalOpen.Constructions
