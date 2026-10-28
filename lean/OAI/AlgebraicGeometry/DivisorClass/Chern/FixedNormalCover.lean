import OAI.AlgebraicGeometry.DivisorClass.Chern.TopCompactOpenCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedGlobalGysin

/-! # Fixed Normal Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FixedNormalCover

noncomputable section

/-! The original algebraic normal charts form a smooth source cover that detects top compact cohomology maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

def regularFixedSourceOpen (x : D.regularAnalyticSpace) : Opens D.regularAnalyticSpace :=
  HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (D.regularFixedNormalPair x) D.isClosedEmbedding_regularComplementInclusion.isEmbedding

theorem mem_regularFixedSourceOpen (x : D.regularAnalyticSpace) : x ∈ regularFixedSourceOpen D x :=
  (D.regularFixedNormalPair x).point_mem_neighborhood

theorem regularFixedNormalPair_contMDiffOn (x : D.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, D.regularAnalyticModel × (Fin 1 → ℂ)) ∞
      (D.regularFixedNormalPair x).ambientChart (D.regularFixedNormalPair x).ambientChart.source := by
  rw [D.regularFixedNormalPair_ambientChart]
  exact (ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates (D.regularFixedComplementImmersion x)).of_le (by simp)

theorem regularFixedNormalPair_symm_contMDiffOn (x : D.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, D.regularAnalyticModel × (Fin 1 → ℂ)) 𝓘(ℂ, V.analyticModel) ∞
      (D.regularFixedNormalPair x).ambientChart.symm (D.regularFixedNormalPair x).ambientChart.target := by
  rw [D.regularFixedNormalPair_ambientChart]
  exact (ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates_symm (D.regularFixedComplementImmersion x)).of_le (by simp)

theorem regularTopCompact_fixedNormal_hom_ext {N : ModuleCat.{0} ℚ}
    {f g : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (2 * D.regularComplexDimension) ⟶ N}
    (h : ∀ x : D.regularAnalyticSpace,
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace)
        (regularFixedSourceOpen D x) (2 * D.regularComplexDimension) ≫ f =
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace)
        (regularFixedSourceOpen D x) (2 * D.regularComplexDimension) ≫ g) : f = g :=
  TopCompactOpenCover.topCompactCohomology_openCover_hom_ext D.regularComplexDimension (regularFixedSourceOpen D)
    (fun x => ⟨x, mem_regularFixedSourceOpen D x⟩) h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FixedNormalCover
