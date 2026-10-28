import OAI.AlgebraicGeometry.DivisorClass.Chern.TopCompactOpenCover
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SourceTrace

/-! # Fixed Normal Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalCover

noncomputable section

/-! The original algebraic normal charts form a smooth source cover that detects top compact cohomology maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.TopCompactOpenCover
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.HigherThom

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularFixedSourceOpen (x : D.regularAnalyticSpace) : Opens D.regularAnalyticSpace :=
  HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen (D.regularFixedNormalPair x) D.isClosedEmbedding_regularComplementInclusion.isEmbedding

theorem mem_regularFixedSourceOpen (x : D.regularAnalyticSpace) : x ∈ regularFixedSourceOpen D x :=
  (D.regularFixedNormalPair x).point_mem_neighborhood

theorem regularFixedNormalPair_contMDiffOn (x : D.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, D.regularAnalyticModel × (Fin p → ℂ)) ∞
      (D.regularFixedNormalPair x).ambientChart (D.regularFixedNormalPair x).ambientChart.source := by
  rw [D.regularFixedNormalPair_ambientChart]
  exact (ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates (D.regularFixedComplementImmersion x)).of_le (by simp)

theorem regularFixedNormalPair_symm_contMDiffOn (x : D.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, D.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ∞
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
  DivisorClass.Chern.TopCompactOpenCover.topCompactCohomology_openCover_hom_ext D.regularComplexDimension (regularFixedSourceOpen D)
    (fun x => ⟨x, mem_regularFixedSourceOpen D x⟩) h

end Constructions.HigherThom

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalCover
