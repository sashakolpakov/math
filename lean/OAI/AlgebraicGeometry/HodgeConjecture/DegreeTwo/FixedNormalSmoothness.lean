import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactGysin
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFixedNormalPair

/-! # Fixed Normal Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FixedNormalSmoothness.Constructions

noncomputable section

/-! The fixed normal charts come from the actual analytic immersion and are smooth in both directions. -/

open scoped _root_.Manifold ContDiff

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : Z.regularAnalyticSpace)

theorem regularFixedNormalPair_contMDiffOn :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞
      (Z.regularFixedNormalPair x).ambientChart (Z.regularFixedNormalPair x).ambientChart.source :=
  (ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates (Z.regularFixedComplementImmersion x)).of_le (by simp)

theorem regularFixedNormalPair_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) 𝓘(ℂ, V.analyticModel) ∞
      (Z.regularFixedNormalPair x).ambientChart.symm (Z.regularFixedNormalPair x).ambientChart.target :=
  (ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates_symm (Z.regularFixedComplementImmersion x)).of_le (by simp)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FixedNormalSmoothness.Constructions
