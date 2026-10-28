import OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth
import OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization

/-! # Chart Reconstruction -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartReconstruction.Constructions

noncomputable section

/-! Bounded reconstruction of actual localized L² coefficients agrees
with the two genuine manifold cutoff multipliers, by smooth density. -/

open _root_.MeasureTheory
open scoped SchwartzMap _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
  (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)

theorem projectiveChartTestL2_localization (u : Form.Constructions.ProjectiveL2Forms V n) :
    ChartTestAbsorption.Constructions.projectiveChartTestL2 V e he n g hgc hgs (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he n χ hχ hχs u) =
      Multiplier.Constructions.projectiveL2Multiplier V n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hgc hgs)
        (Multiplier.Constructions.projectiveL2Multiplier V n (fun x => (χ x : ℂ)) (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V χ hχ) u) := by
  have hclosed : IsClosed {v : Form.Constructions.ProjectiveL2Forms V n |
      ChartTestAbsorption.Constructions.projectiveChartTestL2 V e he n g hgc hgs (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he n χ hχ hχs v) =
        Multiplier.Constructions.projectiveL2Multiplier V n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)
          (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hgc hgs)
          (Multiplier.Constructions.projectiveL2Multiplier V n (fun x => (χ x : ℂ)) (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V χ hχ) v)} :=
    isClosed_eq
      ((ChartTestAbsorption.Constructions.projectiveChartTestL2 V e he n g hgc hgs).continuous.comp
        (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he n χ hχ hχs).continuous)
      ((Multiplier.Constructions.projectiveL2Multiplier V n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hgc hgs)).continuous.comp
        (Multiplier.Constructions.projectiveL2Multiplier V n (fun x => (χ x : ℂ)) (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V χ hχ)).continuous)
  refine (Form.Constructions.smoothToProjectiveL2_dense V n).induction_on u hclosed (fun a => ?_)
  change ChartTestAbsorption.Constructions.projectiveChartTestL2 V e he n g hgc hgs
    (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he n χ hχ hχs (Form.Constructions.smoothToProjectiveL2 V n a)) = _
  rw [VectorEnergyLocalization.Constructions.projectiveVectorL2Localization_on_smooth, ChartTestAbsorption.Constructions.projectiveChartTestL2_on_schwartz,
    Multiplier.Constructions.projectiveL2Multiplier_on_smooth, Multiplier.Constructions.projectiveL2Multiplier_on_smooth,
    ChartReconstructionSmooth.Constructions.projectiveSchwartzTestLocalized_localization]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartReconstruction.Constructions
