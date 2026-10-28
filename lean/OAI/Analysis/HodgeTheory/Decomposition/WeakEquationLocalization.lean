import OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalizationPair
import OAI.Analysis.HodgeTheory.Decomposition.SmoothChartForcing
import OAI.Analysis.HodgeTheory.Decomposition.WeakEquation

/-! # Weak Equation Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakEquationLocalization.Constructions

noncomputable section

/-! Every actual completed manifold weak Hodge solution satisfies its
derived local vector energy equation on compact chart tests. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)
  (hbound : ∃ B : ℝ, ∀ a, ‖VectorEnergyLocalization.Constructions.projectiveVectorH1Localization V e he (n + 1) χ hχ hχs a‖ ≤
    B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)
  (τ : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hτc : HasCompactSupport τ)
  (hτs : tsupport τ ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

include hbound in
theorem projectiveWeakHodgeSolution_local_test
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u f)
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {U : Set V.analyticSpace} (hU : IsOpen U)
    (hKU : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g) ⊆ U) (hχU : ∀ x ∈ U, χ x = 1)
    (hηg : ∀ x ∈ tsupport g, η x = 1)
    (hAg : ∀ x ∈ tsupport g, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x)
    (hτg : ∀ x ∈ tsupport g, τ x = 1) :
    LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB
      (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs u) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g) =
      inner ℝ (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he (n + 1) τ hτc hτs f) (g.toLp 2 volume) := by
  have hE := EnergyLocalizationPair.Constructions.projectiveEnergy_local_hodge_pair V e he n χ hχ hχs hbound η hη hηc hηU A hAm hAB
    g hg hgs hU hKU hχU hηg hAg u
  have hS := hsol (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs))
  rw [SmoothEnergyInclusion.Constructions.projectiveEnergyInclusion_on_smooth] at hS
  exact hE.symm.trans ((congrArg Complex.re hS).trans
    (SmoothChartForcing.Constructions.projectiveChartForcingL2_test_pair V e he (n + 1) τ hτc hτs f g hg hgs hτg).symm)

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakEquationLocalization.Constructions
