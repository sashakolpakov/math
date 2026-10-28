import OAI.Analysis.HodgeTheory.Decomposition.BoundedChartEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyLocalization
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization

/-! # Energy Localization Pair -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalizationPair.Constructions

noncomputable section

/-! The actual completed Hodge energy has the derived local vector
coefficient formula, proved by smooth density and bounded localization. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveEnergyDerivative_smooth_pair (n : ℕ)
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a))
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n b)) =
      Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) +
        Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) (AdjointAlgebra.Constructions.projectiveCodifferential V n b) := by
  change inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))
      (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)) +
    inner ℂ (Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a))
      (Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n b)) = _
  rw [Form.Constructions.smoothToProjectiveL2_inner, Form.Constructions.smoothToProjectiveL2_inner]

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)
  (hbound : ∃ B : ℝ, ∀ a, ‖VectorEnergyLocalization.Constructions.projectiveVectorH1Localization V e he (n + 1) χ hχ hχs a‖ ≤
    B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)

include hbound in
theorem projectiveEnergy_local_hodge_pair
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {U : Set V.analyticSpace} (hU : IsOpen U)
    (hKU : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g) ⊆ U) (hχU : ∀ x ∈ U, χ x = 1)
    (hηg : ∀ x ∈ tsupport g, η x = 1)
    (hAg : ∀ x ∈ tsupport g, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    (inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n u)
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n
        (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs)))).re =
      LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB
        (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs u) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g) := by
  have hclosed : IsClosed {v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n |
      (inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n v)
        (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n
          (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs)))).re =
        LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB
          (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs v) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)} :=
    isClosed_eq
      (Complex.continuous_re.comp ((EnergyDomain.Constructions.projectiveEnergyDerivative V n).continuous.inner continuous_const))
      ((LocalEnergy.Constructions.projectiveLocalHodgeEnergy_continuous_left V e n he η hη hηc hηU A hAm hAB _).comp
        (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs).continuous)
  refine (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n).induction_on u hclosed (fun a => ?_)
  change (inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a))
    (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n
      (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs)))).re = _
  rw [projectiveEnergyDerivative_smooth_pair,
    VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization_on_smooth V e he n χ hχ hχs hbound]
  exact (SmoothEnergyLocalization.Constructions.projectiveSmoothEnergy_cutoff_coefficients V e he n χ hχ hχs a g hg hgs hU hKU hχU).trans
    (BoundedChartEnergy.Constructions.projectiveLocalHodgeEnergy_schwartz V e n he η hη hηc hηU A hAm hAB
      (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he (n + 1) χ hχ hχs a) g
      (SmoothEnergyLocalization.Constructions.projectiveRealLocalizationSchwartz_compact V e he (n + 1) χ hχ hχs a)
      (SmoothEnergyLocalization.Constructions.projectiveRealLocalizationSchwartz_tsupport V e he (n + 1) χ hχ hχs a) hηg hAg).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalizationPair.Constructions
