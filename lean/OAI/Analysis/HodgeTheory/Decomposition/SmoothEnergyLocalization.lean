import OAI.Analysis.HodgeTheory.Decomposition.EnergyLocality
import OAI.Analysis.HodgeTheory.Decomposition.ChartEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful

/-! # Smooth Energy Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyLocalization.Constructions

noncomputable section

/-! A genuine smooth manifold form and a local chart test have precisely
the derived coefficient energy after an outer manifold cutoff. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)

theorem projectiveRealLocalizationSchwartz_compact
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    HasCompactSupport (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n χ hχ hχs a) :=
  SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a).val
    (isClosed_tsupport χ).isCompact hχs
    (fun _ hx => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n χ hχ a hx)

theorem projectiveRealLocalizationSchwartz_tsupport
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    tsupport (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n χ hχ hχs a) ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
  SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a).val
    (isClosed_tsupport χ).isCompact hχs
    (fun _ hx => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n χ hχ a hx)

theorem projectiveRealLocalizationSchwartz_lift
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    RealMultiplier.Constructions.projectiveRealMultiplier V n χ hχ a =
      ChartTestForms.Constructions.projectiveChartTestLift V e he n (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n χ hχ hχs a)
        (projectiveRealLocalizationSchwartz_compact V e he n χ hχ hχs a)
        (projectiveRealLocalizationSchwartz_tsupport V e he n χ hχ hχs a) := by
  apply ChartCoefficientFaithful.Constructions.projectiveChartTestLift_unique
  · intro x hx
    exact RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n χ hχ a (fun h => hx (hχs h))
  · exact fun _ => rfl

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveSmoothEnergy_cutoff_coefficients
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {U : Set V.analyticSpace} (hU : IsOpen U)
    (hKU : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g) ⊆ U) (hχU : ∀ x ∈ U, χ x = 1) :
    let f := SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he (n + 1) χ hχ hχs a
    let hf := projectiveRealLocalizationSchwartz_compact V e he (n + 1) χ hχ hχs a
    let hfs := projectiveRealLocalizationSchwartz_tsupport V e he (n + 1) χ hχ hχs a
    let b := ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs
    let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
    (Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) +
      Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) (AdjointAlgebra.Constructions.projectiveCodifferential V n b)).re =
    ∫ x, inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x) := by
  dsimp only
  have hcut := EnergyLocality.Constructions.projective_hodge_energy_real_cutoff V n a
    (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs) χ hχ
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hgs).isClosed hU hKU hχU
    (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he (n + 1) g hg hgs)
  rw [hcut, projectiveRealLocalizationSchwartz_lift V e he (n + 1) χ hχ hχs a]
  exact ChartEnergy.Constructions.projectiveChartTestLift_hodge_energy V e he n _ g _ _ hg hgs

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyLocalization.Constructions
