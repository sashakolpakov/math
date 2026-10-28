import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEnergyCutoff
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientEnergyNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization

/-! # Global Energy Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalEnergyLocalization.CM.Construction

noncomputable section

/-! The actual global weak energy localizes to the normalized Euclidean
Sobolev energy, by smooth density in the completed derivative graph. -/

open Set _root_.MeasureTheory Filter
open scoped SchwartzMap _root_.Topology

variable {ι : Type*} [Fintype ι]

theorem varietySmoothEnergy_Lp (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {B : ℝ} (hB : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, ‖GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x‖ ≤ B)
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    CoerciveKernelSolver.CM.Construction.boundedFieldEnergy (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b)
      (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_measurable V C b) hB
      (GlobalLp.CM.Construction.varietyOneFormL2 V C b form) (GlobalLp.CM.Construction.varietyOneFormL2 V C b other) =
    ∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b other x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  rw [CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply]
  apply integral_congr_ae
  filter_upwards [GlobalLp.CM.Construction.varietyOneFormL2_coe V C b form, GlobalLp.CM.Construction.varietyOneFormL2_coe V C b other] with x hf hg
  rw [hf, hg]

theorem varietyGlobalEnergy_localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g η : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hgU : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηc : HasCompactSupport (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hη : ∀ z ∈ tsupport g, (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1)
    (A : EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ∀ z ∈ tsupport g, A z = MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z)
    (hAm : AEStronglyMeasurable A volume) {B : ℝ} (hAB : ∀ᵐ z ∂volume, ‖A z‖ ≤ B)
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) :
    (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u x))
      (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgU)) x)
      ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
    ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 *
      ∫ z, inner ℝ (A z (EuclideanGradient.CM.Construction.sobolevVectorGradient b
        (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val z))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) z) := by
  obtain ⟨B₀, _, hB₀⟩ := GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_bounded V C b
  let hAB₀ : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, ‖GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x‖ ≤ B₀ :=
    Eventually.of_forall hB₀
  let Dg := GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hgU))
  let L : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] ℝ :=
    ((CoerciveKernelSolver.CM.Construction.boundedFieldEnergy (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b)
      (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_measurable V C b) hAB₀).flip Dg).comp
        ((GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).restrictScalars ℝ)
  let S : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    (SobolevIs.CM.Construction.supportedH1Coordinates (tsupport η)).subtypeL.comp (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU)
  let R : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] ℝ := ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 •
    (((CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB).flip (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g))).comp
      (((EuclideanGradient.CM.Construction.sobolevVectorGradient b).comp S).restrictScalars ℝ))
  have hLR : (L : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b → ℝ) = R :=
    (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev_dense V C b).equalizer L.continuous R.continuous (by
      funext f
      change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b)
        (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_measurable V C b) hAB₀
        (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f)) Dg =
        ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 * CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB
          (EuclideanGradient.CM.Construction.sobolevVectorGradient b (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU
            (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f)).val)
          (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g))
      rw [GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth, GlobalLocalization.CM.Construction.varietySobolevChartLocalization_smooth]
      change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy _ _ _ (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)) Dg =
        ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 * CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB
          (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he η hηc hηU f)))
          (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g))
      rw [varietySmoothEnergy_Lp, CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply]
      exact (SmoothEnergyCutoff.CM.Construction.varietySmoothEnergy_cutoff_gradient V C b e he f g η hgc hgU hηc hηU hη A hA).trans
        (GradientEnergyNormalization.CM.Construction.schwartzGradient_energy_normalization b _ g A (fun z hz v w => by
          rw [hA z hz]
          exact GradientEnergyNormalization.CM.Construction.varietyComplexDirichletOperator_smul_both V e b z _ v w)))
  have h := congrFun hLR u
  change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy _ _ _ (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u) Dg =
    ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 * CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he η hηc hηU u).val)
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g)) at h
  rwa [CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply, CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply] at h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalEnergyLocalization.CM.Construction
