import OAI.Analysis.HodgeTheory.Decomposition.LocalBound

/-! # Energy Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalization.Constructions

noncomputable section

/-! Bounded H¹ localization of the actual completed Hodge energy domain,
with its L² realization identified on genuine smooth forms and by density. -/

open _root_.MeasureTheory
open TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
  (hs : tsupport f ⊆ e.source)

def projectiveScalarL2Localization (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    Form.Constructions.ProjectiveL2Forms V n →L[ℂ] Lp ℂ 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  ((innerSL ℂ (EuclideanSpace.basisFun (Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) ℂ j)).compLpL 2 volume).comp
    (ChartLocalization.Constructions.projectiveChartLocalization V e he n (fun x => (f x : ℂ))
      (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V f hf) (by
        rw [RealMultiplier.Constructions.projectiveRealFunction_complex_tsupport V f]
        exact hs))

theorem projectiveScalarL2Localization_on_smooth
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveScalarL2Localization V e he n f hf hs j (Form.Constructions.smoothToProjectiveL2 V n a) =
      (SchwartzCoordinates.Constructions.schwartzOrthonormalCoordinate (EuclideanSpace.basisFun _ ℂ) j
        (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n f hf hs a)).toLp 2 volume := by
  rw [projectiveScalarL2Localization, ContinuousLinearMap.comp_apply,
    ChartLocalization.Constructions.projectiveChartLocalization_on_smooth V e he n (fun x => (f x : ℂ))
      (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V f hf) (by
        rw [RealMultiplier.Constructions.projectiveRealFunction_complex_tsupport V f]
        exact hs) a]
  change _ = (SchwartzMap.postcompCLM (innerSL ℂ (EuclideanSpace.basisFun _ ℂ j))
    (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n f hf hs a)).toLp 2 volume
  rw [SchwartzCoordinates.Constructions.schwartz_postcomp_toLp]
  rfl

def projectiveEnergyH1Localization
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    EnergyDomain.Constructions.ProjectiveEnergyDomain V n →L[ℂ] Lp ℂ 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j).extendOfNorm (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n)

theorem projectiveEnergyH1Localization_on_smooth
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (hbound : ∃ B : ℝ, ∀ a, ‖SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    projectiveEnergyH1Localization V e he n f hf hs j (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a) =
      SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j a :=
  LinearMap.extendOfNorm_eq (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n) hbound a

theorem projectiveEnergyH1Localization_L2
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (hbound : ∃ B : ℝ, ∀ a, ‖SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (projectiveEnergyH1Localization V e he n f hf hs j u) =
      projectiveScalarL2Localization V e he (n + 1) f hf hs j (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) := by
  have hclosed : IsClosed {v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n |
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (projectiveEnergyH1Localization V e he n f hf hs j v) =
        projectiveScalarL2Localization V e he (n + 1) f hf hs j (EnergyDomain.Constructions.projectiveEnergyInclusion V n v)} :=
    isClosed_eq
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)).continuous.comp
        (projectiveEnergyH1Localization V e he n f hf hs j).continuous)
      ((projectiveScalarL2Localization V e he (n + 1) f hf hs j).continuous.comp
        (EnergyDomain.Constructions.projectiveEnergyInclusion V n).continuous)
  refine (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n).induction_on u hclosed (fun a => ?_)
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (projectiveEnergyH1Localization V e he n f hf hs j (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a)) = _
  rw [projectiveEnergyH1Localization_on_smooth V e he n f hf hs j hbound,
    SmoothEnergyInclusion.Constructions.projectiveEnergyInclusion_on_smooth, projectiveScalarL2Localization_on_smooth]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1) _

theorem projectiveEnergyH1Localization_memSobolev
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (hbound : ∃ B : ℝ, ∀ a, ‖SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    MemSobolev 1 2
      ((projectiveScalarL2Localization V e he (n + 1) f hf hs j (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) :
        Lp ℂ 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) := by
  rw [← projectiveEnergyH1Localization_L2 V e he n f hf hs j hbound u,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨projectiveEnergyH1Localization V e he n f hf hs j u, rfl⟩

omit f hf hs in
theorem projectiveEnergy_local_h1
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
        (hs : tsupport f ⊆ e.source),
        MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f ⊆ Metric.closedBall z r →
        ∀ (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n),
          MemSobolev 1 2
            ((projectiveScalarL2Localization V e he (n + 1) f hf hs j (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) :
              Lp ℂ 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) := by
  obtain ⟨r, hr, hchart, hbound⟩ := LocalBound.Constructions.projectiveScalarH1Localization_local_bound V e he n z hz
  refine ⟨r, hr, hchart, fun f hf hs hsupport j u => ?_⟩
  obtain ⟨B, _, hB⟩ := hbound f hf hs hsupport
  exact projectiveEnergyH1Localization_memSobolev V e he n f hf hs j ⟨B, hB j⟩ u

end

end OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalization.Constructions
