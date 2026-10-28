import OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergy
import OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding
import OAI.Analysis.HodgeTheory.Decomposition.GraphMultiplier
import OAI.Analysis.HodgeTheory.Decomposition.RellichEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion
import OAI.Analysis.HodgeTheory.Decomposition.LocalRellich

/-! # Vector Energy Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization.Constructions

noncomputable section

section

/-! Actual vector H¹ localization is uniformly bounded by the genuine
Hodge graph norm on sufficiently small chart supports. -/

open _root_.MeasureTheory LineDeriv _root_.Metric
open scoped _root_.Manifold ContDiff SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

def projectiveVectorH1Localization
    (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (hs : tsupport f ⊆ e.source) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1).comp (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n f hf hs)

theorem projectiveVectorH1Localization_local_bound
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
        (hs : tsupport f ⊆ e.source),
        MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f ⊆ closedBall z r →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)),
            ‖projectiveVectorH1Localization V e he (n + 1) f hf hs a‖ ≤ B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖ := by
  obtain ⟨r, hr, hchart, hlocal⟩ := ManifoldGarding.Constructions.projectiveManifold_local_garding V e he n z hz
  refine ⟨r, hr, hchart, fun f hf hs hball => ?_⟩
  have hK : IsCompact (tsupport f) := (isClosed_tsupport f).isCompact
  obtain ⟨C, hC, hgrad⟩ := hlocal (tsupport f) hK hs hball
  obtain ⟨B₀, hB₀, hnorm⟩ := ManifoldGarding.Constructions.supportedEuclideanCoefficients_integral_bound V e he (n + 1) hK hs
  obtain ⟨M, hM, hmul⟩ := GraphMultiplier.Constructions.projectiveRealMultiplier_graph_bound V e he n f hf hs
  let B := Real.sqrt (B₀ + C) * M
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hM
  let q := 1 + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Fintype.card (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨B * q, mul_nonneg hB hq, fun a => ?_⟩
  let b := RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a
  have hb : ∀ x, x ∉ tsupport f → b x = 0 :=
    fun _ hx => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V (n + 1) f hf a hx
  let u := SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he (n + 1) f hf hs a
  have henergy : ‖u.toLp 2 volume‖ ^ 2 +
      (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
        ‖(∂_{stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i} u).toLp 2 volume‖ ^ 2) ≤
      (B * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖) ^ 2 := by
    have hn := (hnorm b hb).trans (mul_le_mul_of_nonneg_left
      (EnergyDomain.Constructions.projectiveGraphEmbedding_value_norm_sq_le V n b) hB₀.le)
    have hd := hgrad b hb
    rw [← EnergyDomain.Constructions.projectiveGraphEmbedding_norm_sq] at hd
    have hg : ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n b‖ ^ 2 ≤ (M * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr (hmul a)
    have htotal := (add_le_add hn hd).trans
      ((add_mul B₀ C (‖EnergyDomain.Constructions.projectiveGraphEmbedding V n b‖ ^ 2)).symm.le.trans
        (mul_le_mul_of_nonneg_left hg (add_pos hB₀ hC).le))
    simp_rw [LocalRellich.Constructions.schwartz_toLp_norm_sq, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (∫ x, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) b.val x‖ ^ 2) +
      (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V, ∫ x,
        ‖fderiv ℝ (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) b.val) x
          (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)‖ ^ 2) ≤ _
    convert htotal using 1; first | rfl | (simp only [B, mul_pow, Real.sq_sqrt (add_pos hB₀ hC).le]; ring)
  have h := VectorEnergy.Constructions.vectorSchwartzSobolev_of_energy
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u
    (B * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖) (mul_nonneg hB (norm_nonneg _)) henergy
  change ‖VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 u‖ ≤ _
  rw [SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_norm]
  exact h.trans_eq (by dsimp only [q]; ring)

end

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

def projectiveVectorL2Localization : Form.Constructions.ProjectiveL2Forms V n →L[ℂ]
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  ChartLocalization.Constructions.projectiveChartLocalization V e he n (fun x => (f x : ℂ))
    (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V f hf) (by
      rw [RealMultiplier.Constructions.projectiveRealFunction_complex_tsupport V f]
      exact hs)

theorem projectiveVectorL2Localization_on_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveVectorL2Localization V e he n f hf hs (Form.Constructions.smoothToProjectiveL2 V n a) =
      (SchwartzLocalization.Constructions.projectiveRealLocalizationSchwartz V e he n f hf hs a).toLp 2 volume := by
  rw [projectiveVectorL2Localization,
    ChartLocalization.Constructions.projectiveChartLocalization_on_smooth V e he n (fun x => (f x : ℂ))
      (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V f hf) (by
        rw [RealMultiplier.Constructions.projectiveRealFunction_complex_tsupport V f]
        exact hs) a]
  rfl

def projectiveVectorEnergyH1Localization
    :
    EnergyDomain.Constructions.ProjectiveEnergyDomain V n →L[ℂ] Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (projectiveVectorH1Localization V e he (n + 1) f hf hs).extendOfNorm (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n)

theorem projectiveVectorEnergyH1Localization_on_smooth
    (hbound : ∃ B : ℝ, ∀ a, ‖projectiveVectorH1Localization V e he (n + 1) f hf hs a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    projectiveVectorEnergyH1Localization V e he n f hf hs (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a) =
      projectiveVectorH1Localization V e he (n + 1) f hf hs a :=
  LinearMap.extendOfNorm_eq (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n) hbound a

theorem projectiveVectorEnergyH1Localization_L2
    (hbound : ∃ B : ℝ, ∀ a, ‖projectiveVectorH1Localization V e he (n + 1) f hf hs a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (projectiveVectorEnergyH1Localization V e he n f hf hs u) =
      projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) := by
  have hclosed : IsClosed {v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n |
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (projectiveVectorEnergyH1Localization V e he n f hf hs v) =
        projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n v)} :=
    isClosed_eq
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)).continuous.comp
        (projectiveVectorEnergyH1Localization V e he n f hf hs).continuous)
      ((projectiveVectorL2Localization V e he (n + 1) f hf hs).continuous.comp
        (EnergyDomain.Constructions.projectiveEnergyInclusion V n).continuous)
  refine (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n).induction_on u hclosed (fun a => ?_)
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (projectiveVectorEnergyH1Localization V e he n f hf hs (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a)) = _
  rw [projectiveVectorEnergyH1Localization_on_smooth V e he n f hf hs hbound,
    SmoothEnergyInclusion.Constructions.projectiveEnergyInclusion_on_smooth, projectiveVectorL2Localization_on_smooth]
  exact VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1) _

theorem projectiveVectorEnergyH1Localization_memSobolev
    (hbound : ∃ B : ℝ, ∀ a, ‖projectiveVectorH1Localization V e he (n + 1) f hf hs a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    MemSobolev 1 2
      ((projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) :
        Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  rw [← projectiveVectorEnergyH1Localization_L2 V e he n f hf hs hbound u,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨projectiveVectorEnergyH1Localization V e he n f hf hs u, rfl⟩

omit f hf hs in
theorem projectiveEnergy_local_vector_h1
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
        (hs : tsupport f ⊆ e.source),
        MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f ⊆ Metric.closedBall z r →
        ∀ (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n),
          MemSobolev 1 2
            ((projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) :
              Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  obtain ⟨r, hr, hchart, hbound⟩ := projectiveVectorH1Localization_local_bound V e he n z hz
  refine ⟨r, hr, hchart, fun f hf hs hsupport u => ?_⟩
  obtain ⟨B, _, hB⟩ := hbound f hf hs hsupport
  exact projectiveVectorEnergyH1Localization_memSobolev V e he n f hf hs ⟨B, hB⟩ u

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization.Constructions
