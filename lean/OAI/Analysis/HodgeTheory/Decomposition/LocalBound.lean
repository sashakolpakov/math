import OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization
import OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding
import OAI.Analysis.HodgeTheory.Decomposition.GraphMultiplier
import OAI.Analysis.HodgeTheory.Decomposition.RellichEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion
import OAI.Analysis.HodgeTheory.Decomposition.LocalRellich

/-! # Local Bound -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalBound.Constructions

noncomputable section

/-! Actual scalar H¹ localization is uniformly bounded by the genuine
Hodge graph norm on sufficiently small chart supports. -/

open _root_.MeasureTheory LineDeriv _root_.Metric
open scoped _root_.Manifold ContDiff SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem projectiveScalarH1Localization_local_bound
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
        (hs : tsupport f ⊆ e.source),
        MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f ⊆ closedBall z r →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
            (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)),
            ‖SchwartzLocalization.Constructions.projectiveScalarH1Localization V e he (n + 1) f hf hs j a‖ ≤ B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖ := by
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
  refine ⟨B * q, mul_nonneg hB hq, fun j a => ?_⟩
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
  have h := RellichEnergy.Constructions.schwartz_coordinate_sobolev_of_energy
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (EuclideanSpace.basisFun _ ℂ) j u
    (B * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖) (mul_nonneg hB (norm_nonneg _)) henergy
  rw [SchwartzLocalization.Constructions.projectiveScalarH1Localization_norm, SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_norm]
  exact h.trans_eq (by dsimp only [q]; ring)

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalBound.Constructions
