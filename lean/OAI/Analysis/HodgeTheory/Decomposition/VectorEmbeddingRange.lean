import OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate

/-! # Vector Embedding Range -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions

noncomputable section

section

/-! Actual vector-valued Schwartz functions in native Bessel Sobolev
coordinates, with their genuine first-derivative norm bound. -/

open _root_.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorSchwartzSobolevCoordinate (s : ℝ) : 𝓢(E, F) →ₗ[ℂ] Lp F 2 (volume : Measure E) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F s).symm.toLinearMap.comp
    ((SchwartzMap.toTemperedDistributionCLM E F (volume : Measure E)).toLinearMap.codRestrict
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevDistributionSubmodule E F s) (fun f => f.memSobolev))

theorem vectorSobolevL2Embedding_schwartz {s : ℝ} (hs : 0 ≤ s) (f : 𝓢(E, F)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs (vectorSchwartzSobolevCoordinate s f) = f.toLp 2 volume := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs (vectorSchwartzSobolevCoordinate s f)) : 𝓢'(E, F)) =
    ((f.toLp 2 volume) : 𝓢'(E, F))
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, Lp.toTemperedDistribution_toLp_eq]
  change besselPotential E F (-s)
    (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F s).symm ⟨(f : 𝓢'(E, F)), f.memSobolev⟩) : 𝓢'(E, F)) = _
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution, besselPotential_besselPotential_apply,
    add_neg_cancel, besselPotential_zero, ContinuousLinearMap.id_apply]

theorem vectorSobolevL2Derivative_schwartz (m : E) (f : 𝓢(E, F)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m (vectorSchwartzSobolevCoordinate 1 f) = (∂_{m} f).toLp 2 volume := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m (vectorSchwartzSobolevCoordinate 1 f)) : 𝓢'(E, F)) =
    (((∂_{m} f).toLp 2 volume) : 𝓢'(E, F))
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, vectorSobolevL2Embedding_schwartz,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact lineDerivOp_toTemperedDistributionCLM_eq f m

theorem vectorSobolev_graph_norm_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u : Lp F 2 (volume : Measure E)) :
    ‖u‖ ≤ ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ + ‖VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u‖ := by
  have h := congrArg Complex.re (VectorSobolevEnergy.Constructions.vectorSobolev_graph_inner b u u)
  have hn : ‖u‖ ^ 2 = ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ ^ 2 +
      ‖VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u‖ ^ 2 := by
    change RCLike.re (inner ℂ u u) =
      RCLike.re (inner ℂ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
      inner ℂ (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u)) at h
    simpa only [map_add, inner_self_eq_norm_sq] using h
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  nlinarith only [hn, mul_nonneg (norm_nonneg (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))
    (norm_nonneg (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u))]

theorem vectorSchwartzSobolevCoordinate_one_bound {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    ‖vectorSchwartzSobolevCoordinate 1 f‖ ≤ ‖f.toLp 2 volume‖ +
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * ∑ i, ‖(∂_{b i} f).toLp 2 volume‖ := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcomp (i : ι) : VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (vectorSchwartzSobolevCoordinate 1 f) i =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∂_{b i} f).toLp 2 volume := by
    rw [← vectorSobolevL2Derivative_schwartz, VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative, inv_smul_smul₀ hκ]
  calc
    _ ≤ ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (vectorSchwartzSobolevCoordinate 1 f)‖ +
        ‖VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (vectorSchwartzSobolevCoordinate 1 f)‖ := vectorSobolev_graph_norm_le b _
    _ ≤ ‖f.toLp 2 volume‖ + ∑ i, ‖VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (vectorSchwartzSobolevCoordinate 1 f) i‖ := by
      rw [vectorSobolevL2Embedding_schwartz]
      exact add_le_add le_rfl (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction.finiteHilbertProduct_norm_le_sum _)
    _ = _ := by simp only [hcomp, norm_smul, Finset.mul_sum]

end

/-! Genuine vector L² representatives belong to a Sobolev space exactly
when they lie in the range of its bounded Bessel-coordinate embedding. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorMemSobolev_l2_iff_embedding_range {s : ℝ} (hs : 0 ≤ s)
    (u : Lp F 2 (volume : Measure E)) :
    MemSobolev s 2 (u : 𝓢'(E, F)) ↔
      ∃ v : Lp F 2 (volume : Measure E), AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs v = u := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateMap_surjective E F s ⟨u, hu⟩
    refine ⟨v, ?_⟩
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := 2)))
    change (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs v : 𝓢'(E, F)) = (u : 𝓢'(E, F))
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution]
    exact congrArg Subtype.val hv
  · rintro ⟨v, rfl⟩
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨v, rfl⟩

theorem vectorSobolevL2Embedding_memSobolev {s : ℝ} (hs : 0 ≤ s)
    (u : Lp F 2 (volume : Measure E)) :
    MemSobolev s 2 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u : 𝓢'(E, F)) :=
  (vectorMemSobolev_l2_iff_embedding_range hs _).mpr ⟨u, rfl⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions
