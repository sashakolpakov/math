import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient

/-! # Smooth Estimate -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction

noncomputable section

/-! A first-order estimate for actual smooth functions in native Bessel
Sobolev coordinates, using their ordinary directional derivatives. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap

theorem finiteHilbertProduct_norm_le_sum {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] (u : PiLp 2 F) :
    ‖u‖ ≤ ∑ i, ‖u i‖ := by
  classical
  have hu : u = ∑ i, PiLp.single 2 i (u i) := by
    apply PiLp.ext
    intro j
    simp
  calc
    ‖u‖ = ‖∑ i, PiLp.single 2 i (u i)‖ := congrArg norm hu
    _ ≤ ∑ i, ‖PiLp.single 2 i (u i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖u i‖ := by simp only [PiLp.norm_single]

theorem schwartzSobolevCoordinate_one_bound {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, ℂ)) :
    ‖SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f‖ ≤ ‖f.toLp 2 (volume : Measure E)‖ +
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * ∑ i, ‖(∂_{b i} f).toLp 2 (volume : Measure E)‖ := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcomp (i : ι) : FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f) i =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∂_{b i} f).toLp 2 (volume : Measure E) := by
    rw [← SobolevDifferential.CM.Construction.sobolevL2Derivative_schwartz, FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative, inv_smul_smul₀ hκ]
  calc
    _ ≤ ‖SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)‖ +
        ‖EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)‖ := EuclideanGradient.CM.Construction.sobolevVectorGradient_graph_bound b _
    _ = ‖f.toLp 2 (volume : Measure E)‖ + ‖FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)‖ := by
      rw [SobolevIs.CM.Construction.sobolevL2Embedding_schwartz, EuclideanGradient.CM.Construction.sobolevVectorGradient_norm]
    _ ≤ ‖f.toLp 2 (volume : Measure E)‖ + ∑ i, ‖FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f) i‖ :=
      add_le_add le_rfl (finiteHilbertProduct_norm_le_sum _)
    _ = _ := by simp only [hcomp, norm_smul, Finset.mul_sum]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction
