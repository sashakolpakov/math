import OAI.Analysis.HodgeTheory.Decomposition.VectorGradient

/-! # Vector Gradient Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.VectorGradientNormalization

noncomputable section

/-! The exact physical-derivative normalization of the actual vector Sobolev gradient, using its coordinate and finite L² synthesis constructions. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap
open OAI.Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorGradient_physical_schwartz (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    ∀ᵐ x ∂(volume : Measure E),
      (2 * Real.pi * Complex.I : ℂ) • Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := F) b (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x =
        WithLp.toLp 2 (fun i => fderiv ℝ f x (b i)) := by
  let u := Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i : ι,
      (2 * Real.pi * Complex.I : ℂ) • Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i x =
        fderiv ℝ f x (b i) := by
    apply ae_all_iff.mpr
    intro i
    have hD := Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSobolevL2Derivative_schwartz (b i) f
    have hκ := Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative b u i
    rw [hD] at hκ
    filter_upwards [Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ) (Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i),
      (∂_{b i} f : 𝓢(E, F)).coeFn_toLp 2 volume] with x hx hfx
    rw [← hκ] at hx
    exact (hx.symm.trans hfx).trans (SchwartzMap.lineDerivOp_apply_eq_fderiv (b i) f x)
  filter_upwards [Analysis.HodgeTheory.Decomposition.FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) (Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u), hc] with x hx hc
  change (2 * Real.pi * Complex.I : ℂ) • Analysis.HodgeTheory.Decomposition.FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) (Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) x = _
  rw [hx]
  exact PiLp.ext hc

theorem vectorGradient_physical_of_coordinate_eq (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F))
    (q : Lp F 2 (volume : Measure E)) (hq : q = Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) :
    ∀ᵐ x ∂(volume : Measure E),
      (2 * Real.pi * Complex.I : ℂ) • Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := F) b q x =
        WithLp.toLp 2 (fun i => fderiv ℝ f x (b i)) := by
  rw [hq]
  exact vectorGradient_physical_schwartz b f

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.VectorGradientNormalization
